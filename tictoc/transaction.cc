
#include <stdio.h>
#include <sys/time.h>

#include <algorithm>
#include <bitset>
#include <fstream>
#include <sstream>
#include <string>

#include "../include/debug.hpp"
#include "../include/inline.hpp"

#include "include/common.hpp"
#include "include/transaction.hpp"
#include "include/tuple.hpp"

extern bool chkSpan(struct timeval &start, struct timeval &stop, long threshold);
extern void displayDB();

using namespace std;

SetElement *
Transaction::searchWriteSet(unsigned int key)
{
  for (auto itr = writeSet.begin(); itr != writeSet.end(); ++itr) {
    if ((*itr).key == key) return &(*itr);
  }

  return nullptr;
}

SetElement *
Transaction::searchReadSet(unsigned int key)
{
  for (auto itr = readSet.begin(); itr != readSet.end(); ++itr) {
    if ((*itr).key == key) return &(*itr);
  }

  return nullptr;
}

void
Transaction::tbegin()
{
  this->status = TransactionStatus::inFlight;
  this->commit_ts = 0;
  this->appro_commit_ts = 0;
}

int
Transaction::tread(unsigned int key)
{
  SetElement *result;

  result = searchWriteSet(key);
  if (result) return result->val;

  result = searchReadSet(key);
  if (result) return result->val;

  TsWord v1, v2;
  unsigned int return_val;

  v1.obj = __atomic_load_n(&(Table[key].tsw.obj), __ATOMIC_ACQUIRE);
  for (;;) {
    if (v1.lock) {
      if ((v1.rts()) < this->appro_commit_ts) {
        // it must check whether this write set include the tuple,
        // but it already checked L31 - L33.
        // so it must abort.
        this->status = TransactionStatus::aborted;
        return 0;
      } else {
        v1.obj = __atomic_load_n(&(Table[key].tsw.obj), __ATOMIC_ACQUIRE);
        continue;
      }
    }

    return_val = Table[key].val;

    v2.obj = __atomic_load_n(&(Table[key].tsw.obj), __ATOMIC_ACQUIRE);
    if (v1 == v2 && !v1.lock) break;
    else v1 = v2;
  } 

  this->appro_commit_ts = max(this->appro_commit_ts, v1.wts);
  readSet.push_back(SetElement(key, return_val, v1));

  return return_val;
}

void 
Transaction::twrite(unsigned int key, unsigned int val)
{
  SetElement *result;

  result = searchWriteSet(key);
  if (result) {
    result->val = val;
    return;
  }

  TsWord tsword;
  tsword.obj = __atomic_load_n(&(Table[key].tsw.obj), __ATOMIC_ACQUIRE);
  this->appro_commit_ts = max(this->appro_commit_ts, tsword.rts() + 1);
  writeSet.push_back(SetElement(key, val, tsword));
}

bool 
Transaction::validationPhase()
{
  lockWriteSet();
  if (this->status == TransactionStatus::aborted) {
    return false;
  }

  // logically, it must execute full fence here,
  // while we assume intel architecture and CAS(cmpxchg) in lockWriteSet() did it.
  //
  asm volatile ("" ::: "memory");

  // step2, compute the commit timestamp
  for (auto itr = writeSet.begin(); itr != writeSet.end(); ++itr) {
    TsWord loadtsw;
      loadtsw.obj = __atomic_load_n(&(Table[(*itr).key].tsw.obj), __ATOMIC_ACQUIRE);
    commit_ts = max(commit_ts, loadtsw.rts() + 1);
  } 

  for (auto itr = readSet.begin(); itr != readSet.end(); ++itr) {
    commit_ts = max(commit_ts, (*itr).tsw.wts);
  }


  // step3, validate the read set.
  for (auto itr = readSet.begin(); itr != readSet.end(); ++itr) {

    TsWord v1, v2;
    SetElement *inW = searchWriteSet((*itr).key);

      v1.obj  = __atomic_load_n(&(Table[(*itr).key].tsw.obj), __ATOMIC_ACQUIRE);
    for (;;) {
      if ((*itr).tsw.wts != v1.wts) {
        TsWord pre_v1;
        pre_v1.obj = __atomic_load_n(&(Table[(*itr).key].pre_tsw.obj), __ATOMIC_ACQUIRE);
        if (pre_v1.wts <= commit_ts && commit_ts < v1.wts) break;
        else return false;
      }

      if ((v1.rts()) < commit_ts && v1.lock) {
        if (inW == nullptr) return false;
      }

      if (inW != nullptr) break;
      //extend the rts of the tuple
      if ((v1.rts()) < commit_ts) {
        rtsudctr++;
        // Handle delta overflow
        uint64_t delta = commit_ts - v1.wts;
        uint64_t shift = delta - (delta & 0x7fff);
        v2.obj = v1.obj;
        v2.wts = v2.wts + shift;
        v2.delta = delta - shift;
        if (__atomic_compare_exchange_n(&(Table[(*itr).key].tsw.obj), &(v1.obj), v2.obj, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE))
          break;
        else continue;
      } else {
        rts_non_udctr++;
        break;
      }
    }
  }

  return true;
}

void 
Transaction::abort() 
{
  unlockCLL();

  readSet.clear();
  writeSet.clear();
  cll.clear();
}

void 
Transaction::writePhase()
{
  TsWord result;
  for (auto itr = writeSet.begin(); itr != writeSet.end(); ++itr) {
    Table[(*itr).key].val = (*itr).val;
    result.wts = this->commit_ts;
    result.delta = 0;
    result.lock = 0;
    __atomic_store_n(&(Table[(*itr).key].pre_tsw.obj), (*itr).tsw.obj, __ATOMIC_RELAXED);
    __atomic_store_n(&(Table[(*itr).key].tsw.obj), result.obj, __ATOMIC_RELEASE);

  }

  readSet.clear();
  writeSet.clear();
  cll.clear();
}

void 
Transaction::lockWriteSet()
{
  TsWord expected, desired;

  sort(writeSet.begin(), writeSet.end());
  for (auto itr = writeSet.begin(); itr != writeSet.end(); ++itr) {
    //lock
    expected.obj = __atomic_load_n(&(Table[(*itr).key].tsw.obj), __ATOMIC_ACQUIRE);
    for (;;) {
      //no-wait locking in validation
      //ロックオブジェクトを作ってデストラクタで解放
      //オブジェクトの中身はtsw へのポインタ
      if (expected.lock) {
        this->status = TransactionStatus::aborted;
        unlockCLL();
        return;
      }
      desired = expected;
      desired.lock = 1;
      if (__atomic_compare_exchange_n(&(Table[(*itr).key].tsw.obj), &(expected.obj), desired.obj, false, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) break;
    }
    cll.push_back((*itr).key);
  }
}

void 
Transaction::unlockCLL()
{
  TsWord expected, desired;

  for (auto itr = cll.begin(); itr != cll.end(); ++itr) {
    //unlock
    expected.obj = __atomic_load_n(&(Table[(*itr)].tsw.obj), __ATOMIC_ACQUIRE);
    desired.obj = expected.obj;
    desired.lock = 0;
    __atomic_store_n(&(Table[(*itr)].tsw.obj), desired.obj, __ATOMIC_RELEASE);
  }
}

void
Transaction::dispWS()
{
  cout << "th " << this->thid << ": write set: ";

  for (auto itr = writeSet.begin(); itr != writeSet.end(); ++itr) {
    cout << "(" << (*itr).key << ", " << (*itr).val << "), ";
  }
  cout << endl;
}
