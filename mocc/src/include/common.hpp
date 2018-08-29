#ifndef COMMON_HPP
#define COMMON_HPP

#include "int64byte.hpp"
#include "procedure.hpp"
#include "tuple.hpp"
#include <atomic>

#ifdef GLOBAL_VALUE_DEFINE
	#define GLOBAL

GLOBAL std::atomic<int> Running(0);
GLOBAL std::atomic<int> Ending(0);
GLOBAL std::atomic<uint64_t> GlobalEpoch(1);
GLOBAL std::atomic<bool> Finish(false);

#else
	#define GLOBAL extern

GLOBAL std::atomic<int> Running;
GLOBAL std::atomic<int> Ending;
GLOBAL std::atomic<uint64_t> GlobalEpoch;
GLOBAL std::atomic<bool> Finish;

#endif

GLOBAL std::atomic<uint64_t> *ThLocalEpoch;

// run-time args
GLOBAL unsigned int TUPLE_NUM;
GLOBAL unsigned int MAX_OPE;
GLOBAL unsigned int THREAD_NUM;
GLOBAL unsigned int PRO_NUM;
GLOBAL float READ_RATIO;
GLOBAL uint64_t CLOCK_PER_US;
GLOBAL uint64_t EPOCH_TIME;
GLOBAL int EXTIME;

GLOBAL uint64_t_64byte *ThRecentTID;
GLOBAL uint64_t_64byte *FinishTransactions;
GLOBAL uint64_t_64byte *AbortCounts;

// ログ永続化エミュレーション用
GLOBAL uint64_t_64byte *Start;	
GLOBAL uint64_t_64byte *Stop;
GLOBAL uint64_t Bgn;
GLOBAL uint64_t End;

GLOBAL Procedure **Pro;
GLOBAL Tuple *Table;

#endif	//	COMMON_HPP
