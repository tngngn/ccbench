#include "../include/common.hh"
#include "../include/random.hh"
#include "../include/result.hh"

#pragma once

#define TPCC_SMALL	false
#define NUM_WH          224
#define DIST_PER_WARE	10
#define LASTNAME_LEN 	16

#ifndef GFLAGS_GFLAGS_H_
 #define FLAGS_num_wh NUM_WH
 #define FLAGS_dist_per_ware DIST_PER_WARE
#if TPCC_SMALL
 #define FLAGS_max_items 10000
 #define FLAGS_cust_per_dist 2000
#else
 #define FLAGS_max_items 100000
 #define FLAGS_cust_per_dist 3000
#endif
 #define FLAGS_perc_payment 50      // 43.1 for fullmix
 #define FLAGS_perc_order_status 0  // 4.1
 #define FLAGS_perc_delivery 0      // 4.2
 #define FLAGS_perc_stock_level 0   // 4.1
#endif

namespace TPCC {

enum QueryType { Q_NONE,
                 Q_NEW_ORDER,
                 Q_PAYMENT,
                 Q_ORDER_STATUS,
                 Q_DELIVERY,
                 Q_STOCK_LEVEL };

namespace query {

  class Option {
  public:
    std::uint32_t num_wh = FLAGS_num_wh;
    std::uint32_t dist_per_ware = DIST_PER_WARE;
    std::uint32_t max_items = MAX_ITEMS;
    std::uint32_t cust_per_dist = CUST_PER_DIST;
    double perc_payment = FLAGS_perc_payment;
    double perc_order_status = FLAGS_perc_order_status;
    double perc_delivery = FLAGS_perc_delivery;
    double perc_stock_level = FLAGS_perc_stock_level;

    /**
     * 0                                                    UINT64_MAX
     * |----|--------|--------|--------------|--------------|
     *      ^        ^        ^              ^
     *      |        |        |              threshold_new_order
     *      |        |        threshold_payment
     *      |        threshold_order_status
     *      threshold_delivery
     *
     * used by decideQueryType().
     */
    uint64_t threshold_new_order;
    uint64_t threshold_payment;
    uint64_t threshold_order_status;
    uint64_t threshold_delivery;

    Option() {
      threshold_delivery = perc_stock_level / 100.0 * UINT64_MAX;
      threshold_order_status = threshold_delivery + (perc_delivery / 100.0 * UINT64_MAX);
      threshold_payment = threshold_order_status + (perc_order_status / 100.0 * UINT64_MAX);
      threshold_new_order = threshold_payment + (perc_payment / 100.0 * UINT64_MAX);
#if 0
      ::printf("query_type_threshold: %.3f %.3f %.3f %.3f\n"
               , threshold_new_order    / (double)UINT64_MAX
               , threshold_payment      / (double)UINT64_MAX
               , threshold_order_status / (double)UINT64_MAX
               , threshold_delivery     / (double)UINT64_MAX);
#endif
    }
  };

  class NewOrder {
  public:
    std::uint16_t w_id;
    std::uint8_t d_id;
    std::uint32_t c_id;
    struct {
      std::uint32_t ol_i_id;
      std::uint16_t ol_supply_w_id;
      std::uint8_t ol_quantity;
    } items[15];
    std::uint8_t rbk;
    bool remote;
    std::uint8_t ol_cnt;
    std::time_t o_entry_d;

    void generate(uint16_t w_id0, Xoroshiro128Plus &rnd, Option &opt);
    void print();
  };

  class Payment {
  public:
    std::uint16_t w_id;
    std::uint8_t d_id;
    std::uint32_t c_id;
    std::uint16_t d_w_id;
    std::uint16_t c_w_id;
    std::uint8_t c_d_id;
    char c_last[LASTNAME_LEN + 1];
    double h_amount;
    bool by_last_name;

    void generate(uint16_t w_id0, Xoroshiro128Plus &rnd, Option &opt);
    void print();
  };

  class OrderStatus {};
  class Delivery {};
  class StockLevel {};

} // namespace query

class Query {
public:
  QueryType type = Q_NONE;
  union {
    query::NewOrder new_order;
    query::Payment payment;
    query::OrderStatus order_status;
    query::Delivery delivery;
    query::StockLevel stock_level;
  };

  void generate(uint16_t w_id0, Xoroshiro128Plus &rnd, query::Option &opt);
  void print();
};
}
