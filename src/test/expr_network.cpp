/*++
Copyright (c) 2019 Microsoft Corporation

--*/

#include "ast/expr_network.h"
#include "ast/reg_decl_plugins.h"

void display_cuts(vector<expr_network::cut_set> const& cuts) {
    unsigned idx = 0;
    for (auto const& cs : cuts) {
        std::cout << idx << ": ";
        for (auto const& cut : cs) {
            std::cout << cut << " ";
        }
        std::cout << "\n";
        ++idx;
    }
}

static void tst_expr_network1() {
    ast_manager m;
    reg_decl_plugins(m);
    expr_network nw(m);
    expr_ref x(m.mk_const("x", m.mk_bool_sort()), m);
    expr_ref y(m.mk_const("y", m.mk_bool_sort()), m);
    nw.add_root(m.mk_and(x, y));
    nw.add_root(m.mk_and(y, x));
    auto cuts = nw.get_cuts(4);
    display_cuts(cuts);
}

static void tst_expr_network2() {

    {
        // x0.shift_table(x0.x1):       01    -> 0101
        expr_network::cut cut1, cut2;
        cut1.m_table = 0x2;
        cut1.add(0);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(1);
        std::cout << cut1 << "\n";
    }

    {
        // x0.shift_table(x0.x1.x2):    10   -> 1010 1010
        expr_network::cut cut1, cut2;
        cut1.m_table = 0x2;
        cut1.add(0);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(1);
        cut1.add(2);

        std::cout << cut1 << "\n";
    }

    {
        // x1.shift_table(x0.x1.x2):    10   -> 1100 1100
        expr_network::cut cut1, cut2;
        cut1.m_table = 0x2;
        cut1.add(1);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(0);
        cut1.add(2);
        cut1.sort();
        std::cout << cut1 << "\n";
    }

    {
        // x0.x1.shift_table(x0.x1.x2): 1011 -> 1011 1011
        expr_network::cut cut1, cut2;
        cut1.m_table = 0xb;
        cut1.add(0);
        cut1.add(1);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(2);
        std::cout << cut1 << "\n";
    }

    {
        // x1.x2.shift_table(x0.x1.x2): 1011 -> 1100 1111
        expr_network::cut cut1, cut2;
        cut1.m_table = 0xb;
        cut1.add(1);
        cut1.add(2);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(0);
        cut1.sort();
        std::cout << cut1 << "\n";
    }
    {
        // x2.shift_table(x0.x1.x2):    10   -> 1111 0000
        expr_network::cut cut1, cut2;
        cut1.m_table = 0x2;
        cut1.add(2);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(0);
        cut1.add(1);
        cut1.sort();
        std::cout << cut1 << "\n";
    }

    {
        // x0.x2.shift_table(x0.x1.x2): 1011 -> 1010 1111
        expr_network::cut cut1, cut2;
        cut1.m_table = 0xb;
        cut1.add(0);
        cut1.add(2);
        std::cout << cut1 << "\n";
        cut2.add(0);
        cut2.add(1);
        cut2.add(2);
        cut1.m_table = cut1.shift_table(cut2);
        cut1.add(1);
        cut1.sort();
        std::cout << cut1 << "\n";
    }


}

void tst_expr_network() {
    tst_expr_network1();
    tst_expr_network2();
}
