#include "lp_utils.h"
#ifdef lp_for_z3
namespace lp {
double numeric_traits<double>::g_zero = 0.0;
double numeric_traits<double>::g_one = 1.0;
}
#endif
