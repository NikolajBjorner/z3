/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <vector>
#include "util/lp/indexed_vector.cpp"
namespace lean {
template void indexed_vector<double>::clear();
template void indexed_vector<double>::clear_all();
template void indexed_vector<double>::erase_from_index(unsigned int);
template void indexed_vector<double>::set_value(const double&, unsigned int);
template void indexed_vector<mpq>::clear();
template void indexed_vector<unsigned>::clear();
template void indexed_vector<mpq>::clear_all();
template void indexed_vector<mpq>::erase_from_index(unsigned int);
template void indexed_vector<mpq>::resize(unsigned int);
template void indexed_vector<unsigned>::resize(unsigned int);
template void indexed_vector<mpq>::set_value(const mpq&, unsigned int);
template void indexed_vector<unsigned>::set_value(const unsigned&, unsigned int);
#ifdef LEAN_DEBUG
template bool indexed_vector<double>::is_OK() const;
template bool indexed_vector<mpq>::is_OK() const;
template bool indexed_vector<lean::numeric_pair<mpq> >::is_OK() const;
template void lean::indexed_vector< lean::mpq>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lean::indexed_vector<double>::print(std::basic_ostream<char,struct std::char_traits<char> > &);
template void lean::indexed_vector<lean::numeric_pair<lean::mpq> >::print(std::ostream&);
#endif
}
template void lean::print_vector<double>(std::vector<double, std::allocator<double> > const&, std::ostream&);
template void lean::print_vector<unsigned int>(std::vector<unsigned int> const&, std::ostream&);
template void lean::print_vector<std::string>(std::vector<std::string, std::allocator<std::string> > const&, std::ostream&);
template void lean::print_vector<lean::numeric_pair<lean::mpq> >(std::vector<lean::numeric_pair<lean::mpq>, std::allocator<lean::numeric_pair<lean::mpq> > > const&, std::ostream&);
template void lean::indexed_vector<double>::resize(unsigned int);
template void lean::print_vector< lean::mpq>(std::vector< lean::mpq, std::allocator< lean::mpq> > const &, std::basic_ostream<char, std::char_traits<char> > &);
template void lean::indexed_vector<lean::numeric_pair<lean::mpq> >::erase_from_index(unsigned int);
