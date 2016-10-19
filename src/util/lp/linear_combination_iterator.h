/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
namespace lean {
template <typename T>
struct linear_combination_iterator {
    virtual bool next(T & a, unsigned & i) = 0;
    virtual void reset() = 0;
    virtual linear_combination_iterator * clone() = 0;
    virtual ~linear_combination_iterator(){}
};
}
