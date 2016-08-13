#pragma once
/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
namespace lean {
class column_namer {
public:
    virtual std::string get_column_name(unsigned j) const = 0;
};
}
