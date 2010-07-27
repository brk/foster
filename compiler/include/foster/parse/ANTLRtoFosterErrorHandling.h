// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef ANTLR_TO_FOSTER_ERROR_HANDLING_H
#define ANTLR_TO_FOSTER_ERROR_HANDLING_H

#include <antlr3defs.h>

namespace foster {

void installRecognitionErrorFilter(pANTLR3_BASE_RECOGNIZER recognizer);

}

#endif // header guard

