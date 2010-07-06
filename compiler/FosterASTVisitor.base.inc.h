// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// Code duplication remover: every visitor header must include this list
// of class names, and the FosterASTVisitor class must include " = 0"
// pure virtual markers. Rather than copy/pasting the list n times...

/// Externally-settable macros
///
///  FOSTER_AST_VISITOR_GEN              (optionally #define to declaration)
///   called for each AST node type
///
/// ---------------------------------------------------------------------------
///
///   NOTE: The following are not intended for use by individual passes.
///
/// FOSTER_AST_VISITOR_PURE_VIRTUAL      (optionally #define)
///   determines whether the function prototypes are marked pure virtual or not.
///   Without getting into really ugly PP hackery, the general functionality of
///   default function implementations isn't very interesting, since there are
///   no useful passes that can be defined completely homogenously, and the
///   impl wouldn't be an override-able default like we want...
///
/// FOSTER_AST_RETVAL                     (optionally #define to a return type)
///   If set, determines the homogenous return type for all visit functions;
///   If unset, the return type for each function defaults to the type of the
///   AST node being visited.

// ----------------------------------------------------------------------------

#ifndef FOSTER_AST_INCLUDED_VIA_DECLS_H
#error "FosterASTVisitor.base.inc.h should not be included directly!"
#endif

// ----------------------------------------------------------------------------

#ifdef  FOSTER_AST_VISITOR_PURE_VIRTUAL
#define FOSTER_AST_VISITOR_IMPL    = 0
#else
#define FOSTER_AST_VISITOR_IMPL
#endif // FOSTER_AST_VISITOR_PURE_VIRTUAL

// ----------------------------------------------------------------------------

#ifndef FOSTER_AST_VISITOR_GEN
#  ifdef FOSTER_AST_RETVAL
#    define FOSTER_AST_VISITOR_GEN(type) \
        virtual FOSTER_AST_RETVAL visit(type* ast) FOSTER_AST_VISITOR_IMPL
#else
#    define FOSTER_AST_VISITOR_GEN(type) \
         virtual type*            visit(type* ast) FOSTER_AST_VISITOR_IMPL
#  endif // FOSTER_AST_RETVAL
#endif // FOSTER_AST_VISITOR_GEN

// ----------------------------------------------------------------------------

FOSTER_AST_VISITOR_GEN(FnAST);
FOSTER_AST_VISITOR_GEN(SeqAST);
FOSTER_AST_VISITOR_GEN(BoolAST);
FOSTER_AST_VISITOR_GEN(CallAST);
FOSTER_AST_VISITOR_GEN(IntAST);
FOSTER_AST_VISITOR_GEN(IfExprAST);
FOSTER_AST_VISITOR_GEN(NilExprAST);
FOSTER_AST_VISITOR_GEN(RefExprAST);
FOSTER_AST_VISITOR_GEN(DerefExprAST);
FOSTER_AST_VISITOR_GEN(ClosureAST);
FOSTER_AST_VISITOR_GEN(VariableAST);
FOSTER_AST_VISITOR_GEN(ArrayExprAST);
FOSTER_AST_VISITOR_GEN(PrototypeAST);
FOSTER_AST_VISITOR_GEN(TupleExprAST);
FOSTER_AST_VISITOR_GEN(SubscriptAST);
FOSTER_AST_VISITOR_GEN(AssignExprAST);
FOSTER_AST_VISITOR_GEN(SimdVectorAST);
FOSTER_AST_VISITOR_GEN(ClosureTypeAST);
FOSTER_AST_VISITOR_GEN(UnaryOpExprAST);
FOSTER_AST_VISITOR_GEN(BinaryOpExprAST);
FOSTER_AST_VISITOR_GEN(ForRangeExprAST);
FOSTER_AST_VISITOR_GEN(BuiltinCompilesExprAST);

// ----------------------------------------------------------------------------

// Undefine any internally-defined macros to make this file
// clean for multiple-inclusion.
#undef FOSTER_AST_VISITOR_IMPL
#undef FOSTER_AST_VISITOR_GEN

