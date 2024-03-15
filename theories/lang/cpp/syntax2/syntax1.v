(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax2.prelude.

Require Export bedrock.lang.cpp.syntax.names(
  ident,
  localname,
  field_name.t(..),
  Build_field
).
Bind Scope bs_scope with ident.
Bind Scope bs_scope with localname.

Require Export bedrock.lang.cpp.arith.types.

Require Export bedrock.lang.cpp.syntax.types(
  type_qualifiers(..), q_const, q_volatile, CV, merge_tq,
  calling_conv(..),
  function_arity(..),
  char_type.t(..), char_type,
  int_type.t, int_type.rank, int_type.Ichar, int_type.Ishort, int_type.Iint, int_type.Ilong, int_type.Ilonglong,
  float_type.t(..),
  char_bits, short_bits, int_bits, long_bits, long_long_bits
).

Require Export bedrock.lang.cpp.syntax.expr(
  OverloadableOperator(..),
  evaluation_order.t(..),
  UnOp(..),
  BinOp(..),
  AtomicOp(..),
  BuiltinFn(..),
  Cast'(..), Cast.existsb,
  dispatch_type(..),
  ValCat(..),
  operator_impl.t(..), operator_impl.functype, operator_impl.existsb,
  new_form.t(..), new_form,
  MethodRef', MethodRef.existsb,
  (** relevant to keys in translation units *)
  Nenum_const
).

Require Export bedrock.lang.cpp.syntax.stmt.

Require Export bedrock.lang.cpp.syntax.decl.

Require Export bedrock.lang.cpp.syntax.translation_unit(
  ObjValue'(..),
  GlobDecl'(..),
  GlobalInit'(..),
  GlobalInitializer'(..), g_name, g_type, g_init,
  InitializerBlock'
).
