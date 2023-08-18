module Hedgehog.Internal.Function.Derive

import Language.Reflection.Util

import Hedgehog.Internal.Function

%default total

perturbClaim : Visibility -> Name -> ParamTypeInfo -> Decl
perturbClaim vis fun p = simpleClaim vis fun $ piAll `(~(p.applied) -> Seed -> Seed) $ allImplicits p "Cogen"

perturbDef : List Name -> Name -> TypeInfo -> Decl
perturbDef nms fun ti = def fun $ map clause $ [0 .. length ti.cons] `zip` ti.cons where
  clause : (Nat, Con _ _) -> Clause
  clause (idx, con) = accumArgs unerased (\x => `(~(var fun) ~x)) rhs arg con where

    arg : BoundArg 1 Unerased -> TTImp
    arg $ BA g [x] _ = assertIfRec nms g.type `(Function.perturb ~(varStr x) . Function.shiftArg)

    rhs : SnocList TTImp -> TTImp
    rhs = foldr (\l, r => `(~l . ~r)) `(Seed.variant ~(primVal $ B64 $ cast idx))

cogenImplClaim : Visibility -> Name -> ParamTypeInfo -> Decl
cogenImplClaim vis impl p = implClaimVis vis impl $ implType "Cogen" p

cogenImplDef : (fun, impl : Name) -> Decl
cogenImplDef fun impl = def impl $ pure $ patClause (var impl) (var "MkCogen" `app` var fun)

export
CogenVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
CogenVis vis nms p = do
  let fun  := funName p "perturb"
  let impl := implName p "Cogen"
  Right [ TL (perturbClaim vis fun p) (perturbDef nms fun p.info)
        , TL (cogenImplClaim vis impl p) (cogenImplDef fun impl)
        ]

||| Alias for `CogenVis Public`
export %inline
Cogen : List Name -> ParamTypeInfo -> Res (List TopLevel)
Cogen = CogenVis Public
