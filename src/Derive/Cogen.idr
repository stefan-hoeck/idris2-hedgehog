module Derive.Cogen

import public Hedgehog.Internal.Function as Hedgehog

import public Language.Reflection.Util

%default total

||| Derivation facility for `Gogen` interface
|||
||| Use `derive`, `deriveIndexed` or `derivePattern` from
||| `Language.Reflection.Derive` for simple, purely indexed or mixed data types
export
CogenVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
CogenVis vis nms p = do
  let fun  := funName p "perturb"
  let impl := implName p "Cogen"
  Right
    [ TL (perturbClaim fun p) (perturbDef fun p.info)
    , TL (cogenImplClaim impl p) (cogenImplDef fun impl)
    ]

  where
    perturbClaim : Name -> ParamTypeInfo -> Decl
    perturbClaim fun p =
      simpleClaim vis fun $
        piAll `(~(p.applied) -> StdGen -> StdGen) $ allImplicits p "Cogen"

    perturbDef : Name -> TypeInfo -> Decl
    perturbDef fun ti =
      def fun $ map clause $ [0 .. length ti.cons] `zip` ti.cons where

      clause : (Nat, Con _ _) -> Clause
      clause (idx, con) =
        accumArgs unerased (\x => `(~(var fun) ~x)) rhs arg con where

        arg : BoundArg 1 Unerased -> TTImp
        arg $ BA g [x] _ =
          assertIfRec nms g.type
            `(Function.perturb ~(varStr x) . Function.shiftArg)

        rhs : SnocList TTImp -> TTImp
        rhs = foldr (\l, r => `(~l . ~r))
                    `(System.Random.Pure.variant (fromInteger ~(primVal $ BI $ cast idx)))

    cogenImplClaim : Name -> ParamTypeInfo -> Decl
    cogenImplClaim impl p = implClaimVis vis impl $ implType "Cogen" p

    cogenImplDef : (fun, impl : Name) -> Decl
    cogenImplDef fun impl =
      def impl $ pure $ patClause (var impl) (var "MkCogen" `app` var fun)


||| Alias for `CogenVis Public`
export %inline
Cogen : List Name -> ParamTypeInfo -> Res (List TopLevel)
Cogen = CogenVis Public
