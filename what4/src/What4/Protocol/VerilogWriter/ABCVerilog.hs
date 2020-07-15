{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-
Module           : What4.Protocol.VerilogWriter.Export.ABCVerilog
Copyright        : (c) Galois, Inc 2020
Maintainer       : Aaron Tomb <atomb@galois.com>
License          : BSD3

Export Verilog in the particular syntax ABC supports.
-}

module What4.Protocol.VerilogWriter.ABCVerilog where

import Data.BitVector.Sized
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.String
import Data.Text.Prettyprint.Doc
import What4.BaseTypes
import What4.Protocol.VerilogWriter.AST
import Prelude hiding ((<$>))

moduleDoc :: Module sym n -> Doc () -> Doc ()
moduleDoc (Module ms) name =
  vsep
    [ nest 2 $ vsep
      [ "module" <+> name <> tupled params <> semi
      , vsep (map inputDoc (reverse (vsInputs ms)))
      , vsep (map (wireDoc "wire") (reverse (vsWires ms)))
      , vsep (map (wireDoc "output") (reverse (vsOutputs ms)))
      ]
    , "endmodule"
    ]
  where
    inputNames = map (identDoc . snd) (vsInputs ms)
    outputNames = map (identDoc . (\(_, _, n, _) -> n)) (vsOutputs ms)
    params = reverse inputNames ++ reverse outputNames

typeDoc :: Doc () -> Bool -> BaseTypeRepr tp -> Doc ()
typeDoc ty _ BaseBoolRepr = ty
typeDoc ty isSigned (BaseBVRepr w) =
  ty <+>
  (if isSigned then "signed " else mempty) <>
  lbracket <>
  pretty (intValue w - 1) <>
  ":0" <>
  rbracket
typeDoc _ _ _ = "<type error>"

identDoc :: Identifier -> Doc ()
identDoc = pretty

lhsDoc :: LHS -> Doc ()
lhsDoc (LHS name) = identDoc name
lhsDoc (LHSBit name idx) =
  identDoc name <> lbracket <> pretty idx <> rbracket

inputDoc :: (Some BaseTypeRepr, Identifier) -> Doc ()
inputDoc (tp, name) =
  viewSome (typeDoc "input" False) tp <+> identDoc name <> semi

wireDoc :: Doc () -> (Some BaseTypeRepr, Bool, Identifier, Some Exp) -> Doc ()
wireDoc ty (tp, isSigned, name, e) =
  viewSome (typeDoc ty isSigned) tp <+>
  identDoc name <+>
  equals <+>
  viewSome expDoc e <>
  semi

unopDoc :: Unop tp -> Doc ()
unopDoc = pretty . showUnop

binopDoc :: Binop inTp outTp -> Doc ()
binopDoc = pretty . showBinop

-- | Show non-negative Integral numbers in base 16.
hexDoc :: NatRepr w -> BV w -> Doc ()
hexDoc w n = fromString $ ppHex w n

decDoc :: NatRepr w -> BV w -> Doc ()
decDoc w n = fromString $ ppDec w n

iexpDoc :: IExp tp -> Doc ()
iexpDoc (Ident _ name) = identDoc name

-- NB: special pretty-printer because ABC has a hack to detect this specific syntax
rotateDoc :: String -> String -> NatRepr w -> IExp tp -> BV w -> Doc ()
rotateDoc op1 op2 wr@(intValue -> w) e n =
  parens (v <+> fromString op1 <+> nd) <+> "|" <+>
  parens (v <+> fromString op2 <+> parens (pretty w <+> "-" <+> nd))
    where v = iexpDoc e
          nd = decDoc wr n

expDoc :: Exp tp -> Doc ()
expDoc (IExp e) = iexpDoc e
expDoc (Binop op l r) = iexpDoc l <+> binopDoc op <+> iexpDoc r
expDoc (Unop op e) = unopDoc op <+> iexpDoc e
expDoc (BVRotateL wr e n) = rotateDoc "<<" ">>" wr e n
expDoc (BVRotateR wr e n) = rotateDoc ">>" "<<" wr e n
expDoc (Mux c t e) = iexpDoc c <+> "?" <+> iexpDoc t <+> colon <+> iexpDoc e
expDoc (Bit e i) =
  iexpDoc e <> lbracket <> pretty i <> rbracket
expDoc (BitSelect e (intValue -> start) (intValue -> len)) =
  iexpDoc e <> lbracket
            <> pretty (start + (len - 1))
            <> colon
            <> pretty start
            <> rbracket
expDoc (Concat _ es) = encloseSep lbrace rbrace comma (map (viewSome iexpDoc) es)
expDoc (BVLit w n) = pretty (intValue w) <> "'h" <> hexDoc w n
expDoc (BoolLit True) = "1'b1"
expDoc (BoolLit False) = "1'b0"
