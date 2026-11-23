module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOKg2
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx
  Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.KerJoinS Formalism.IndefR.CxPass

namespace GlobalTheory.MiS
open _root_.Formalism Formalism.IndefR Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC}

def DcPtG {ex : Extra D L hT Gi Gl Kc Yd cX} (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

structure RealPack (ex : Extra D L hT Gi Gl Kc Yd cX) where

  R : Formalism.L2.RecT ex

  S : Formalism.L2.SG.SpectralTiesReal.STiesR R

  P : RowSideFamily ex

  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)

  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)

  Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3

  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]

  Q : RealT R P Dcf Spf Zscf S Ks

attribute [instance] RealPack.fKs RealPack.nKs RealPack.aKs

variable {ex : Extra D L hT Gi Gl Kc Yd cX}

def HypAt (W : RealPack ex) : Prop :=
  Nonempty (Formalism.L2.SG.JoinSI.JoinSI W.R W.S W.Q) ∧
    (∀ u, Formalism.L2.SG.ColDict.LevelMatch W.S.X (W.S.tr u) W.S.Y.hK) ∧ DcPtG W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl

abbrev cxW (W : RealPack ex) := W.Q.Rl.toCx3 W.Q.F

def LevHyp (W : RealPack ex) : Prop :=
  (∃ s, W.P.A3.fam3.Ok3 s) ∧ (cxW W).RatZ ∧
    ∃ gE : Representation ℂ W.P.Gp (cxW W).EE, GUnit3 (cxW W) gE ∧ GEquiv3 W.P.A3 (cxW W) gE ∧
      PrincipalLevelBijectivity W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE false W.P.P0 W.P.ψ0 ∧
      LevType3 W.P.A3 (cxW W) (P1 := W.P.Ps) (ψ1 := W.P.ψs) (Dc := W.Dcf) (Sp := W.Spf) (Zsc := W.Zscf) gE true W.P.Ps W.P.ψs

end GlobalTheory.MiS

end
