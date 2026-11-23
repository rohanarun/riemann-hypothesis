module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033

@[expose] public section

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RealSide.Framed {D : D7} (X : RealSide D) : Prop :=
  ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV

theorem RealSide.space_eq {D : D7} (X : RealSide D) (j : Fin D.R.m) :
    X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
  X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀

section At

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
  [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
  (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
  (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)

def TwAt (_H : NExpRealH R cG S YS) (cf : CharFrame D) : Type 1 :=
  TwJoin hL D nch xd first R F cG geo S YS cf

variable {hL D nch xd first R F cG geo S YS}

theorem TwAt.Sb_eq {H : NExpRealH R cG S YS} {cf : CharFrame D} (a : TwAt hL D nch xd first R F cG geo S YS H cf) :
    a.X.R.Sb = R.Sb := TwJoin.Sb_eq a

end At

def TwExt (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  TwAt hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp c.row.hecke (TC.cf w.I w.l Z)

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)}

end Rows

end GlobalTheory.TwInputs

end
