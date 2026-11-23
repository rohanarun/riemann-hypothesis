module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.HarderNarasimhan.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
section
noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)

abbrev ColsK : Type := MfV (Pr := B.primes X) B.wts I.Ch u

abbrev RowsK : Type := MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps

structure CplData where

  b : (I.idx a).β (B.R.m - 2 + 1)
  hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) (I.cst a) (I.idx a) u (B.R.m - 2) b
  hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) b hY I.Ps
  hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok

variable {I u a}

def CplData.per (c : CplData I u a) (h : I.Ok) (hX : B.fields.Ok) :
    ColsK I u →ₗ[B.fields.K] RowsK I a →ₗ[B.fields.K] B.fields.K :=
  PtilE (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u ∘ₗ
    colMu (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u (B.R.m - 2) c.b c.hY I.Ps c.hK c.hF (h.idx_ok a)

variable (I u a) (l : I.Laws)

def IsCol (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) : Prop :=
  ∀ c : (I.stp u a 0).Cl, x.1 c = φ.1 ((I.stp u a 0).rep c).1.1.deco

def IsRow (F : (I.per l u a).Mt) (z : RowsK I a) : Prop :=
  ∀ p : (I.stX a).D (), F.1 () p = MvPolynomial.map B.embLL (z.1 (toRow I.sel (I.tup a) p.1.1)).1

def ColMatch (h : I.Ok) (hX : B.fields.Ok) : Prop :=
  Nonempty (CplData I u a) ∧ ∀ (c : CplData I u a) x φ F z, IsCol I u a l x φ → IsRow I u a l F z →
    (I.per l u a).PtilCol ((I.fm l u a).emb 0 x) F = B.embLL (c.per h hX φ z)

def ColMatchAll : Prop :=
  ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (_Z : TC.Later B (I.cols l)),
    ColIn.JetsIn I → ∀ u a, ColMatch I u a l h hX

end GlobalTheory.Core.Ht2

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
section
noncomputable section

open scoped NNReal
open Set Metric Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EisCont

variable {D : D7}

def RegAt (T : HSp D) (e : ℂ → GA D T → ℂ) (s₀ : ℂ) (k : ℕ) : Prop :=
  ∃ (r : ℝ) (H : ℂ → GA D T → ℂ), 0 < r ∧
    (∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * cont (fun z => e z g) s) ∧
    (∀ g, DifferentiableOn ℂ (H · g) (ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × GA D T => H x.1 x.2) (ball s₀ r ×ˢ univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball s₀ r, ∀ g, ‖H s g‖ ≤ C * Grow.height T g ^ N

def ContMod (T : HSp D) (e : ℂ → GA D T → ℂ) : Prop := (∀ g, Continues fun z => e z g) ∧ ∀ s₀, ∃ k, RegAt T e s₀ k

def detChar {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (μ : (AE D)ˣ →* Circle) : stab d →* Circle :=
  μ.comp (Matrix.GeneralLinearGroup.det.comp (onX d))

abbrev lev (T : HSp D) (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)) : Subgroup (GA D T) := AdelicU.levelAll D.sp.cm.sig T.gram L a

structure IsLevel (T : HSp D) (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin T.rank → D.host.E))
    (a : GL (Fin T.rank) (AE D)) : Prop where
  lat : Submodule.IsLattice D.host.E L
  dual : ∀ v, AdelicU.IsSelfDualAt D.sp.cm.sig T.gram L v
  maj : AdelicU.IsMajorantFrame D.sp.cm.sig T.gram a

end GlobalTheory.EisCont

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.L2.SG.PackageTie2 Formalism.L2.SG.SpectralTiesReal
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Link (D : D7) (u : D.what₂.Word) (W : Tower D) where

  P : W.Lv

  eT : (D.mem u).P.Mt →ₗ[ℂ] W.CXP P
  eT_onto : Function.Surjective eT

  jE : W.CP P 0 →ₗ⋆[ℂ] D.s.HH
  jE_onto : Function.Surjective jE

  Θ : Desc D u
  Θ_eq : ∀ F, ∃ T₀ : W.CP P 0, W.IsDn (eT F) T₀ ∧ Θ F = jE T₀

namespace Link

variable {D : D7} {u : D.what₂.Word} {W : Tower D} (L : Link D u W)


end Link

structure STrue (D : D7) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) extends STies D where

  hF : FinX Y
  tr : ∀ u, Formalism.L2.SG.ColDict.Transport X u (F₀ u)
  into : ∀ u, Formalism.L2.SG.ColDict.ColDictInto X (tr u) Y.hK
  bij : ∀ u, Formalism.L2.SG.ColDict.ColDictBij X (tr u) Y.hK
  lev : ∀ u, Formalism.L2.SG.ColDict.LevelMatch X (tr u) Y.hK
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    Formalism.L2.SG.ColDict.colDict X (tr u) Y.hK (into u) (bij u) ((hI hF).eCu u x) = D.s_Cu u x
  inst : X.B.I = RationalEmbedding.inst D
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

section Bare

variable {D : D7} {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u}

end Bare

section Built

open GlobalTheory.Mem GlobalTheory.Mem.Col2

structure World {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) where
  ok : I.Ok
  pins : TC.Pins B X
  C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)
  std : I.StdC l Z C
  S : STrue (I.rec7 l Z) fun u => (C.forms u).to0

def TrueD (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), D = I.rec7 l Z ∧ Nonempty (World I l Z)

theorem TrueD.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), World I l Z → Q (I.rec7 l Z))
    {D : D7} (hD : TrueD D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, ⟨w⟩⟩ := hD
  exact h B X I l Z w

theorem TrueD.sTies {D : D7} (hD : TrueD D) :
    ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D :=
  TrueD.elim (Q := fun D => ∃ S : STies D, FinX S.Y ∧ Formalism.L2.SG.Pf.LocCP.LocTied D)
    (fun _ _ _ _ _ w => ⟨w.S.toSTies, w.S.hF, w.S.locTied⟩) hD

section Maps

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)}

end Maps

end Built

variable (D : D7) (u : D.what₂.Word)

end GlobalTheory.Core.Rk

end
end

