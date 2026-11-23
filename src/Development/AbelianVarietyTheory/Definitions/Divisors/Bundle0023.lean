module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
section
noncomputable section

open Matrix
open scoped NNReal Classical

namespace GlobalTheory.WeilM.SplitModel

variable {K : Type} [Field K]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable [Invertible (2 : K)]





variable [Fintype K]

variable [TopologicalSpace K] [DiscreteTopology K] [IsTopologicalRing K]





end GlobalTheory.WeilM.SplitModel

namespace GlobalTheory.WeilM.SplitModel

end GlobalTheory.WeilM.SplitModel

end

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : R)]


omit [DecidableEq α] in
theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

end Alg

section Forms

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]




end Forms

section RankZero

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]


variable [TopologicalSpace R] [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology R E] {C : TestClass R}



end RankZero


end GlobalTheory.WeilM.SiegelModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
section
noncomputable section

namespace GlobalTheory.ColRows

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

structure KerTies (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) : Prop where
  host : HostTie (ofRecord D L Del h0) t.seam t.Pr
  wts : ∃ pl : RPl D.R ≃ t.X.Tau, ∀ u, WeightTie (ofRecord D L Del h0) W pl (t.word u) (letterOf D L Del h0 u)
  chr : CharTie (ofRecord D L Del h0) t.seam W t.Ch t.glob t.sel
  an : AnalyticTie D t.δ t.χ t.cD
  mu0 : t.tup D.what₂.mu0 = 1
  sharp : (t.cst D.what₂.mu0).sharp = true
  m2 : t.m2 = D.R.m - 2
  fld : ∀ u, FieldOfDefinition W t.sel (t.tup D.what₂.mu0) (t.cst D.what₂.mu0) (t.word u) t.amb

structure KerSizes (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (CY CT : ℝ) : Prop where
  sizes : Sizes t.Pr W L.sc.a
  what₂ : ∀ u, GlobalTheory.Core.Ht2.SizeRowsS CY (ofRecord D L Del h0) (letterOf D L Del h0 u)
  logT : ∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * L.sc.L

end GlobalTheory.ColRows

end
end

