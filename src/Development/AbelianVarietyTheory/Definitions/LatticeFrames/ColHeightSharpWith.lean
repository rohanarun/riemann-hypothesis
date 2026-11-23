module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.HarderNarasimhan.Bundle0001

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Ht2

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

def SizeRowsS (CY : ℝ) (N : NumDatum) (δ : Code N) : Prop :=
  (Real.log N.rd ≤ N.sc.L ∧ Real.log N.q ≤ N.sc.L ∧ Real.log N.d ≤ N.sc.L ∧ Real.log (4 * N.sc.x) ≤ N.sc.L ∧
    |N.logDerivativeAtOne| ≤ N.sc.L) ∧
  (∀ i, ((N.R.k : ℝ) * N.sc.b) ^ 8 ≤ N.g i ∧ Real.log (N.g i) ≤ CY * N.sc.L + 1) ∧
  True ∧
  (N.R.f : ℝ) * N.Nm ≤ N.sc.b ∧
  (∀ j ∈ N.lifts, ∀ z, ∀ i < N.R.N (j - 1), 0 ≤ N.nu δ j z i ∧ ((N.nu δ j z i : ℚ) : ℝ) ≤ 3 * N.sc.a) ∧
  (∀ z i j, |(((N.hc z).b i - (N.hc z).e j : ℚ) : ℝ)| ≤ N.eta) ∧
  (∀ z i, 0 ≤ (N.hc z).v i ∧ (((N.hc z).v i : ℚ) : ℝ) ≤ N.Sc) ∧
  (∀ z (i : Fin N.R.k), 1 ≤ i.1 → i.1 + 1 < N.R.k → 0 ≤ N.uW δ z i ∧ ((N.uW δ z i : ℚ) : ℝ) ≤ N.Sc) ∧
  (∀ t ∈ N.TT, N.sc.b' ≤ ((N.bT t : ℚ) : ℝ) ∧ ((N.bT t : ℚ) : ℝ) ≤ 2 * N.sc.b') ∧
  ∀ z, ¬ IsTopPl N z → ∀ hk : 2 ≤ N.R.k,
    (N.hc z).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).v ⟨N.R.k - 2, by omega⟩ - 1 / 2 ∧
    N.Sc ≤ (((N.hc z).u ⟨0, by omega⟩ - (N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) ∧
    (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) ≤ 3 * N.Sc

def HypS (CY : ℝ) {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) {Pr : Primes X} (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m)
    (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
    (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) : Prop :=
  HostTie N s Pr ∧ WeightTie N W pl u δ ∧ CharTie N s W Ch G sel ∧ AnalyticTie D dl χ cD ∧ mu = 1 ∧ cst.sharp = true ∧
    I.Ok Ch sel mu cst G (N.R.m - 2) ∧ Sizes Pr W N.sc.a ∧ SizeRowsS CY N δ

end GlobalTheory.Core.Ht2

end
