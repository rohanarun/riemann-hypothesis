module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsColumnArrows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridReal

open GlobalTheory.SignedHC

theorem num_real_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  intro D large₂ hS τ
  obtain ⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, -⟩ := GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr6 : 6 ≤ D.R.r := by unfold Ranks.r; omega
  set X : ℝ := (D.R.r : ℝ) + 1 with hX
  have hX7 : 7 ≤ X := by
    have : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    linarith
  have hX3 : 0 ≤ X ^ 3 := by positivity

  have hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := by
      have := Pm.Cgap_pos; positivity
    have hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)
      exact_mod_cast this
    have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
    nlinarith

  have hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ) := by
    have hB := ((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1
    have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X := by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl
    rw [hn] at hB
    have h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3 := by positivity
    have h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D) := by
      have := Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ); positivity
    have h4 : (1000 : ℝ) ≤ X ^ 4 := by
      have : (7 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX7 4
      norm_num at this; linarith
    have h7 : 1000 * X ^ 3 ≤ X ^ 7 := by
      have : X ^ 7 = X ^ 4 * X ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h4 hX3
    rw [hga]; linarith
  have hX1 : (1 : ℝ) ≤ 1000 * X ^ 3 := by
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ (by linarith)
    linarith

  have hga0 : (0 : ℝ) ≤ (G.ga : ℝ) := by positivity
  have hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := by rw [hga]; exact hSb
  have hSc := large₂.Sc_pos
  have hbga : (G.ga : ℝ) ≤ large₂.sc.b := by
    have : (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
      nlinarith
    linarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩
  ·
    intro i hi1 hi2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hlt : a + 1 < D.R.k - 1 := by rw [hk] at hi2; omega
    have h := (Pm.sig_gaps τ).1 a hlt
    have e := hv ⟨a, by omega⟩
    have e' := hv ⟨a + 1, hlt⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have : ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ) := by
      rw [show a + 2 + 1 = a + 1 + 2 by omega]; linarith
    exact_mod_cast this
  ·
    have h := (Pm.sig_gaps τ).2.1 (by omega) (by omega)
    have e := hv ⟨D.R.k - 2, by omega⟩
    have e' := hb ⟨0, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    have : (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  ·
    intro l hl1 hl2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hl1
    have hlt : j + 1 < D.R.m := by rw [hm] at hl2; omega
    have h := (Pm.nodes_gap τ j hlt).1
    have hf := Pm.heightBound_ge_rank_cubic
    have e := hb ⟨j + 1, hlt⟩
    have e' := hb ⟨j, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      have h44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
      have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
      have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hY 3
    have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
    have : ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ) := by nlinarith
    exact this
  · exact hgap
  ·
    have h := (large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    rw [hv] at h
    simp only at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    exact_mod_cast h
  ·
    have h := (hpos τ ⟨0, by omega⟩).1
    have e := hb ⟨0, by omega⟩
    have h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact_mod_cast h'
  ·
    have h := (large₂.cloud_v τ ⟨0, by omega⟩).2
    rw [hv] at h
    simp only [zero_add] at h
    have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      unfold GridData.a; rw [hm]; push_cast; ring
    rw [e]; linarith
  ·
    have h := large₂.b_le τ ⟨D.R.m - 1, by omega⟩
    rw [hb] at h
    simp only at h
    rw [hm, show D.R.m = D.R.m - 1 + 1 by omega]
    exact h
  ·
    have h8 : 8 * X ≤ 1000 * X ^ 3 := by
      have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ (by linarith)
      have : X ^ 3 = X * X ^ 2 := by ring
      have hXX : X ≤ X ^ 3 := by rw [this]; nlinarith
      linarith
    have hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4 := by
      have : large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3 := by ring
      rw [this]
      have : (1 : ℝ) ≤ large₂.sc.b ^ 3 := one_le_pow₀ hb1
      nlinarith
    linarith

end GlobalTheory.GridReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefCont

theorem continuous_coefR : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  intro D θ hθ V S M v a
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  unfold coefR
  refine continuous_finsetProd _ fun τ _ => ?_

  have hc : Continuous fun g : GA D V => cmp θ τ g := GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)
  have hu : ∀ g : GA D V, (cmp θ τ g)ᴴ * gramAt D V τ * cmp θ τ g = gramAt D V τ := by
    intro g
    have h0 := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram (tauE D τ)
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x) (θ τ) (hθ τ) g
    have he : (cmp θ τ g)ᴴ = ((cmp θ τ g).map (starRingEnd ℂ)).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he]
    exact h0
  have hB : M.fr τ * (M.fr τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hmem : ∀ g : GA D V, Formalism.REAL.inUJ (M.ε τ) (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) := by
    intro g
    unfold Formalism.REAL.inUJ
    calc (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)
        = ((M.fr τ)⁻¹)ᴴ * ((cmp θ τ g)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * cmp θ τ g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
          rw [M.fr_gram τ, hu g]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) := by
          rw [hB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hconj : Continuous fun g : GA D V => M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have hσ := (M.ds τ).2.2.1.2.2 (a τ)
  have hrep : Continuous fun g : GA D V => M.rep τ (cmp θ τ g) (a τ) :=
    hσ.comp_continuous hconj hmem
  exact continuous_const.inner hrep

end GlobalTheory.SepPer.CoefCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainRealParametersCorrespond
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreOntoPar
open GlobalTheory.SignedHC GlobalTheory.PairLift Finset

theorem mem_dualPar' {S : SPar} {x : ℚ × Bool} : x ∈ dualPar S ↔ (-x.1, x.2) ∈ S := by
  simp only [dualPar, mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, h, he⟩
    rw [← he]; simpa using h
  · intro h; exact ⟨_, _, h, by simp⟩

theorem mem_block_neg {c y : ℚ} {t : ℕ} : y ∈ TPar.block (-c) t ↔ -y ∈ TPar.block c t := by
  rw [mem_block, mem_block]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  · rintro ⟨a, ha, h⟩
    refine ⟨t - 1 - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith

theorem dual_partner (t : ℕ) (c : ℚ) (P : SPar) (hc : ∀ x ∈ P, x.1 ≠ c) :
    partner t true (-c) (-c) (dualPar P) = dualPar (GlobalTheory.SignedHC.flip (partner t false c c P)) := by
  ext ⟨y, b⟩
  rw [mem_dualPar', GlobalTheory.SignedHC.mem_flip]
  simp only [partner, mem_union, mem_image, Prod.exists, Prod.mk.injEq, mem_dualPar', sub_neg_eq_add,
    add_neg_cancel_right, sub_add_cancel]
  constructor
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, rfl, rfl⟩)
    · left
      refine ⟨-a, b', h, rfl, ?_⟩
      have hne : -a ≠ c := hc _ h
      by_cases h1 : a < -c
      · have h3 : ¬ (-a < c) := by linarith
        rw [if_pos h1] at h2; rw [if_neg h3]; subst h2; simp
      · have h3 : -a < c := lt_of_le_of_ne (by linarith) hne
        rw [if_neg h1] at h2; rw [if_pos h3]; subst h2; simp
    · right; exact ⟨-a, mem_block_neg.1 ha, rfl, rfl⟩
  · rintro (⟨a, b', h, rfl, h2⟩ | ⟨a, ha, ha', hb⟩)
    · left
      have hne : -y ≠ c := hc _ h
      refine ⟨y, b', h, rfl, ?_⟩
      by_cases h1 : y < -c
      · have h3 : ¬ (-y < c) := by linarith
        rw [if_neg h3] at h2; rw [if_pos h1]; subst h2; simp
      · have h3 : -y < c := lt_of_le_of_ne (by linarith) hne
        rw [if_pos h3] at h2; rw [if_neg h1]; exact Bool.not_inj h2
    · right
      subst ha'
      refine ⟨y, mem_block_neg.2 ha, rfl, ?_⟩
      cases b
      · exact absurd hb (by decide)
      · rfl

theorem parOK_core : ParOK := by
  intro D hS i hi τ
  show GlobalTheory.EvenOnto.UpPair (GlobalTheory.ChiGrid.sLen D - 1) ((GlobalTheory.ChiGrid.num D 1 τ).parPi i) ((GlobalTheory.ChiGrid.num D 1 τ).parPi (i + 1)) _ _
  set G := GlobalTheory.ChiGrid.num D 1 τ with hGdef
  set c : ℚ := (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) : ℚ) with hc
  have hN : G.NearMid := GlobalTheory.ChiGrid.num_nearMid D 1 τ
  have hgp := (GlobalTheory.ChiGrid.isLeast_gap D 1).1
  have hγ : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 + 2 * GlobalTheory.ChiGrid.sLen D + 2 < GlobalTheory.ChiGrid.gap D 1 := hgp.2.1
  have hr := hS.1
  have hsl : GlobalTheory.ChiGrid.sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ G.s := show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega
  have hq : G.s = 2 * (a + b + 2) + 1 := show GlobalTheory.ChiGrid.sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < GlobalTheory.ChiGrid.bigN D := by unfold GlobalTheory.ChiGrid.bigN; omega
  have hγq : (G.s : ℚ) + 4 ≤ G.ga := by
    show (GlobalTheory.ChiGrid.sLen D : ℚ) + 4 ≤ (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : GlobalTheory.ChiGrid.sLen D + 4 ≤ GlobalTheory.ChiGrid.gap D 1)
  have hγ2 : 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < G.ga := by
    show 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 < (GlobalTheory.ChiGrid.gap D 1 : ℚ)
    exact_mod_cast (by omega : 2 * GlobalTheory.ChiGrid.bigN D ^ 3 < GlobalTheory.ChiGrid.gap D 1)
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hsγ : (G.s : ℚ) ≤ G.ga := by linarith
  have hsq : (G.s : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) := rfl
  have hcastT : ((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ GlobalTheory.ChiGrid.sLen D by omega)]; simp
  have hfar : FarFrom c (((GlobalTheory.ChiGrid.sLen D : ℚ) + 2) / 2) (G.parPi i) :=
    GlobalTheory.ParPairArrows.far_parPi G hN hs1 hγq hi
  have hpart : partner (GlobalTheory.ChiGrid.sLen D - 1) false c c (G.parPi i) = GlobalTheory.SignedHC.flip (G.parPi (i + 1)) :=
    GlobalTheory.ParPairArrows.partner_parPi G hN hs1 hγq hi
  have hcne : ∀ x ∈ G.parPi i, x.1 ≠ c := fun x hx e => by
    have := hfar x.1 (fst_mem_entries hx)
    rw [e, sub_self, abs_zero] at this
    linarith
  have hflip : ∀ S : SPar, GlobalTheory.SignedHC.flip (GlobalTheory.SignedHC.flip S) = S := fun S => by
    ext ⟨x, s⟩; simp [mem_flip]
  have hP1 : partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i)) = dualPar (G.parPi (i + 1)) := by
    rw [dual_partner _ _ _ hcne, hpart, hflip]
  have hgapP : ∀ j, j ≤ D.R.m → GapOver (dualPar (G.parPi j)) (2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3) := by
    intro j hj x hx y hy hne
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hj _ hx _ hy hne
    have e : |(-x.1) - (-y.1)| = |x.1 - y.1| := by rw [show (-x.1) - (-y.1) = -(x.1 - y.1) by ring, abs_neg]
    rw [e] at this
    linarith
  have hne : (dualPar (G.parPi i)).Nonempty := by
    have h0 : (G.parPi i).Nonempty := ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
    exact h0.image _
  have hreg : IsRegular (dualPar (G.parPi i)) := by
    intro x hx y hy e
    by_contra hne'
    rw [mem_dualPar'] at hx hy
    have := GlobalTheory.ParPairArrows.gap_parPi G hN hs1 hsγ hi.le _ hx _ hy hne'
    rw [e, sub_self, abs_zero] at this
    linarith
  have hco : InCoset (-c + (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries (dualPar (G.parPi i))) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    obtain ⟨z, hz⟩ := GlobalTheory.ParPairArrows.inCoset_parPi G hq (GlobalTheory.ChiGrid.cen D 1 τ (D.R.m - i) - GlobalTheory.ChiGrid.sLen D) i (-x)
      (fst_mem_entries hs')
    have hcastG : ((G.s - 1 : ℕ) : ℚ) = (GlobalTheory.ChiGrid.sLen D : ℚ) - 1 := hcastT
    rw [hcastG] at hz
    push_cast at hz
    refine ⟨-z, ?_⟩
    rw [hcastT]; push_cast
    linarith
  have hfar' : FarFrom (-c) ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) + 1) / 2) (dualPar (G.parPi i)) := by
    intro x hx
    obtain ⟨s', hs'⟩ := mem_entries.1 hx
    rw [mem_dualPar'] at hs'
    simp only at hs'
    have := hfar _ (fst_mem_entries hs')
    simp only at this
    have e : |x - -c| = |-x - c| := by rw [show x - -c = -(-x - c) by ring, abs_neg]
    rw [hcastT, e]
    linarith
  have hcard : (dualPar (G.parPi i)).card + (GlobalTheory.ChiGrid.sLen D - 1) ≤ GlobalTheory.ChiGrid.bigN D := by
    have hc0 : (dualPar (G.parPi i)).card ≤ (G.parPi i).card := card_image_le
    have hc := GlobalTheory.ParPairArrows.card_parPi G i
    have h1 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) ≤ D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) := Nat.mul_le_mul_right _ hi
    have h2 : (i + 1) * (GlobalTheory.ChiGrid.sLen D - 1) = i * (GlobalTheory.ChiGrid.sLen D - 1) + (GlobalTheory.ChiGrid.sLen D - 1) := Nat.succ_mul _ _
    have h3 : D.R.m * (GlobalTheory.ChiGrid.sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (GlobalTheory.ChiGrid.sLen D - 1) at hc
    show _ ≤ D.R.k + D.R.m * (D.R.t + GlobalTheory.ChiGrid.sLen D + 1)
    omega
  have hth := GlobalTheory.PairLift.FromSigned.thetaPar_partner (GlobalTheory.ChiGrid.sLen D - 1) true (-c) (-c) (dualPar (G.parPi i))
    (GlobalTheory.ChiGrid.bigN D) (by omega) hne hreg hco hfar' hcard hN1 (hgapP i hi.le) (by rw [hP1]; exact hgapP (i + 1) hi)
  obtain ⟨al, be, ga, de, hPe, (⟨hD, hP'⟩ | ⟨_, hP'⟩)⟩ := hth
  · refine ⟨al, be, ga, de, hD, ?_, ?_, ?_⟩
    · intro e he
      have hmem : ∃ s, (e + -c, s) ∈ dualPar (G.parPi i) := by
        rw [hPe]
        simp only [List.mem_append] at he
        rcases he with ((h | h) | h) | h
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨true, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inl ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
        · exact ⟨false, GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [h]⟩)⟩
      obtain ⟨s, hs⟩ := hmem
      rw [mem_dualPar'] at hs
      simp only at hs
      have := hfar _ (fst_mem_entries hs)
      simp only at this
      have e1 : |-(e + -c) - c| = |e| := by rw [show -(e + -c) - c = -e by ring, abs_neg]
      rw [e1] at this
      rw [hcastT]
      linarith
    · rw [← hPe, dualPar_dualPar]
    · rw [← hP', hP1, dualPar_dualPar]
  · exfalso
    have hg := hgapP (i + 1) hi
    rw [← hP1, hP'] at hg
    have e0m : (((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 ∈ block (GlobalTheory.ChiGrid.sLen D - 1) :=
      GlobalTheory.PairLift.FromSigned.mem_blockList.2 ⟨0, by omega, by simp⟩
    have hf : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, false) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) :=
      GlobalTheory.Chain.ItPairCompare.mem_signed.2 (Or.inr ⟨rfl, by simp [e0m]⟩)
    have ht : ((((GlobalTheory.ChiGrid.sLen D - 1 : ℕ) : ℚ) - 1) / 2 + -c, true) ∈
        GlobalTheory.Chain.signed (al ++ de) (ga ++ block (GlobalTheory.ChiGrid.sLen D - 1) ++ be) (-c) := by
      rw [← hP']
      refine mem_union.2 (Or.inr (mem_image.2 ⟨_, mem_block.2 ⟨0, by omega, ?_⟩, rfl⟩))
      push_cast; ring
    have := hg _ ht _ hf (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (GlobalTheory.ChiGrid.bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.CoreOntoPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_testData_large_gaps_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  first | exact @GlobalTheory.DSGapData.dsData_gap_integrable | exact GlobalTheory.DSGapData.dsData_gap_integrable | (intros; apply GlobalTheory.DSGapData.dsData_gap_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addEquiv_symplecticCoords_orientedModel : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (c : D.host.E), c ≠ 0 →
    ∃ f : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      ∀ u, f u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (c • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords | exact GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords | (intros; apply GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords <;> assumption)
end

