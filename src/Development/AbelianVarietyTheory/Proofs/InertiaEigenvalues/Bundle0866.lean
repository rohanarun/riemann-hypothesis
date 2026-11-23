module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFrameIntAnyField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Formalism.LocalToGlobal.Columns.MtAdWt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
section
noncomputable section

open NumberField Matrix MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff
open GlobalTheory.RSTheta GlobalTheory.ShortVecDecay GlobalTheory.Petersson GlobalTheory.CuspQuot Topology GroundTheory.Automorphic.GJMatrix GlobalTheory.RSThetaLow

namespace GlobalTheory.RSThetaLowM

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mspanR_invT (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ GlobalTheory.JSW.mspanR π) :
    (fun g => F (invT a (Ad E) g)) ∈ GlobalTheory.JSW.mspanR π.contra :=
  _root_.GlobalTheory.JSW.invT_mem_mspanR_contra E a π F hF

def rsm (π : CuspSub E a) : Submodule ℂ (Sm E a) := (GlobalTheory.JSW.mspanR π).comap (Sm E a).subtype

theorem lie_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) (X : Lie E a) {F : Sm E a} (hF : F ∈ rsm π) :
    lie E a X F ∈ rsm π := by
  obtain ⟨ψ, hψ, hw, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF
  obtain rfl : ψ = F := Subtype.ext hψ
  simpa [GlobalTheory.GLFin.word, rsm] using hw [X]

theorem bounded_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    ∃ C : ℝ, ∀ g, ‖F.1 g‖ ≤ C :=
  (GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π hπ F.1 hF).choose_spec.2.2.2

theorem decays_invT_of_mem_rsm {π : CuspSub E a} (hπ : π.IsUnitary) {F : Sm E a} (hF : F ∈ rsm π) :
    Decays fun g => F.1 (invT a (Ad E) g) := by
  obtain ⟨ψ, hψ, -, -⟩ := GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded E a GlobalTheory.CuspOrth.cuspFormsBounded π.contra hπ.contra _ (mspanR_invT π hF)
  intro L hL C₀ hC₀ N
  obtain ⟨C, h⟩ := GlobalTheory.T.cuspFormSmoothSpan_norm_le_shortRationalVector E a π.contra hπ.contra ψ (Or.inr (hψ ▸ mspanR_invT π hF)) [] L hL C₀ hC₀ N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := h g c hc ξ hξ hm
  simpa [GlobalTheory.GLFin.word, hψ] using this

variable {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
variable {π π' : CuspSub E a} {φ φ' : Sm E a}

theorem exists_norm_rsHat_le_const (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) :
    ∃ C : ℝ, ∀ g y, ‖rsHat ℓ φ.1 φ'.1 Φ J η g y‖ ≤ C := by
  obtain ⟨C, h⟩ := exists_norm_rsHat_le J η (g := id) (w := fun _ => 1) (fun X _ => lie_mem_rsm hπ X)
    (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF _ _ => (bounded_of_mem_rsm hπ hF).imp fun C h _ _ _ => (h _).trans_eq (mul_one _).symm)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ 0
  exact ⟨C, fun g y => by simpa using h g y⟩

theorem exists_tsum_norm_rsHat_le (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hΦ : IsTest (rowSet E ℓ) Φ) (K : ℕ) : ∃ C : ℝ, ∀ g ∈ lowSet E a,
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖rsHat ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖ ≤
        C * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ K := by
  set N := K + Module.finrank ℝ (Fin a → Cinf E) with hN
  have had : 1 ≤ a * Module.finrank ℚ E := Nat.mul_pos ℓ.pos Module.finrank_pos
  obtain ⟨M, C₁, h₁⟩ := GlobalTheory.T.summable_nonzeroRationalVector_le_shortestVector E a (traceDualIdeal E J) (a * Module.finrank ℚ E * N)
    ((Nat.le_add_left _ K).trans (Nat.le_mul_of_pos_left _ had))
  obtain ⟨C₂, h₂⟩ := exists_norm_rsHat_le J η
    (ι := {p : GA E a × (Fin a → E) // p.2 ≠ 0 ∧
      (fun i => pFin E (((fun j => algebraMap E (Ad E) (p.2 j)) ᵥ* p.1.val) i)) ∈ latt a (traceDualIdeal E J)})
    (g := fun p => invT a (Ad E) p.1.1)
    (w := fun p => (‖fun i => pInf E (((fun j => algebraMap E (Ad E) (p.1.2 j)) ᵥ* p.1.1.val) i)‖ ^
      (a * Module.finrank ℚ E) / (ideleModule E (GeneralLinearGroup.det p.1.1) : ℝ)) ^ N)
    (fun X _ => lie_mem_rsm hπ X) (fun X _ => lie_mem_rsm hπ' X)
    (fun F hF C₀ hC₀ => (decays_invT_of_mem_rsm hπ hF _ (isCompact_latt _) _ (hC₀.image continuous_invT) N).imp
      fun C h p c hc => by simpa only [map_mul, invT_invT] using h p.1.1 _ ⟨c, hc, rfl⟩ p.1.2 p.2.1 p.2.2)
    (fun F hF => bounded_of_mem_rsm hπ' hF) hφ hφ' hΦ M
  refine ⟨|C₁| * |C₂|, fun g hg => ?_⟩
  set δ : ℝ := (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδ0 : 0 < δ := (ideleModule E _).2
  have h := (h₁ (invT a (Ad E) g) (|C₂| * δ ^ N)
    (fun ξ => rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)) (by positivity)
    (fun ξ hξ => by
      rw [rsHat_eq J η φ φ' hΦ]
      exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Set.indicator_of_notMem hξ _)) _)
    (fun ξ ξ' h0 hξ' => by
      have h3 := h₂ ⟨(invT a (Ad E) g, ξ'), h0, hξ'⟩ ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* (g⁻¹).valᵀ)
      simp only [invT_invT, absDet_invT, ← hδ, div_inv_eq_mul, mul_pow, ← pow_mul] at h3
      refine h3.trans ?_
      rw [mul_assoc |C₂|, mul_comm (δ ^ N)]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))).2
  refine h.trans ?_
  rw [mul_assoc]
  refine mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hδ0.le hg (Nat.le_add_right _ _)) (abs_nonneg _)) (by positivity) (abs_nonneg _)

variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}

theorem integrableOn_partA (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
    {s : ℂ} (hs : 1 < s.re) : IntegrableOn (fun g => rsHat ℓ φ.1 φ'.1 Φ J η g 0 *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ := by
  obtain ⟨C, hC⟩ := exists_norm_rsHat_le_const J η hπ hπ' hφ hφ' hΦ
  refine ((_root_.GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ℓ.pos μ 𝓕 h𝓕 (s.re - 1) (by linarith)).const_mul C).mono'
    ((stronglyMeasurable_rsHat J η hc hc' hΦ continuous_const).aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp GlobalTheory.RSThetaLow.continuous_absDet.measurable).pow_const _).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC g 0) (Real.rpow_nonneg (ideleModule E _).2.le _)

theorem partB_entire (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    (∀ s : ℂ, IntegrableOn (fun g => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1)) (𝓕 ∩ lowSet E a) μ) ∧
    Differentiable ℂ (partB ℓ φ.1 φ'.1 Φ J η μ 𝓕) := by
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hm : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, AEStronglyMeasurable (fun g : GA E a =>
      rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) (μ.restrict (𝓕 ∩ lowSet E a)) :=
    fun ξ => (stronglyMeasurable_rsHat J η hc hc' hΦ
      (continuous_const.matrix_vecMul Units.continuous_coe_inv.matrix_transpose)).aestronglyMeasurable
  have hlow : ∀ᵐ g ∂μ.restrict (𝓕 ∩ lowSet E a), g ∈ lowSet E a :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right
      (ae_restrict_mem (isClosed_le GlobalTheory.RSThetaLow.continuous_absDet continuous_const).measurableSet)
  have hδ := hlow.mono (q := fun g => 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧
    (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1) fun g hg => ⟨(ideleModule E _).2, hg⟩
  have hi := _root_.GlobalTheory.RSThetaLow.integrableOn_absDet_rpow_low E a ℓ.pos μ 𝓕 h𝓕 1 one_pos
  simp only [Real.rpow_one] at hi
  have hb := exists_tsum_norm_rsHat_le J η hπ hπ' hφ hφ' hΦ
  have h1 := _root_.GlobalTheory.integral_mul_cpow_of_rapid_decay_entire _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi (AEStronglyMeasurable.tsum hm) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg =>
      (norm_tsum_le_tsum_norm (poisson_rsPsi J η φ φ' hΦ g).2.1).trans (h g hg)
  have h2 := _root_.GlobalTheory.integral_mul_cpow_of_rapid_decay_entire _ _ _ _ GlobalTheory.RSThetaLow.continuous_absDet.measurable hδ hi
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (AEStronglyMeasurable.tsum fun ξ => (hm ξ).norm)) fun K =>
    (hb K).imp fun C h => hlow.mono fun g hg => by
      rw [Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
      exact h g hg
  refine ⟨fun x => ((h2.1 ((x - 1 : ℝ) : ℂ)).norm).congr (.of_forall fun g => ?_), fun s => h1.1 _,
    h1.2.comp (differentiable_id.sub_const 1)⟩
  simp only [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  rw [Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]

theorem integral_low_eq (hπ : π.IsUnitary) (hπ' : π'.IsUnitary) (hφ : φ ∈ rsm π)
    (hφ' : φ' ∈ rsm π') (hc : Continuous φ.1) (hc' : Continuous φ'.1) (hΦ : IsTest (rowSet E ℓ) Φ)
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun g => (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s) (𝓕 ∩ lowSet E a) μ ∧
    ∫ g in 𝓕 ∩ lowSet E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ =
      partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s + partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s := by
  have hA := integrableOn_partA J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕 hs
  have hB := (partB_entire J η hπ hπ' hφ hφ' hc hc' hΦ h𝓕).2.1 s
  have e : ∀ g : GA E a, (∑' ξ : Fin a → E, rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) *
      ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s =
      rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) +
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        rsHat ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) := fun g => by
    rw [(poisson_rsPsi J η φ φ' hΦ g).2.2, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 (ideleModule E _).2.ne'),
      Complex.cpow_one]
    ring
  simp only [e]
  exact ⟨hA.add hB, integral_add hA hB⟩

end GlobalTheory.RSThetaLowM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduce
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.GLift

theorem act_mul' {k : Type} [CommRing k] {n : ℕ} (g h : GL (Fin n) k) (Y : Gl n k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul]

theorem omega_lift {F : Type} [NontriviallyNormedField F] (r : ℕ) (Z : Gl r F) (μ l : F) :
    omega (GlobalTheory.JR.Step.lift Z μ l) = omega Z := by
  have h := (GlobalTheory.JR.transfer_factor_lemma F (r + 1)).1 (GlobalTheory.JR.Step.lift Z μ l)
  have hc : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = lastDet Z := rfl
  unfold omega eta
  rw [h, hc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem orbG_lift : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 →
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 →
    orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  intro F E _ _ _ _ hU r M M' Z μ l hμ hΔ
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨lc1, sc1⟩ := gl_lc_sc F (r + 1)
  letI := M.mG
  haveI := M.bG
  letI := M'.mG
  haveI := M'.bG
  haveI := M.haarG
  haveI := M'.haarG
  haveI := gl_unimodular F E (r + 1) M
  haveI := gl_unimodular F E r M'
  obtain ⟨hO, hC⟩ := _root_.GlobalTheory.JR.GLift.glO_isOpen_isCompact F (r + 1)
  have hemb := _root_.GlobalTheory.JR.Step.EmbClosed.isClosedEmbedding_emb F r
  have key := GlobalTheory.CosetIntegral.integral_eq_of_coset_support (GL (Fin (r + 1)) F) (GL (Fin r) F)
    (GlobalTheory.JR.Step.emb r F) hemb M.μG M'.μG (glOSub (r + 1) F) hO hC M.volG
    (by rw [coe_glOSub, _root_.GlobalTheory.JR.GLift.emb_preimage_glO F r]; exact M'.volG)
    (fun g => unitG (r + 1) F (act g (GlobalTheory.JR.Step.lift Z μ l)) * omega (act g (GlobalTheory.JR.Step.lift Z μ l)))
    (fun k hk g => by
      simp only [act_mul', _root_.GlobalTheory.JR.GLift.unitG_act F (r + 1) k hk, _root_.GlobalTheory.JR.omega_act_glO F (r + 1) k hk])
    (fun g hg => _root_.GlobalTheory.JR.GLift.support_lift F E r Z μ l hμ g (left_ne_zero_of_mul hg))
    ((_root_.GlobalTheory.JR.orbG_integrand_hasCompactSupport F (r + 1) _ hΔ).comp_isClosedEmbedding hemb)
  unfold orbG
  rw [key]
  simp only [_root_.GlobalTheory.JR.Step.ActEmbLift.act_emb_lift, _root_.GlobalTheory.JR.UnitGLift.unitG_lift F r _ μ l hμ.le, omega_lift, mul_assoc]
  exact integral_const_mul _ _

end GlobalTheory.JR.GLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedField
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

namespace GlobalTheory.HkAnyFieldOf

theorem heckeFrameInt_anyField_of : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  intro hHI E _ _ _ H Dw l Xo c la 𝔓 p i hP hpla T io e hla y hy Ω _ _ _ k yΩ hyΩ C z hz
  letI : Algebra c.F T.Fr := io.toAlgebra

  letI : Algebra T.Fr Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower c.F T.Fr Ω := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  let k₀ : T.Fr →ₐ[c.F] AlgebraicClosure T.Fr := IsScalarTower.toAlgHom c.F T.Fr (AlgebraicClosure T.Fr)
  let φ₀ : AlgebraicClosure T.Fr →ₐ[T.Fr] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let φ : AlgebraicClosure T.Fr →ₐ[c.F] Ω := φ₀.restrictScalars c.F
  have hφk : ∀ a, φ (k₀ a) = k a := fun a => φ₀.commutes a

  obtain ⟨yK, hyK⟩ := exists_frMap k₀ y.1
  have hKΩ : FrMap φ yK yΩ := frMap_of_comp hyK hyΩ hφk

  obtain ⟨C₀, z₀, hz₀, hz₀z⟩ := GlobalTheory.HkAnyField.exists_hkRelFr_down hP φ hKΩ C hz
  have halg : (letI := k₀.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr (AlgebraicClosure T.Fr)) := by
    have hA : k₀.toRingHom.toAlgebra = AlgebraicClosure.instAlgebra T.Fr :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact hA ▸ AlgebraicClosure.isAlgebraic T.Fr
  have h₀ := (hHI E H Dw l Xo c).2.1 la 𝔓 p i hP hpla T io e hla y hy trivial (AlgebraicClosure T.Fr) k₀ halg
    yK hyK C₀ z₀ hz₀

  have h₁ := GlobalTheory.HkAnyField.isIntegralUpToUnits_up φ hz₀z h₀
  have hcomp : φ.toRingHom.comp k₀.toRingHom = k.toRingHom := RingHom.ext hφk
  rwa [hcomp] at h₁

end GlobalTheory.HkAnyFieldOf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.WtDescent

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.CoefModel

theorem weight_descends : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] (e : K →+* ℂ) (emb : ι → L →+* K), Function.Injective (fun t => e.comp (emb t)) → (∀ t t', (fun t => e.comp (emb t)) t ≠ ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (fun t => e.comp (emb t)) t ∨ σ = ComplexEmbedding.conjugate ((fun t => e.comp (emb t)) t)) → ∀ (c : L →+* L), (∀ x, c x = IsCMField.complexConj L x) → ∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K (ReciprocityTheory.Aut.GQ L n) W), ρ.IsIrreducible → ∀ lam0 : ι → Fin n → ℤ, (∀ t, NX.HWAtF c ρ.dual (emb t) (lam0 t)) → ∃ lam : ι → DomWeight n, (∀ t, (lam t).w = lam0 t) ∧ ∃ T : W ≃ₗ[K] VV K lam, ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  intro L _ _ _ n ι _ K _ e emb hinj hcm hcov c hc W _ _ _ ρ hρ lam0 hw
  classical
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := L) (M := ℂ)).toRingHom⟩
  obtain ⟨t₀, -⟩ := hcov σ
  let N := Module.finrank K W
  let b : Module.Basis (Fin N) K W := Module.finBasis K W
  let A : ReciprocityTheory.Aut.GQ L n → Matrix (Fin N) (Fin N) K := fun γ => LinearMap.toMatrix b b (ρ γ)
  let ρC : Representation ℂ (ReciprocityTheory.Aut.GQ L n) (Fin N → ℂ) :=
    ((Matrix.toLinAlgEquiv' : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin N → ℂ)) :
        Matrix (Fin N) (Fin N) ℂ →* Module.End ℂ (Fin N → ℂ)).comp
      (((e.mapMatrix : Matrix (Fin N) (Fin N) K →+* Matrix (Fin N) (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) K →* Matrix (Fin N) (Fin N) ℂ).comp
        (((LinearMap.toMatrixAlgEquiv b : Module.End K W ≃ₐ[K] Matrix (Fin N) (Fin N) K) :
          Module.End K W →* Matrix (Fin N) (Fin N) K).comp ρ))
  have hρC : ∀ γ, LinearMap.toMatrix' (ρC γ) = (LinearMap.toMatrix b b (ρ γ)).map e := by
    intro γ
    show LinearMap.toMatrix' (Matrix.toLin' ((LinearMap.toMatrix b b (ρ γ)).map e)) = _
    rw [LinearMap.toMatrix'_toLin']
  have halg : Formalism.AUTREP.IsAlgWeight L n ρC :=
    _root_.GlobalTheory.AlgWtDualRead.isAlgWeight_of_hwAtF_dual L n K e c hc W ρ (Fin N) b ρC hρC (emb t₀) (lam0 t₀) (hw t₀)
  haveI : Nontrivial W := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible ρ hρ
  have hN : 0 < N := Module.finrank_pos
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, j, hj, hjρ⟩ := _root_.GlobalTheory.AlgSubrep.exists_irreducible_algWt L n (Fin N → ℂ) ρC halg
  obtain ⟨lam, Tc, hTc⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists L n ι (fun t => e.comp (emb t)) hinj hcm hcov a
  have hmatch : ∀ γ : ReciprocityTheory.Aut.GQ L n, (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
      Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
      ((mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
    intro γ
    exact (congrArg (fun g : GL (Fin n) (ReciprocityTheory.Aut.AL L) => (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)))
      (mtwInc_mtwRatFun γ)).symm
  let bK := bVV K lam
  let bC : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (linearIndependent_mapVV e lam) (span_mapVV e lam).ge
  have hbC : ∀ i, bC i = mapVV e lam (bK i) := fun i => Module.Basis.mk_apply _ _ _
  have hrepr : ∀ x i, bC.repr (mapVV e lam x) i = e (bK.repr x i) := by
    intro x i
    have hx : mapVV e lam x = bC.equivFun.symm (fun i => e (bK.repr x i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← bK.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smulₛₗ, hbC]
    rw [hx, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  let B : ReciprocityTheory.Aut.GQ L n → Matrix (VVIdx lam) (VVIdx lam) K :=
    fun γ => LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ))
  have hB : ∀ γ, LinearMap.toMatrix bC bC (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ)) = (B γ).map e := by
    intro γ
    ext i k
    rw [LinearMap.toMatrix_apply, Matrix.map_apply]
    show _ = e (LinearMap.toMatrix bK bK (rhoVr emb lam (mtwRat (L := L) (n := n) γ)) i k)
    rw [LinearMap.toMatrix_apply, hbC, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hrepr]
  let M : VV ℂ lam →ₗ[ℂ] (Fin N → ℂ) := j ∘ₗ Tc.symm.toLinearMap
  have hM : ∀ γ y, M (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = ρC γ (M y) := by
    intro γ y
    have h1 : Tc.symm (rhoVr (fun t => e.comp (emb t)) lam (mtwRat (L := L) (n := n) γ) y) = a.ρ γ (Tc.symm y) := by
      apply Tc.injective
      rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [M, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, hjρ]
  let X : Matrix (Fin N) (VVIdx lam) ℂ := LinearMap.toMatrix bC (Pi.basisFun ℂ (Fin N)) M
  have hX0 : X ≠ 0 := by
    intro h
    have hM0 : M = 0 := by
      have := congrArg (Matrix.toLin bC (Pi.basisFun ℂ (Fin N))) h
      simpa [X] using this
    haveI := GlobalTheory.PiIsotypic.nontrivial_of_isIrreducible a.ρ a.irr
    obtain ⟨x, hx⟩ := exists_ne (0 : a.W)
    apply hx
    apply hj
    have : M (Tc x) = j x := by simp [M]
    rw [← this, hM0, LinearMap.zero_apply, map_zero]
  have hXrel : ∀ γ, X * (B γ).map e = (A γ).map e * X := by
    intro γ
    rw [← hB, show (A γ).map e = LinearMap.toMatrix' (ρC γ) from (hρC γ).symm,
      ← LinearMap.toMatrix_eq_toMatrix', ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext fun y => hM γ y
  obtain ⟨XK, hXK0, hXK⟩ := _root_.GlobalTheory.matrix_intertwiner_descends K e (ReciprocityTheory.Aut.GQ L n) (VVIdx lam) (Fin N) B A ⟨X, hX0, hXrel⟩
  let Φ : VV K lam →ₗ[K] W := Matrix.toLin bK b XK
  have hΦ : ∀ γ x, Φ (rhoVr emb lam (mtwRat (L := L) (n := n) γ) x) = ρ γ (Φ x) := by
    intro γ x
    have h : Φ ∘ₗ rhoVr emb lam (mtwRat (L := L) (n := n) γ) = ρ γ ∘ₗ Φ := by
      apply (LinearMap.toMatrix bK b).injective
      rw [LinearMap.toMatrix_comp bK bK b, LinearMap.toMatrix_comp bK b b, LinearMap.toMatrix_toLin]
      exact hXK γ
    exact LinearMap.congr_fun h x
  have hsurj : Function.Surjective Φ := by
    let S : Subrepresentation ρ := ⟨LinearMap.range Φ, by
      rintro γ _ ⟨x, rfl⟩
      exact ⟨_, hΦ γ x⟩⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exfalso
      apply hXK0
      have hr : LinearMap.range Φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      have hΦ0 : Φ = 0 := LinearMap.range_eq_bot.1 hr
      have := congrArg (LinearMap.toMatrix bK b) hΦ0
      simpa [Φ] using this
    · have hr : LinearMap.range Φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  haveI : FiniteDimensional K (VV K lam) := Module.Finite.of_basis bK
  have hdimC : Module.finrank ℂ a.W ≤ N := by
    have := LinearMap.finrank_le_finrank_of_injective hj
    simpa using this
  have hdimA : Module.finrank ℂ a.W = Fintype.card (VVIdx lam) := by
    rw [Tc.finrank_eq, Module.finrank_eq_card_basis bC]
  have hdimK : Module.finrank K (VV K lam) = Fintype.card (VVIdx lam) := Module.finrank_eq_card_basis bK
  have hle : N ≤ Module.finrank K (VV K lam) := by
    have := LinearMap.finrank_range_le Φ
    rwa [LinearMap.range_eq_top.2 hsurj, finrank_top] at this
  have heq : Module.finrank K (VV K lam) = Module.finrank K W := by
    show Module.finrank K (VV K lam) = N
    omega
  have hinjΦ : Function.Injective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).2 hsurj
  let Φb : VV K lam ≃ₗ[K] W := LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩
  have h1 : ∀ y, Φb y = Φ y := fun y => rfl
  have hT : ∀ γ x, Φb.symm (ρ γ x) = rhoVr emb lam (mtwRat (L := L) (n := n) γ) (Φb.symm x) := by
    intro γ x
    apply Φb.injective
    rw [Φb.apply_symm_apply, h1, hΦ, ← h1, Φb.apply_symm_apply]
  have hten : Formalism.L2.Col.TenIrr (fun t => e.comp (emb t)) lam := by
    refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv a.ρ _ Tc (fun γ v => ?_) a.irr
    rw [hTc γ (mtwRat (L := L) (n := n) γ) (hmatch γ)]
    rfl
  refine ⟨lam, fun t => (GlobalTheory.mtRatDual_hw L n ι K e emb hinj hcm c hc lam hten W ρ Φb.symm hT t (lam0 t) (hw t)).symm,
    Φb.symm, fun γ γ₀ hm x => ?_⟩
  obtain rfl := mtwRat_eq_of_match γ γ₀ hm
  exact hT γ x

end GlobalTheory.WtDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  first | exact @GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | exact GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | (intros; apply GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge <;> assumption)
end

