module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0022
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0024
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0019
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0015
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0016
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0021
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0017
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0023
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralTsumIdeleCoveringEqConstMul
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem gen {T U P Y Q : Type*} [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace P] [MeasurableSpace Y]
    [MeasurableSpace Q] [Countable Q] [MeasurableSingletonClass Q]
    (τ : Measure T) (υ : Measure U) (ν : Measure P) (μ : Measure Y) [SFinite τ] [SFinite υ] [SFinite ν] [SFinite μ]
    (f : T → U → P → Q → Y) (hf : Measurable fun x : T × U × P × Q => f x.1 x.2.1 x.2.2.1 x.2.2.2) (c : ℝ≥0)
    (hc : ∀ p, ∀ h : Y → ℝ≥0∞, Measurable h → ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α) ∂υ ∂τ = c * ∫⁻ y, h y ∂μ)
    (H : Y × P → ℂ) (hH : Measurable H) (hI : Integrable H (μ.prod ν)) :
    (∀ᵐ t ∂τ, ∀ᵐ u ∂υ, ∀ᵐ p ∂ν, Summable fun α => H (f t u p α, p)) ∧
      ∫ t, ∫ u, ∫ p, ∑' α, H (f t u p α, p) ∂ν ∂υ ∂τ = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
  let Ψ : T × U × P × Q → Y × P := fun x => (f x.1 x.2.1 x.2.2.1 x.2.2.2, x.2.2.1)
  have hΨ : Measurable Ψ := hf.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd))
  let m : Measure (T × U × P × Q) := τ.prod (υ.prod (ν.prod Measure.count))
  have hmap : m.map Ψ = c • μ.prod ν := by
    refine Measure.ext_of_lintegral _ fun h hh => ?_
    have hΨh : Measurable fun x => h (Ψ x) := hh.comp hΨ
    have hG : Measurable fun x : T × U × P => ∑' α, h (f x.1 x.2.1 x.2.2 α, x.2.2) :=
      Measurable.tsum fun α => hΨh.comp (f := fun x : T × U × P => (x.1, x.2.1, x.2.2, α)) (by fun_prop)
    rw [lintegral_map hh hΨ, lintegral_smul_measure, lintegral_prod _ hΨh.aemeasurable, lintegral_prod_symm _ hh.aemeasurable]
    have e1 : ∀ t, ∫⁻ y, h (Ψ (t, y)) ∂(υ.prod (ν.prod Measure.count)) =
        ∫⁻ p, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂ν := by
      intro t
      have a1 : Measurable fun y : U × P × Q => h (Ψ (t, y)) := hΨh.comp measurable_prodMk_left
      have a2 : Measurable (Function.uncurry fun (u : U) (p : P) => ∑' α, h (f t u p α, p)) :=
        hG.comp (measurable_prodMk_left (x := t))
      rw [lintegral_prod _ a1.aemeasurable, ← lintegral_lintegral_swap a2.aemeasurable]
      refine lintegral_congr fun u => ?_
      have a3 : Measurable fun y : P × Q => h (Ψ (t, u, y)) := a1.comp measurable_prodMk_left
      rw [lintegral_prod _ a3.aemeasurable]
      refine lintegral_congr fun p => ?_
      rw [lintegral_count]
    simp only [e1]
    have hG2 : Measurable fun x : T × P => ∫⁻ u, ∑' α, h (f x.1 u x.2 α, x.2) ∂υ :=
      Measurable.lintegral_prod_right' (f := fun x : (T × P) × U => ∑' α, h (f x.1.1 x.2 x.1.2 α, x.1.2))
        (hG.comp (f := fun x : (T × P) × U => (x.1.1, x.2, x.1.2)) (by fun_prop))
    rw [lintegral_lintegral_swap hG2.aemeasurable]
    have e2 : ∀ p, ∫⁻ t, ∫⁻ u, ∑' α, h (f t u p α, p) ∂υ ∂τ = c * ∫⁻ y, h (y, p) ∂μ :=
      fun p => hc p (fun y => h (y, p)) (hh.comp measurable_prodMk_right)
    simp only [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    rfl
  have hI1 : Integrable H (m.map Ψ) := by
    rw [hmap]
    exact hI.smul_measure ENNReal.coe_ne_top
  have hI2 : Integrable (fun x => H (Ψ x)) m := (integrable_map_measure hH.aestronglyMeasurable hΨ.aemeasurable).1 hI1
  have hval : ∫ x, H (Ψ x) ∂m = (c : ℂ) * ∫ q, H q ∂(μ.prod ν) := by
    rw [← integral_map hΨ.aemeasurable hH.aestronglyMeasurable, hmap, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  constructor
  · filter_upwards [hI2.prod_right_ae] with t ht
    filter_upwards [ht.prod_right_ae] with u hu
    filter_upwards [hu.prod_right_ae] with p hp
    exact (integrable_count_iff.1 hp).of_norm
  · rw [← hval, integral_prod _ hI2]
    refine integral_congr_ae ?_
    filter_upwards [hI2.prod_right_ae] with t ht
    rw [integral_prod _ ht]
    refine integral_congr_ae ?_
    filter_upwards [ht.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae ?_
    filter_upwards [hu.prod_right_ae] with p hp
    rw [integral_countable hp]
    simp [Ψ]

theorem UpperTheory.integral_tsum_ideleCovering_eq_const_mul :
    ∀ (U : UMeas) (c : ℝ≥0), (∀ h : IdeleGroup ℚ → ℝ≥0∞, Measurable h →
          ∫⁻ t : ℝ, ∫⁻ u, ∑' α : ℚˣ, h (Un.cov t u α) ∂U.υ = c * ∫⁻ y, h y ∂(ideleMeasure ℚ)) →
        ∀ (κ : Measure (G1 ℚ)) [IsProbabilityMeasure κ] (H : IdeleGroup ℚ × IdeleGroup ℚ × G1 ℚ → ℂ), Measurable H →
        Integrable H ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) →
        (∀ᵐ t : ℝ, ∀ᵐ u ∂U.υ, ∀ᵐ p ∂((ideleMeasure ℚ).prod κ), Summable fun α : ℚˣ => H (Un.cov t u α * (p.1 * p.1)⁻¹, p)) ∧
        ∫ t : ℝ, ∫ u, ∫ p, ∑' α : ℚˣ, H (Un.cov t u α * (p.1 * p.1)⁻¹, p) ∂((ideleMeasure ℚ).prod κ) ∂U.υ =
          (c : ℂ) * ∫ q, H q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod κ)) := by
  intro U c hc κ _ H hH hI
  haveI := U.prob
  letI : MeasurableSpace ℚˣ := ⊤
  haveI : MeasurableSingletonClass ℚˣ := ⟨fun _ => trivial⟩
  haveI : Countable ℚˣ := Units.val_injective.countable
  have hiy : Measurable (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := by
    have h : Continuous (fun t : ℝ => (iy (Real.exp t) : IdeleGroup ℚ)) := UpperTheory.realIdele_mul_abs_continuous_and_unit_abs_eq_one.2.2.1
    exact h.measurable
  have hd : Measurable (fun α : ℚˣ => (IdeleGroup.diagonal ℚ α : IdeleGroup ℚ)) := measurable_from_top
  refine gen volume U.υ ((ideleMeasure ℚ).prod κ) (ideleMeasure ℚ)
    (fun t u p α => Un.cov t u α * (p.1 * p.1)⁻¹) ?_ c ?_ H hH hI
  · have h1 : Measurable fun x : ℝ × IdeleGroup ℚ × (IdeleGroup ℚ × G1 ℚ) × ℚˣ => x.2.2.1.1 := by fun_prop
    exact (((hd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul
      ((hiy.comp measurable_fst).mul (hiy.comp measurable_fst))).mul (measurable_fst.comp measurable_snd)).mul (h1.mul h1).inv
  · intro p h hh
    rw [hc (fun y => h (y * (p.1 * p.1)⁻¹)) (hh.comp (measurable_mul_const _)), lintegral_mul_right_eq_self]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffLieDerivUnipotentEqMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), Pp.Lf f.1 →
        (∀ X, Continuous (lie E 2 X f).1 ∧ ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B) → ∀ (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)),
        Wo D (lie E 2 (toL (XB D k)) f).1 (em E (aE y) * k) = (2 * Real.pi * Complex.I * (re (y : A ℚ) : ℂ)) * Wo D f.1 (em E (aE y) * k) := by
  intro E _ _ _ D f hf hl y k
  obtain ⟨c0, cadd, cd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have h1 := UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) (toL (XB D k)) (em E (aE y) * k) c0 cadd cd hf.1 (hl _).1 (hl _).2
  have e : (fun t : ℝ => Wo D f.1 (em E (aE y) * k * infGL E 2 (cv D k t))) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t : ℂ) * (re (y : A ℚ) : ℂ))) * Wo D f.1 (em E (aE y) * k) := by
    funext t
    rw [UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hf]
    have e1 : (![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] : Fin 2 → A ℚ) 1 = TR.sInf ℚ fun _ => t * re (y : A ℚ) := rfl
    rw [e1, UpperTheory.standardAddChar_neg_archimedean_rat]
    push_cast
    rfl
  rw [e] at h1
  have a : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 := (((a.mul_const (re (y : A ℚ) : ℂ)).const_mul (2 * Real.pi * Complex.I)).cexp).mul_const
    (Wo D f.1 (em E (aE y) * k))
  have h3 := h1.unique h2
  rw [h3]
  simp
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffNeZeroFiniteAdeleMemCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittakerCoeff_ne_zero_finiteAdele_mem_compact :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f → Pp.Lf f.1 →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ K : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact K ∧
          ∀ (y : (A ℚ)ˣ), ∀ k ∈ C, Wo D f.1 (em E (aE y) * k) ≠ 0 → (y : A ℚ).2 ∈ K := by
  intro E _ _ _ D f hf hL C hC
  obtain ⟨N, hN, hfN⟩ := UpperTheory.exists_level_unipotent_invariance_automorphicForm E D f hf C hC
  obtain ⟨K, hK, hKN⟩ := UpperTheory.exists_isCompact_annihilator_scaled_integralAdeles N hN
  refine ⟨K, hK, fun y k hk hW => hKN _ fun b hb => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : A ℚ, x = ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ) := ⟨_, rfl⟩
  have h1 : Wo D f.1 (em E (aE y) * k) = Wo D f.1 (em E (aE y) * gl (nU (D.mkE 0 x)) * k) := by
    have pt : ∀ G, f.1 (G * (em E (aE y) * k)) = f.1 (G * (em E (aE y) * gl (nU (D.mkE 0 x)) * k)) := by
      intro G
      have h := hfN k hk b hb (G * em E (aE y))
      rw [← hx] at h
      simp only [mul_assoc] at h ⊢
      exact h.symm
    simp only [Wo]
    congr 1
    funext u
    rw [pt]
  rw [UpperTheory.embedGL2_diag_mul_unipotent_theta_eq, mul_assoc, UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D f.1 hL] at h1
  have h2 : ψ (-((y : A ℚ) * x)) = 1 := by
    have h3 : ψ (-((y : A ℚ) * x)) * Wo D f.1 (em E (aE y) * k) = 1 * Wo D f.1 (em E (aE y) * k) := by
      rw [one_mul]
      exact h1.symm
    exact mul_right_cancel₀ hW h3
  have h4 : ψ ((y : A ℚ) * x) = 1 := by
    have h5 := Pp.ψ_add ((y : A ℚ) * x) (-((y : A ℚ) * x))
    have h6 : ψ (0 : A ℚ) = 1 := by
      have := Pp.ψ_rt (0 : ℚ)
      simpa using this
    rw [add_neg_cancel, h6, h2, mul_one] at h5
    exact h5.symm
  have h7 : (y : A ℚ) * x = ((0, (y : A ℚ).2 * ((N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b)) : A ℚ) := by
    rw [hx]
    exact Prod.ext (mul_zero _) rfl
  rw [← h7]
  exact h4
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem compact_cover_fundamental_domain : ∃ C : Set (Fin 2 → A ℚ), IsCompact C ∧ FS2 ℚ ⊆ C := by
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  exact ⟨Set.univ.pi fun _ : Fin 2 => C, isCompact_univ_pi fun _ => hC, Set.pi_mono fun _ _ => hs⟩

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

theorem UpperTheory.whittakerFunction_continuous_bounded_equivariant :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Continuous (Wo D φ) ∧ (∃ B : ℝ, ∀ h, ‖Wo D φ h‖ ≤ B) ∧
        (∀ (u : Fin 2 → A ℚ) h, Wo D φ (nE D u * h) = ψ (-(u 1)) * Wo D φ h) ∧
        (∀ z h, Wo D φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * Wo D φ h) := by
  intro E _ _ D ω φ hφ
  obtain ⟨B, hB⟩ := hφ.bdd
  refine ⟨?_, ⟨B, fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.2 φ B h hB⟩,
    fun u h => UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul E D φ ⟨hφ.cont, hφ.left⟩ u h, fun z h => ?_⟩
  · obtain ⟨C, hC, hs⟩ := compact_cover_fundamental_domain
    have e : Wo D φ = fun h => ∫ u in C, φ (nE D u * h) * ψ (u 1) ∂((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := by
      funext h
      rw [Measure.restrict_restrict hC.measurableSet, Set.inter_eq_right.2 hs]
      rfl
    rw [e]
    haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) :=
      ⟨by simpa using (measure_mono hs).trans_lt hC.measure_lt_top⟩
    set_option synthInstance.maxHeartbeats 200000 in
    exact continuous_parametric_integral_of_continuous
      ((hφ.cont.comp (((cont_nE D).comp continuous_snd).mul continuous_fst)).mul
        (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp ((continuous_apply 1).comp continuous_snd))) hC
  · unfold Wo
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only []
    rw [← mul_assoc, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, mul_assoc, hφ.cen, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerLintegralAbsPowBoundedOnMaximalCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_lintegral_abs_pow_bounded_on_maximalCompact :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : ℝ, 1 < x → ∃ C : ℝ≥0, ∀ k ∈ KK ℚ,
        ∫⁻ y : IdeleGroup ℚ, ‖Wo D φ (em E (aE y * gl k))‖ₑ * ENNReal.ofReal (ab y ^ x) ∂(ideleMeasure ℚ) ≤ C := by
  intro E _ _ D ω φ hA x hx
  have hemc : Continuous (em E) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id AdeleBaseChange.continuous_adeleMap)
  have hglc : Continuous (gl : G1 ℚ → GL (Fin 2) (A ℚ)) := Matrix.SpecialLinearGroup.continuous_toGL
  have hC : IsCompact ((fun k : G1 ℚ => em E (gl k)) '' KK ℚ) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt ℚ).2.image (hemc.comp hglc)
  obtain ⟨K, hKc, hK⟩ := hA.wdec _ hC
  obtain ⟨r, hr⟩ := exists_nat_gt x
  obtain ⟨B, hB⟩ := hK r
  have hI := UpperTheory.lintegral_idele_rat_polyDecay_mul_norm_rpow_lt_top K hKc x hx r hr
  refine ⟨(ENNReal.ofReal |B| * ∫⁻ y : IdeleGroup ℚ, (if (y : A ℚ).2 ∈ K then ENNReal.ofReal (((1 + |re (y : A ℚ)|) ^ r)⁻¹ * ab y ^ x) else 0) ∂(ideleMeasure ℚ)).toNNReal, fun k hk => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  have hb := hB y (em E (gl k)) ⟨k, hk, rfl⟩
  rw [← map_mul] at hb
  have hab : 0 ≤ ab y ^ x := Real.rpow_nonneg (IdeleGroup.ideleModule ℚ y).2.le x
  by_cases hy : (y : A ℚ).2 ∈ K
  · rw [if_pos hy, ← ENNReal.ofReal_mul (abs_nonneg _), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right (hb.1.trans ?_) hab
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · have h0 : Wo D φ (em E (aE y * gl k)) = 0 := by
      by_contra h
      exact hy (hb.2 h)
    rw [h0, enorm_zero, zero_mul]
    exact bot_le
end

