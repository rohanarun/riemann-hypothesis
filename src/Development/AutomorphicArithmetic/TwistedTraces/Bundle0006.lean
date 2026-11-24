module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0004
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0002
public import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsSmoothArchCutoffKbarEqOne
section
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem frob_diag {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) (e : 𝕜) (r : ℝ)
    (he : ‖e‖ = r) : frobSq (M * Matrix.diagonal fun _ => e) = r ^ 2 * frobSq M := by
  simp only [frobSq, Matrix.mul_diagonal, norm_mul, mul_pow, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

private noncomputable def lam (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : ℝ :=
  ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s : {r : ℝ // 0 < r}) : ℝ)

private theorem lam_pos (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : 0 < lam K n s :=
  (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s).2

private theorem infAt_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r})
    (w : InfinitePlace K) : ∃ u : w.Completion, ‖u‖ = lam K n s ∧ ∀ a b : Fin n,
      Reduction.infAt w (infEmb K n (zInf K n s)) a b = if a = b then u else 0 := by
  refine ⟨(GroundTheory.Global.IdeleGroup.infiniteProj w (posIdele (K := K) (lam K n s) (lam_pos K n s)) : (w.Completion)ˣ), ?_, fun a b => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj]
    exact norm_posIdele_infinite _ _ w
  · have e : centralSection K n s = diagUnits n fun _ => posIdele (K := K) (lam K n s) (lam_pos K n s) := rfl
    rw [infEmb_zInf, e, infAt_diagUnits, coe_diagUnits, Matrix.diagonal_apply]

private theorem quad_mul_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (A : ArchMatrix K n)
    (s : {r : ℝ // 0 < r}) : archQuad (A * archVal (zInf K n s)) = lam K n s ^ 2 * archQuad A := by
  have hr : ∀ v : {w : InfinitePlace K // InfinitePlace.IsReal w}, ∃ e : ℝ, ‖e‖ = lam K n s ∧
      realCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm] at h1
      simp only [realCompM_apply, Matrix.map_apply, realComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  have hc : ∀ v : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ∃ e : ℂ, ‖e‖ = lam K n s ∧
      complexCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbedding w u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbedding w) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbedding_symm _ hw] at h1
      simp only [complexCompM_apply, Matrix.map_apply, complexComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  simp only [archQuad, mul_add, Finset.mul_sum, map_mul]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hr v
    rw [hv, frob_diag _ e _ he]
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hc v
    rw [hv, frob_diag _ e _ he]

private theorem quad_ne (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) :
    archQuad (archVal a) ≠ 0 := by
  intro h
  have h0 := archQuad_eq_zero h
  have h1 : archVal a * archVal a⁻¹ = 1 := by
    rw [archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [h0, zero_mul] at h1
  have h2 : (0 : mixedEmbedding.mixedSpace K) = 1 := by
    have h3 := congrFun (congrFun (congrArg mat h1) ⟨0, hn⟩) ⟨0, hn⟩
    rw [mat_zero, mat_one, Matrix.one_apply_eq] at h3
    exact h3
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  by_cases hw : InfinitePlace.IsReal w
  · have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨w, hw⟩) h2
    exact zero_ne_one (α := ℝ) h3
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨w, hw'⟩) h2
    exact zero_ne_one (α := ℂ) h3

private theorem lam_exp (K : Type) [Field K] [NumberField K] (n : ℕ) (t : ℝ) :
    lam K n (GroundTheory.Global.expPos t) = Real.exp (t * (n * Module.finrank ℚ K : ℝ)⁻¹) := by
  change (Real.exp t) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹ = _
  rw [← Real.exp_mul]

private noncomputable def lq (K : Type) [Field K] [NumberField K] (n : ℕ) (a : archGroup K n) : ℝ :=
  Real.log (archQuad (archVal a))

private theorem lq_mul (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) (t : ℝ) :
    lq K n (a * zInf K n (GroundTheory.Global.expPos t)) = lq K n a + 2 * (n * Module.finrank ℚ K : ℝ)⁻¹ * t := by
  have e : archVal (a * zInf K n (GroundTheory.Global.expPos t)) = archVal a * archVal (zInf K n (GroundTheory.Global.expPos t)) := rfl
  rw [lq, e, quad_mul_zInf, lam_exp, Real.log_mul (by positivity) (quad_ne K n hn a), Real.log_pow, Real.log_exp, lq]
  push_cast
  ring

private theorem continuous_lq (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    Continuous (lq K n) :=
  Continuous.log ((contDiff_archQuad (K := K) (n := n)).continuous.comp continuous_archVal) (quad_ne K n hn)

theorem UpperTheory.exists_smooth_archCutoff_kbar_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∃ χ : archGroup K n → ℝ, (isExpLieAlgebra K n).IsSmoothFun (fun A => (χ A : ℂ)) ∧
          (∀ A, kbar (fun g => (χ g : ℂ)) A = 1) ∧
          ∀ C : Set (G1 K n), IsCompact C → ∃ D : Set (archGroup K n), IsCompact D ∧
            ∀ A, χ A ≠ 0 → archP K n A ∈ C → A ∈ D := by
  intro K _ _ n hn
  set d : ℝ := (n * Module.finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h3 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 this
    positivity
  set β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hβ
  set h : ℝ → ℝ := β.normed volume with hh
  set c : ℝ := 2 * d⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨fun A => c * h (lq K n A), ?_, fun A => ?_, fun C hC => ?_⟩
  · rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    have e : (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        Real.log (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n))) := by
      funext Y
      simp only [lq, archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    have hl : ContDiff ℝ ∞ (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) := by
      rw [e]
      refine ContDiff.log (hq.comp (contDiff_const.mul (hexp.comp hY))) fun Y => ?_
      have := quad_ne K n hn (g * (isExpLieAlgebra K n).expG Y)
      simpa only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG] using this
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (β.contDiff_normed.comp hl))
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    rw [kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos, hemb.integral_map]
    have e1 : ∀ t : ℝ, ((c * h (lq K n (A * zInf K n (GroundTheory.Global.expPos t))) : ℝ) : ℂ) =
        ((c * h (lq K n A + c * t) : ℝ) : ℂ) := fun t => by
      rw [lq_mul K n hn]
    simp only [e1]
    rw [integral_complex_ofReal, integral_const_mul]
    have e2 : ∫ t, h (lq K n A + c * t) = |c⁻¹| • ∫ y, h (lq K n A + y) :=
      Measure.integral_comp_mul_left (fun y => h (lq K n A + y)) c
    rw [e2, integral_add_left_eq_self h (lq K n A), hh, β.integral_normed, abs_of_pos (inv_pos.2 hc0),
      smul_eq_mul, mul_one, mul_inv_cancel₀ hc0.ne']
    simp
  · set C' : Set (archGroup K n) := (fun x : G1 K n => infPart K n (x : AdelicGLn.AdelicGL K n)) '' C with hC'
    have hC'c : IsCompact C' := hC.image (continuous_infPart.comp continuous_subtype_val)
    obtain ⟨M, hM⟩ := hC'c.exists_bound_of_continuousOn (continuous_lq K n hn).continuousOn
    set R : ℝ := (2 + M) / c with hR
    refine ⟨(fun p : archGroup K n × ℝ => p.1 * zInf K n (GroundTheory.Global.expPos p.2)) '' (C' ×ˢ Set.Icc (-R) R),
      (hC'c.prod isCompact_Icc).image
        (continuous_fst.mul (continuous_zInf.comp (GroundTheory.Global.expPosHomeomorph.continuous.comp continuous_snd))),
      fun A hA hAC => ?_⟩
    set r := detA K n A with hr
    set a := infPart K n (archP K n A : AdelicGLn.AdelicGL K n) with ha
    have haC : a ∈ C' := ⟨_, hAC, rfl⟩
    have hr' : GroundTheory.Global.expPos (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
    have hAa : A = a * zInf K n (GroundTheory.Global.expPos (Real.log r)) := by
      rw [hr', ha, infPart_archP, inv_mul_cancel_right]
    have hsup : lq K n A ∈ Metric.ball (0 : ℝ) 2 := by
      have h1 : h (lq K n A) ≠ 0 := right_ne_zero_of_mul hA
      have h2 : lq K n A ∈ Function.support h := h1
      rw [hh, β.support_normed_eq] at h2
      exact h2
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hsup
    have hl := lq_mul K n hn a (Real.log r)
    rw [← hAa] at hl
    have hMa := hM a haC
    rw [Real.norm_eq_abs] at hMa
    have hct : |c * Real.log r| ≤ 2 + M := by
      have e3 : c * Real.log r = lq K n A - lq K n a := by rw [hl, hc, hd]; ring
      rw [e3]
      exact (abs_sub _ _).trans (by linarith)
    have ht : |Real.log r| ≤ R := by
      rw [hR, le_div_iff₀ hc0]
      rwa [abs_mul, abs_of_pos hc0, mul_comm] at hct
    exact ⟨(a, Real.log r), ⟨haC, abs_le.1 ht⟩, hAa.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalCuspFormsOfLevelAndDerivOpBound
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

set_option maxHeartbeats 20000000 in
theorem UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (C : ℝ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (S : Submodule ℂ (cuspForms K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → S ≤ centralCuspForms K n → (∀ φ ∈ S, ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.integralFiniteGL K n) φ = φ) → (∀ φ ∈ S, ∀ i, ‖cuspVecL μ ((gkModuleCusp K n).ρ (b i) φ)‖ ≤ C * ‖cuspVecL μ φ‖) → FiniteDimensional ℂ S := by
  intro K _ _ n μ _ d b C U S hU hS hfix hbound
  obtain ⟨N, hN, hNv⟩ := UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound _ _ _ (isExpLieAlgebra K n) d b C
  obtain ⟨N', hN', hN'd⟩ := UpperTheory.exists_nhds_one_normOneGL_factorization K n N U hN hU
  have hApprox := UpperTheory.exists_approximate_identity_integrated
    (normOneGL (K := K) (n := n)) (CuspL2 μ) (cuspRepT μ) μ N' hN'
  obtain ⟨f, hf⟩ := hApprox
  have key : ∀ v ∈ S.map (cuspVecL μ),
      ‖(cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ 1 / 2 * ‖v‖ := by
    rintro _ ⟨φ, hφ, rfl⟩
    apply hf (cuspVecL μ φ) (1 / 2 * ‖cuspVecL μ φ‖)
    intro g hg
    obtain ⟨a, ha, u, hu, rfl⟩ := hN'd g hg
    have hφ' : φ ∈ centralCuspForms K n := hS hφ
    have hfx : cuspRepT μ (retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n))) (cuspVecL μ φ) =
        cuspVecL μ φ := by
      rw [← cuspToL2_finRepCusp μ _ hφ', hfix φ hφ u hu]
    rw [(cuspRepT μ).map_mul_apply, hfx, ← archRepT_apply]
    refine hNv (CuspL2 μ) (archRepT μ) (cuspVecL μ φ) (fun g w => ?_)
      (isSmoothVector_cuspToL2 μ hφ') (fun i => ?_) a ha
    · rw [archRepT_apply]
      exact UnitaryRep.norm_map _ _ _
    · rw [derivOp_cuspVecL μ hφ']
      exact hbound φ hφ i
  haveI : FiniteDimensional ℂ (S.map (cuspVecL μ)) :=
    UpperTheory.finiteDimensional_of_compact_near_identity (CuspL2 μ) _ (S.map (cuspVecL μ)) (isCompactOperator_cuspRep μ f) key
  exact UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map (cuspVecL μ)) (cuspVecL μ)
    (fun x hx => Submodule.mem_map_of_mem hx)
    (fun x hx h => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hS hx) h)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.NormDerivOrbitLeOfPolynomialAnnihilated
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : ℝ → H →L[ℂ] H) (p : ℝ → ℂ[X]) (M : ℝ) (v y : H), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => u t v)) → HasDerivAt (fun t : ℝ => u t v) y 0 → (∀ t, aeval (u t) (p t) v = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ‖y‖ ≤ M * ‖v‖ := by
  intro H _ _ u p M v y h0 hadd hiso hfin hy hp hM
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v) := ⟨_, rfl⟩
  rw [← hE] at hfin
  haveI : FiniteDimensional ℂ E := hfin
  have hcomm : ∀ s t x, u s (u t x) = u t (u s x) := by
    intro s t x
    have h : u s * u t = u t * u s := by rw [← hadd, ← hadd, add_comm]
    exact DFunLike.congr_fun h x
  have h0' : ∀ a, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hstab : ∀ s, ∀ x ∈ E, u s x ∈ E := by
    intro s x hx
    rw [hE] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨s + t, by simp [hadd]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hvE : v ∈ E := by
    rw [hE]
    exact Submodule.subset_span ⟨0, h0' v⟩
  have hclosed : IsClosed (E : Set H) := Submodule.closed_of_finiteDimensional E
  have hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E := by
    intro w hw d hd
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    refine hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))
  have hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 →
      HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0 := by
    intro s w d hd
    let LR : H →L[ℝ] H := (u s).restrictScalars ℝ
    have h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 hd
    have h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w) := by
      funext t
      exact hcomm s t w
    rw [h2] at h1
    exact h1
  have hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0 := by
    intro w hw
    rw [hE] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨u s y, hsh s v y hy⟩
    | zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨da, hda⟩ := ha
      obtain ⟨db, hdb⟩ := hb
      refine ⟨da + db, ?_⟩
      convert hda.add hdb using 1
      funext t
      simp
    | smul c a _ ha =>
      obtain ⟨da, hda⟩ := ha
      refine ⟨c • da, ?_⟩
      convert hda.const_smul c using 1
      funext t
      simp
  have hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0 := by
    intro w
    obtain ⟨d, hd⟩ := hder w w.2
    rw [hd.deriv]
    exact hd
  let D : Module.End ℂ E :=
    { toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        refine (hd (a + b)).unique ?_
        convert (hd a).add (hd b) using 1
        · funext t
          simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine (hd (c • a)).unique ?_
        convert (hd a).const_smul c using 1
        · funext t
          simp
      }
  let u' : ℝ → Module.End ℂ E := fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)
  have hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H) := fun t x => rfl
  have hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0 := fun x => rfl
  have haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H) := by
    intro t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']
  have hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x) := by
    intro s t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]
  have hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0 := by
    intro t x hx
    rw [hE] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      show aeval (u t) (p t) (u s v) = 0
      rw [hcq, hp, map_zero]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0 := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hasDerivAt_iff_tendsto_slope.1 (hd x)
    rw [tendsto_subtype_rng]
    refine h.congr fun t => ?_
    simp [slope_def_module, hu']
  have hbound := UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M
    (by
      ext x
      simp [hu', h0'])
    (by
      intro s t
      ext x
      simp [hu', hadd])
    (by
      intro t x
      exact hiso t x)
    hder'
    (by
      intro t
      ext x
      rw [haev]
      simpa using hkill t x x.2)
    hM ⟨v, hvE⟩
  have hDv : ((D ⟨v, hvE⟩ : E) : H) = y := by
    rw [hD]
    exact hy.deriv
  have hn : ‖D ⟨v, hvE⟩‖ = ‖y‖ := by
    rw [← hDv]
    rfl
  rw [hn] at hbound
  exact hbound
end

