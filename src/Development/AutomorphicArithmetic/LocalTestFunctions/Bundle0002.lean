module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.IntegratedRightRegularEqLocalOperator
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.integrated_rightRegular_eq_localOperator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure]
          (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw ψ T →
          (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
            (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) = T := by
  intro K _ _ n μ _ w _ _ mw _ ψ T h
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [UnitaryRep.inner_integrated, h u v]
  refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 mw ψ).mono fun g hg => ?_)
  have hr : (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
      (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1) g = rhoL μ w g := by
    simp only [UnitaryRep.compHom_apply]
    rfl
  simp only [hr]
  exact congrArg (· * ⟪u, rhoL μ w g v⟫_ℂ) hg
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.LocalOperatorCommuteRhoFOfTrivialAtPlace
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.localOperator_commute_rhoF_of_trivial_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] (mw : Measure (Gw n w)) (φ : Gw n w → ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw φ T →
          ∀ h : AdelicGLn.FiniteAdelicGL K n, finAt w (finEmb K n h) = 1 → Commute T (rhoF μ h) := by
  intro K _ _ n μ _ w _ mw φ T hT h hh
  obtain ⟨-, -, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.2 h hh
  have hcomm : ∀ (g : Gw n w) (v : LL μ), rhoL μ w g (rhoF μ h v) = rhoF μ h (rhoL μ w g v) := by
    intro g v
    have e : rhoF μ (AdelicGLn.localEmbedding w g * h) = rhoF μ (h * AdelicGLn.localEmbedding w g) := by
      rw [hc g]
    rw [hmul, hmul] at e
    exact congrArg (fun S : LL μ →L[ℂ] LL μ => S v) e
  have key : ∀ u v : LL μ, ⟪u, T (rhoF μ h v)⟫_ℂ = ⟪u, rhoF μ h (T v)⟫_ℂ := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_left (rhoF μ h) (T v) u, hT u, hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show φ g * ⟪u, rhoL μ w g (rhoF μ h v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint (rhoF μ h) u, rhoL μ w g v⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_left, hcomm]
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  exact key u v
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.LocalOperatorCompRhoLEqOfRightInvariant
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem map_right_eq_of_CO {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsHaarMeasure] {J : Subgroup G} (hJ : CO J) {k : G} (hk : k ∈ J) :
    Measure.map (· * k) m = m := by
  have hcont : Measurable (· * k : G → G) := (continuous_mul_const k).measurable
  haveI : (Measure.map (· * k) m).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right m k
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * k) m) m
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have hpre : (· * k : G → G) ⁻¹' (J : Set G) = J := by
    ext x
    exact Subgroup.mul_mem_cancel_right J hk
  have h0 : m (J : Set G) ≠ 0 := (hJ.2.measure_pos m ⟨1, J.one_mem⟩).ne'
  have hT : m (J : Set G) ≠ ⊤ := hJ.1.measure_lt_top.ne
  have e := congrArg (fun ν : Measure G => ν (J : Set G)) h
  simp only [Measure.map_apply hcont hmeas, hpre, Measure.smul_apply] at e
  have hc : Measure.haarScalarFactor (Measure.map (· * k) m) m = 1 := by
    have e' : m (J : Set G) = (Measure.haarScalarFactor (Measure.map (· * k) m) m : ENNReal) * m (J : Set G) := by
      simpa [ENNReal.smul_def] using e
    have : ((Measure.haarScalarFactor (Measure.map (· * k) m) m : NNReal) : ENNReal) = 1 :=
      ((ENNReal.mul_eq_right h0 hT).1 e'.symm)
    exact_mod_cast this
  rw [h, hc, one_smul]

theorem UpperTheory.localOperator_comp_rhoL_eq_of_right_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (φ : Gw n w → ℂ), (∀ k ∈ J, ∀ x, φ (x * k) = φ x) → ∀ T : LL μ →L[ℂ] LL μ, IsOloc μ w mw φ T →
          ∀ k ∈ J, T ∘L rhoL μ w k = T := by
  intro K _ _ n μ _ w _ _ mw _ J hJ φ hφ T hT k hk
  have hmul : ∀ (g : Gw n w) (v : LL μ), rhoL μ w (g * k) v = rhoL μ w g (rhoL μ w k v) := by
    intro g v
    simp only [rhoL, rhoF, map_mul]
    exact UnitaryRep.map_mul_apply _ _ _ v
  have hmp : MeasurePreserving (· * k : Gw n w → Gw n w) mw mw :=
    ⟨(continuous_mul_const k).measurable, map_right_eq_of_CO mw hJ hk⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.comp_apply, hT u, hT u v,
    ← hmp.integral_comp (Homeomorph.mulRight k).measurableEmbedding
      (fun g => φ g * ⟪u, rhoL μ w g v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hφ k hk, hmul]
end

