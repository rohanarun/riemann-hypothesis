module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdNormOne
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0009
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.GalTwistFinProjEqOfGalAdFinEmbEq
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem galAd_adeleMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (a : NumberField.AdeleRing (𝓞 F) F) :
    galAd σ (AdeleBaseChange.adeleMap F E a) = AdeleBaseChange.adeleMap F E a := by
  change AdeleBaseChange.adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
    ((AdeleBaseChange.adeleTensorEquiv F E).symm (AdeleBaseChange.adeleMap F E a))) = _
  rw [AdeleBaseChange.adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul,
    AdeleBaseChange.adeleTensorEquiv_tmul, map_one, map_one, one_mul]
  rfl

private theorem exists_pow_eq (d : ℕ) (hd : d ≠ 0) (t : {r : ℝ // 0 < r}) :
    ∃ s : {r : ℝ // 0 < r}, s ^ d = t := by
  refine ⟨rpowHom ((d : ℝ))⁻¹ t, Subtype.ext ?_⟩
  change ((t : ℝ) ^ ((d : ℝ))⁻¹) ^ d = t
  exact Real.rpow_inv_natCast_pow t.2.le hd

private theorem map_centralSection {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (n : ℕ) (t : {r : ℝ // 0 < r}) :
    (mapGL n (galAd σ) (centralSection E n t) : AdelicGLn.AdelicGL E n) = centralSection E n t := by
  obtain ⟨s, rfl⟩ := exists_pow_eq (Module.finrank F E) Module.finrank_pos.ne' t
  have h := UpperTheory.centralSection_baseChange F E n s
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact galAd_adeleMap σ _

theorem UpperTheory.galTwist_finProj_eq_of_galAd_finEmb_eq :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
          ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ h h' : AdelicGLn.FiniteAdelicGL E n,
            (mapGL n (galAd σ) (finEmb E n h) : AdelicGLn.AdelicGL E n) = finEmb E n h' →
            θ.e (MultiplicityOne.finProj E n h) = MultiplicityOne.finProj E n h' := by
  intro F E _ _ _ _ _ _ σ n hn μ _ θ hθ h h' hh
  refine Subtype.ext ?_
  rw [hθ, MultiplicityOne.coe_finProj, MultiplicityOne.coe_finProj, map_mul, map_inv, hh, map_centralSection]
  set s := detModule E n (finEmb E n h) with hs
  have hmem : finEmb E n h' * (centralSection E n s)⁻¹ ∈ normOneGL (K := E) (n := n) := by
    have h1 := (θ.e (MultiplicityOne.finProj E n h)).2
    rw [hθ, MultiplicityOne.coe_finProj, map_mul, map_inv, hh, map_centralSection] at h1
    exact h1
  have hd : detModule E n (finEmb E n h') = s := by
    have h2 := (mem_normOneGL_iff_detModule).1 hmem
    rw [map_mul, map_inv, detModule_centralSection hn] at h2
    exact mul_inv_eq_one.1 h2
  rw [hd]
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.LevFIsOpenIsCompactLeIntegral
section
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

theorem UpperTheory.levF_isOpen_isCompact_le_integral :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (lev : ∀ v : Pl K, Subgroup (GL (Fin n) (v.adicCompletion K))) (S : Finset (Pl K)),
      (∀ v ∈ S, IsOpen (lev v : Set (GL (Fin n) (v.adicCompletion K))) ∧ lev v ≤ GLnLocal.integralGL (v.adicCompletion K) n) →
      (∀ v, v ∉ S → lev v = GLnLocal.integralGL (v.adicCompletion K) n) →
      IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
        levF lev ≤ AdelicGLn.integralFiniteGL K n ∧
        ∀ (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), J ≤ lev w → J.map (AdelicGLn.localEmbedding w) ≤ levF lev := by
  classical
  intro K _ _ n lev S hS hS'
  have hmem : ∀ h : AdelicGLn.FiniteAdelicGL K n,
      h ∈ levF lev ↔ ∀ v, AdelicGLn.finiteRestrictedEquiv K n h v ∈ lev v := fun h => Iff.rfl
  have hint : levF lev ≤ AdelicGLn.integralFiniteGL K n := by
    intro h hh
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    intro v
    have hv := (hmem h).1 hh v
    by_cases hvS : v ∈ S
    · exact (hS v hvS).2 hv
    · rwa [hS' v hvS] at hv
  have hev : ∀ v : Pl K, Continuous fun h : AdelicGLn.FiniteAdelicGL K n =>
      (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K)) := fun v =>
    (_root_.RestrictedProduct.continuous_eval v).comp (AdelicGLn.finiteRestrictedEquiv K n).continuous
  have hVo : IsOpen ((AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
      ⋂ v ∈ S, (fun h : AdelicGLn.FiniteAdelicGL K n =>
        (AdelicGLn.finiteRestrictedEquiv K n h v : GL (Fin n) (v.adicCompletion K))) ⁻¹'
          (lev v : Set (GL (Fin n) (v.adicCompletion K)))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).inter
      (isOpen_biInter_finset fun v hv => (hS v hv).1.preimage (hev v))
  have hopen : IsOpen (levF lev : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    refine Subgroup.isOpen_of_mem_nhds (levF lev) (g := 1) ?_
    refine Filter.mem_of_superset (hVo.mem_nhds ?_) ?_
    · refine ⟨one_mem _, ?_⟩
      simp only [Set.mem_iInter]
      intro v _
      exact (levF lev).one_mem v
    · rintro h ⟨h1, h2⟩
      simp only [Set.mem_iInter] at h2
      refine (hmem h).2 fun v => ?_
      by_cases hvS : v ∈ S
      · exact h2 v hvS
      · rw [hS' v hvS]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 h1 v
  refine ⟨hopen, ?_, hint, ?_⟩
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ hopen) hint
  · rintro w J hJ _ ⟨x, hx, rfl⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1
    have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.1
    intro v
    by_cases hv : v = w
    · subst hv
      rw [h1]
      exact hJ hx
    · rw [h2 v hv]
      exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.RhoFCompOfinOfLeftInvariant
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem comp_integrated_of_left_inv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (u : G) (f : CompactlySupportedContinuousMap G ℂ) (hf : ∀ x, f (u * x) = f x) :
    π u ∘L π.integrated μ (UnitaryRep.ccToL1 μ f) = π.integrated μ (UnitaryRep.ccToL1 μ f) := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, UnitaryRep.inner_map_right, CuspidalProjection.inner_integrated_ccToL1,
    CuspidalProjection.inner_integrated_ccToL1, ← integral_mul_left_eq_self (μ := μ) _ u⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have h : f (u⁻¹ * x) = f x := by rw [← hf (u⁻¹ * x), mul_inv_cancel_left]
  rw [h, UnitaryRep.inner_map_left, inv_inv, UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply π u,
    mul_inv_cancel, UnitaryRep.map_one_apply]

theorem UpperTheory.rhoF_comp_Ofin_of_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (e : TF K n) (u : AdelicGLn.FiniteAdelicGL K n), (∀ x, e (u * x) = e x) → rhoF μ u ∘L Ofin μ m e = Ofin μ m e := by
  intro K _ _ n μ _ m _ e u hu
  exact comp_integrated_of_left_inv m ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n)
    MultiplicityOne.continuous_finProj) u e hu
end

