module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.CompProjFixedLevelEqOfLocalInvariance
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem level_decomp (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (r : ℕ) (w : Fin r → Pl K) (hw : Function.Injective w) (J : ∀ i, Subgroup (Gw n (w i)))
    (A : LL μ →L[ℂ] LL μ) (hA : ∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A)
    (g : AdelicGLn.FiniteAdelicGL K n) (hg : ∀ i, finAt (w i) (finEmb K n g) ∈ J i) (S : Finset (Fin r)) :
    ∃ a : AdelicGLn.FiniteAdelicGL K n, A ∘L rhoF μ a = A ∧
      (∀ i ∈ S, finAt (w i) (finEmb K n a) = finAt (w i) (finEmb K n g)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), (∀ i ∈ S, v ≠ w i) → finAt v (finEmb K n a) = 1 := by
  classical
  obtain ⟨-, -, -, -, -, hmul, hone, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
  have emul : ∀ (u : HeightOneSpectrum (𝓞 K)) (y z : AdelicGLn.FiniteAdelicGL K n),
      finAt u (finEmb K n (y * z)) = finAt u (finEmb K n y) * finAt u (finEmb K n z) := by
    intro u y z
    rw [e, e, e, map_mul, RestrictedProduct.mul_apply]
  have eone : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n 1) = 1 := by
    intro u
    rw [e, map_one, RestrictedProduct.one_apply]
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, ?_, by simp, fun v _ => eone v⟩
    rw [hone]
    exact ContinuousLinearMap.comp_id A
  | insert i S hi ih =>
    obtain ⟨a, h1, h2, h3⟩ := ih
    obtain ⟨-, l2, l3, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)
    refine ⟨a * AdelicGLn.localEmbedding (w i) (finAt (w i) (finEmb K n g)), ?_, ?_, ?_⟩
    · rw [hmul, ← ContinuousLinearMap.comp_assoc, h1]
      exact hA i _ (hg i)
    · intro j hj
      rw [emul]
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rw [l2, h3 _ (fun k hk e => hi (by rw [hw e]; exact hk)), one_mul]
      · have hne : w j ≠ w i := fun e => hi (hw e ▸ hj)
        rw [l3 _ hne, mul_one, h2 j hj]
    · intro v hv
      rw [emul, h3 v (fun j hj => hv j (Finset.mem_insert_of_mem hj)),
        l3 v (hv i (Finset.mem_insert_self _ _)), one_mul]

theorem UpperTheory.comp_proj_fixed_level_eq_of_local_invariance :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
          (r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (J : ∀ i, Subgroup (Gw n (w i))) (U US : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
          IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) →
          (∀ h, h ∈ US ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1) →
          ∀ A : LL μ →L[ℂ] LL μ, (∀ i, ∀ k ∈ J i, A ∘L rhoL μ (w i) k = A) → A ∘L prj (fixF μ U) = A ∘L prj (fixF μ US) := by
  intro K _ _ n μ _ m _ r w hw J U US hUo hUc hU hUS A hA
  obtain ⟨-, hmemU, -, -, -, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  obtain ⟨-, hmemS, b1, -, -, -, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ US
  have hle : fixF μ U ≤ fixF μ US := fun v hv => (hmemS v).2 fun u hu =>
    (hmemU v).1 hv u ((hU u).2 ⟨((hUS u).1 hu).1, fun i => by
      rw [((hUS u).1 hu).2 i]
      exact (J i).one_mem⟩)
  have hPQ : prj (fixF μ U) ∘L prj (fixF μ US) = prj (fixF μ U) := by
    unfold prj
    exact Submodule.starProjection_comp_starProjection_of_le (Submodule.topologicalClosure_mono hle)
  have hpt : ∀ g ∈ U, ∀ x ∈ fixF μ US, A (rhoF μ g x) = A x := by
    intro g hg x hx
    obtain ⟨hgi, hgJ⟩ := (hU g).1 hg
    obtain ⟨a, h1, h2, h3⟩ := level_decomp K n μ r w hw J A hA g hgJ Finset.univ
    have e : ∀ (u : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
        finAt u (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y u := fun _ _ => rfl
    have ec : ∀ u : HeightOneSpectrum (𝓞 K), finAt u (finEmb K n (a⁻¹ * g)) =
        (finAt u (finEmb K n a))⁻¹ * finAt u (finEmb K n g) := by
      intro u
      rw [e, e, e, map_mul, map_inv]
      rfl
    have hcomp : ∀ i, finAt (w i) (finEmb K n (a⁻¹ * g)) = 1 := by
      intro i
      rw [ec, h2 i (Finset.mem_univ i), inv_mul_cancel]
    have hb : a⁻¹ * g ∈ US := by
      refine (hUS _).2 ⟨(AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, hcomp⟩
      rw [← e]
      by_cases hv : ∃ i, v = w i
      · obtain ⟨i, rfl⟩ := hv
        rw [hcomp i]
        exact one_mem _
      · rw [ec, h3 v (fun i _ h => hv ⟨i, h⟩), inv_one, one_mul, e]
        exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hgi v
    have hga : rhoF μ g x = rhoF μ a x := by
      have hg' : g = a * (a⁻¹ * g) := (mul_inv_cancel_left a g).symm
      rw [hg', hmul, ContinuousLinearMap.comp_apply, (hmemS x).1 hx _ hb]
    rw [hga, ← ContinuousLinearMap.comp_apply, h1]
  have hcl : ∀ x ∈ fixF μ US, A (prj (fixF μ U) x) = A x := by
    intro x hx
    obtain ⟨e, he, hOe⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m U hUo hUc
    have hpos : (m.real U : ℝ) ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_lt_top.ne⟩
    have hO : Ofin μ m e x = ∫ h, e h • rhoF μ h x ∂m := by
      unfold Ofin
      rw [UnitaryRep.integrated_ccToL1_apply]
      rfl
    have hint : Integrable (fun h => e h • rhoF μ h x) m :=
      (e.continuous.smul (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).continuous_orbit x).comp
        MultiplicityOne.continuous_finProj)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right
    rw [← hOe, hO, ← ContinuousLinearMap.integral_comp_comm _ hint]
    have h2 : (fun h => A (e h • rhoF μ h x)) = fun h => e h • A x := by
      funext h
      rw [map_smul, he]
      by_cases hh : h ∈ U
      · rw [hpt h hh x hx]
      · rw [Set.indicator_of_notMem (show h ∉ (U : Set _) from hh), zero_smul, zero_smul]
    rw [h2, integral_smul_const]
    simp only [he]
    rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
  refine ContinuousLinearMap.ext fun v => ?_
  have hPv : prj (fixF μ U) v = prj (fixF μ U) (prj (fixF μ US) v) := by
    rw [← ContinuousLinearMap.comp_apply, hPQ]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hPv, hcl _ (b1 v)]
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.ExistsCompactOpenBiinvariantOfTest
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_compactOpen_biinvariant_of_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (φ : Gw n w → ℂ), Test φ →
          ∃ J : Subgroup (Gw n w), CO J ∧ J ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ ∀ k ∈ J, ∀ x, φ (k * x) = φ x ∧ φ (x * k) = φ x := by
  intro K _ _ n w φ hφ
  obtain ⟨U, hU, hf⟩ := GlobalTheory.Orb.exists_biinvariant (G := Gw n w) (f := φ) ⟨hφ.1, hφ.2⟩
  refine ⟨U ⊓ GLnLocal.integralGL (w.adicCompletion K) n, ⟨?_, ?_⟩, inf_le_right,
    fun k hk x => hf k hk.1 x⟩
  · rw [Subgroup.coe_inf]
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion K) n).inter_left
      (U.isClosed_of_isOpen hU)
  · rw [Subgroup.coe_inf]
    exact hU.inter (GLnLocal.isOpen_integralGL (w.adicCompletion K) n)
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.ExistsOpenCompactLevelSubgroup
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_open_compact_level_subgroup :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))), (∀ i, CO (J i)) →
          ∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) ∧
            IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  intro K _ _ n r w J hJ
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun i => ?_⟩
        rw [map_mul, finAt_mul]
        exact mul_mem (ha' i) (hb' i)
      one_mem' := by
        refine ⟨one_mem _, fun i => ?_⟩
        rw [map_one, finAt_one]
        exact one_mem _
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun i => ?_⟩
        have h1 : finAt (w i) (finEmb K n a⁻¹) * finAt (w i) (finEmb K n a) = 1 := by
          rw [← finAt_mul, ← map_mul, inv_mul_cancel, map_one, finAt_one]
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (ha' i) }
  have hmem : ∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i :=
    fun h => Iff.rfl
  have hset : (U : Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ i, (fun h => finAt (w i) (finEmb K n h)) ⁻¹' (J i : Set (Gw n (w i))) := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact hmem h
  have hopen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [hset]
    refine (AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_iInter_of_finite fun i => ?_)
    exact (hJ i).2.preimage ((continuous_finAt (w i)).comp continuous_finEmb)
  refine ⟨U, hmem, hopen, ?_⟩
  exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen U hopen) fun _ h => h.1
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.ExistsTestFunctionIntegralLocalFactor
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_testFunction_integral_local_factor :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ), (∀ k ∈ J, ∀ x, ψ (x * k) = ψ x) →
          ∀ (R : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ y x, R (AdelicGLn.localEmbedding w y * x) = R x) →
          ∀ e₀ : TF K n, (∀ x, e₀ x = R x * (J : Set (Gw n w)).indicator 1 (finAt w (finEmb K n x))) →
          ∃ g : TF K n, (∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x)))) ∧
            (∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m) ∧
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (AdelicGLn.FiniteAdelicGL K n) H),
              π.integrated m (UnitaryRep.ccToL1 m g) =
                (π.compHom (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) ∘L
                  π.integrated m (UnitaryRep.ccToL1 m e₀) := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro K _ _ n m _ w _ _ mw _ J hJ ψ hψ R hR e₀ he₀
    have hp := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
    obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv _ _ (AdelicGLn.localEmbedding w) hp m mw ψ e₀
    have hJm : MeasurableSet (J : Set (Gw n w)) := hJ.2.measurableSet
    have hval : ∀ x, g x = (mw.real J : ℂ) * (R x * ψ (finAt w (finEmb K n x))) := by
      intro x
      set a := finAt w (finEmb K n x) with ha
      have hfa : ∀ y, finAt w (finEmb K n ((AdelicGLn.localEmbedding w y)⁻¹ * x)) = y⁻¹ * a := by
        intro y
        rw [map_mul, finAt_mul, map_inv, finAt_inv, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]
      have hRy : ∀ y, R ((AdelicGLn.localEmbedding w y)⁻¹ * x) = R x := by
        intro y
        rw [← map_inv, hR]
      have hpt : ∀ y, ψ (a * y) * e₀ ((AdelicGLn.localEmbedding w (a * y))⁻¹ * x) =
          (J : Set (Gw n w)).indicator (fun _ => R x * ψ a) y := by
        intro y
        rw [he₀, hRy, hfa]
        have e1 : (a * y)⁻¹ * a = y⁻¹ := by group
        rw [e1]
        by_cases hy : y ∈ J
        · have hy' : y⁻¹ ∈ J := J.inv_mem hy
          rw [Set.indicator_of_mem (show y⁻¹ ∈ (J : Set (Gw n w)) from hy'),
            Set.indicator_of_mem (show y ∈ (J : Set (Gw n w)) from hy), hψ y hy, Pi.one_apply]
          ring
        · have hy' : y⁻¹ ∉ J := fun h => hy (by simpa using J.inv_mem h)
          rw [Set.indicator_of_notMem (show y⁻¹ ∉ (J : Set (Gw n w)) from hy'),
            Set.indicator_of_notMem (show y ∉ (J : Set (Gw n w)) from hy)]
          ring
      rw [hg, ← integral_mul_left_eq_self _ a]
      simp only [hpt]
      rw [integral_indicator hJm, setIntegral_const]
      simp [Measure.real, mul_comm]
    have hint : ∫ x, g x ∂m = (∫ y, ψ y ∂mw) * ∫ x, e₀ x ∂m := by
      have hf : IsCompact (tsupport ψ) := ψ.hasCompactSupport.isCompact
      have hS : IsCompact ((AdelicGLn.localEmbedding w) '' tsupport ψ * tsupport e₀) :=
        (hf.image hp).mul e₀.hasCompactSupport.isCompact
      have hker : Continuous fun q : AdelicGLn.FiniteAdelicGL K n × Gw n w =>
          ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) :=
        (ψ.continuous.comp continuous_snd).mul
          (e₀.continuous.comp ((hp.comp continuous_snd).inv.mul continuous_fst))
      have hI : Integrable (Function.uncurry fun (x : AdelicGLn.FiniteAdelicGL K n) (y : Gw n w) =>
          ψ y * e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x)) (m.prod mw) := by
        refine Continuous.integrable_of_hasCompactSupport hker ?_
        refine HasCompactSupport.intro (hS.prod hf) fun q hq => ?_
        change ψ q.2 * e₀ ((AdelicGLn.localEmbedding w q.2)⁻¹ * q.1) = 0
        by_contra hne
        obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
        exact hq ⟨⟨_, ⟨q.2, subset_tsupport _ h1, rfl⟩, _, subset_tsupport _ h2,
          mul_inv_cancel_left _ _⟩, subset_tsupport _ h1⟩
      simp only [hg]
      rw [integral_integral_swap hI]
      simp only [integral_const_mul]
      have hinv : ∀ y : Gw n w, ∫ x, e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) ∂m = ∫ x, e₀ x ∂m :=
        fun y => integral_mul_left_eq_self (fun x => e₀ x) _
      simp only [hinv]
      rw [integral_mul_const]
    exact ⟨g, hval, hint, hop⟩
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.FinprodLocalEqIndicatorMulProd
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.finprod_local_eq_indicator_mul_prod :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K), Function.Injective w → ∀ (f : ∀ v : Pl K, Gw n v → ℂ),
          (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) → ∀ x : AdelicGLn.FiniteAdelicGL K n,
          ∏ᶠ v, f v (finAt v (finEmb K n x)) =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, f (w i) (finAt (w i) (finEmb K n x)) := by
  classical
  intro K _ _ n r w hw f hf x
  have hfin : {v : Pl K | finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n}.Finite := by
    have hB : {v : Pl K | AdelicGLn.finiteRestrictedEquiv K n x v ∉
        GLnLocal.integralGL (v.adicCompletion K) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv K n x).2
    refine hB.subset ?_
    intro v hv
    have e : finAt v (finEmb K n x) = AdelicGLn.finiteRestrictedEquiv K n x v := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).2) v = _
      rw [prodEquiv_finEmb]
    simpa [e] using hv
  set S : Finset (Pl K) := hfin.toFinset ∪ Finset.univ.image w with hS
  have hoff : ∀ v, v ∉ Set.range w → f v (finAt v (finEmb K n x)) =
      if finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then 1 else 0 := by
    intro v hv
    rw [hf v hv]
    by_cases h : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n
    · rw [if_pos h]; exact Set.indicator_of_mem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
    · rw [if_neg h]; exact Set.indicator_of_notMem (s := (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v))) h _
  have hsupp : Function.mulSupport (fun v => f v (finAt v (finEmb K n x))) ⊆ (S : Set (Pl K)) := by
    intro v hv
    by_contra hvS
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hvS (by simp [hS])
    have h2 : finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hvS (by simp only [hS, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]; exact Or.inl h)
    exact hv ((hoff v h1).trans (if_pos h2))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    have hsub : Finset.univ.image w ⊆ S := Finset.subset_union_right
    rw [← Finset.prod_subset hsub, Finset.prod_image (fun a _ b _ h => hw h)]
    intro v _ hv
    have h1 : v ∉ Set.range w := by
      rintro ⟨i, rfl⟩
      exact hv (by simp)
    rw [hoff v h1, if_pos (hx v h1)]
  · rw [Set.indicator_of_notMem hx, zero_mul]
    have hx' : ∃ v, v ∉ Set.range w ∧ finAt v (finEmb K n x) ∉ GLnLocal.integralGL (v.adicCompletion K) n := by
      by_contra hc
      push_neg at hc
      exact hx hc
    obtain ⟨v, h1, h2⟩ := hx'
    refine Finset.prod_eq_zero (i := v) ?_ ?_
    · simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset]; exact Or.inl h2
    · rw [hoff v h1, if_neg h2]
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.IndicatorIntegralAwayMulLocalEmbedding
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.indicator_integral_away_mul_localEmbedding :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (i : Fin r) (y : Gw n (w i)) (x : AdelicGLn.FiniteAdelicGL K n),
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) (AdelicGLn.localEmbedding (w i) y * x) =
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x := by
  intro K _ _ n r w i y x
  have key : ∀ v, v ∉ Set.range w →
      finAt v (finEmb K n (AdelicGLn.localEmbedding (w i) y * x)) = finAt v (finEmb K n x) := by
    intro v hv
    have hne : v ≠ w i := fun h => hv ⟨i, h.symm⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 v hne y
    have e : ∀ z : AdelicGLn.FiniteAdelicGL K n,
        finAt v (finEmb K n z) = AdelicGLn.finiteRestrictedEquiv K n z v := fun z => rfl
    rw [e] at h1
    rw [e, e, map_mul, RestrictedProduct.mul_apply, h1, one_mul]
  have hmem : (AdelicGLn.localEmbedding (w i) y * x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) ↔
      (x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) := by
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun v hv => by rw [key v hv]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
end

-- bundled from Development.AutomorphicArithmetic.LocalTestFunctions.IndicatorLevelEqProdLocalIndicator
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.indicator_level_eq_prod_local_indicator :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))),
          (∀ i, J i ≤ GLnLocal.integralGL ((w i).adicCompletion K) n) → ∀ U : Set (AdelicGLn.FiniteAdelicGL K n),
          (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) → ∀ x,
          U.indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) x =
            ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x *
              ∏ i, (J i : Set (Gw n (w i))).indicator 1 (finAt (w i) (finEmb K n x)) := by
  intro K _ _ n r w J hJ U hU x
  have key : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (v : Pl K),
      finAt v (finEmb K n h) = AdelicGLn.finiteRestrictedEquiv K n h v := by
    intro h v
    show AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n h)).2 v = _
    rw [prodEquiv_finEmb]
  have hint : ∀ h : AdelicGLn.FiniteAdelicGL K n, h ∈ AdelicGLn.integralFiniteGL K n ↔
      ∀ v : Pl K, finAt v (finEmb K n h) ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    simp only [key]
  by_cases hx : x ∈ U
  · obtain ⟨h1, h2⟩ := (hU x).1 hx
    have hy : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
        GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      fun v _ => (hint x).1 h1 v
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Finset.prod_eq_one]
    · simp
    · intro i _
      rw [Set.indicator_of_mem (SetLike.mem_coe.2 (h2 i))]
      rfl
  · rw [Set.indicator_of_notMem hx]
    by_cases hJx : ∀ i, finAt (w i) (finEmb K n x) ∈ J i
    · have hy : x ∉ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈
          GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)) := by
        intro hy
        refine hx ((hU x).2 ⟨(hint x).2 fun v => ?_, hJx⟩)
        by_cases hv : v ∈ Set.range w
        · obtain ⟨i, rfl⟩ := hv
          exact hJ i (hJx i)
        · exact hy v hv
      rw [Set.indicator_of_notMem hy, zero_mul]
    · push_neg at hJx
      obtain ⟨i, hi⟩ := hJx
      rw [Finset.prod_eq_zero (Finset.mem_univ i)
        (Set.indicator_of_notMem (SetLike.mem_coe.not.2 hi) _), mul_zero]
end

