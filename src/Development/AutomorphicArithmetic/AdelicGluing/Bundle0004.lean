module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.OfinDoubleCosetIndicatorEqHop
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem out_mem_iff {G : Type*} [Group G] (J : Subgroup G) (y : G) (c : G ⧸ J) :
    c.out ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)} := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, ?_⟩
    rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa [mul_assoc] using J.inv_mem hb)
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J (k * y)
    exact ⟨k, hk, j, j.2, hj⟩

private theorem dc_support {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G) (y : G)
    (hc : IsCompact (J : Set G)) :
    HasCompactSupport ({g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ)) := by
  have hDc : IsCompact {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    have : {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} = (fun p : G × G => p.1 * y * p.2) ''
        ((J : Set G) ×ˢ (J : Set G)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, SetLike.mem_coe, Prod.exists]
      exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, b, ⟨ha, hb⟩, e.symm⟩, fun ⟨a, b, ⟨ha, hb⟩, e⟩ => ⟨a, ha, b, hb, e.symm⟩⟩
    rw [this]
    exact (hc.prod hc).image (by fun_prop)
  exact HasCompactSupport.intro hDc fun x hx => Set.indicator_of_notMem hx _

private theorem dc_inv {G : Type*} [Group G] (J : Subgroup G) (y : G) :
    ∀ k ∈ J, ∀ x, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) (x * k) =
      {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 x := by
  have hmem : ∀ k ∈ J, ∀ x, x * k ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} ↔
      x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    intro k hk x
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k⁻¹, J.mul_mem hb (J.inv_mem hk), by rw [← mul_assoc, ← e]; simp⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * k, J.mul_mem hb hk, by rw [e]; simp [mul_assoc]⟩
  intro k hk x
  by_cases hx : x ∈ {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem k hk x).2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun q => hx ((hmem k hk x).1 q)]

private theorem dc_sum {G E : Type*} [Group G] [AddCommMonoid E] [Module ℂ E] (J : Subgroup G) (y : G) (ρ : G → E) :
    (∑ᶠ c : G ⧸ J, {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ) c.out • ρ c.out) =
      ∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}, ρ c.out := by
  rw [finsum_mem_def]
  refine finsum_congr fun c => ?_
  by_cases hcC : c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * y)}
  · rw [Set.indicator_of_mem hcC, Set.indicator_of_mem ((out_mem_iff J y c).2 hcC)]
    simp
  · rw [Set.indicator_of_notMem hcC, Set.indicator_of_notMem fun q => hcC ((out_mem_iff J y c).1 q)]
    simp

theorem UpperTheory.Ofin_doubleCoset_indicator_eq_Hop :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
      (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (y : GL (Fin n) (w.adicCompletion K)),
      IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
        (∀ x, e₀ x = r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w x)) →
        (∀ x, e₁ x = r x * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator 1 (cf w x)) →
        Ofin μ m e₁ = Hop μ w J y ∘L Ofin μ m e₀ := by
  intro K _ _ n hn μ _ m _ w J y ho hc r hr e₀ e₁ h0 h1
  obtain ⟨hfix, heq⟩ := UpperTheory.ConvolutionTheory.GM.stepFin K n hn μ m w J ho _ (dc_support J y hc) (dc_inv J y) r hr e₀ e₁ h0 h1
  refine ContinuousLinearMap.ext fun u => ?_
  rw [heq, dc_sum J y (rhoL μ w)]
  have hp : prj (fixL μ w J) (Ofin μ m e₀ u) = Ofin μ m e₀ u :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.2.2.1 _ (hfix u)
  simp only [Hop, ContinuousLinearMap.comp_apply, hp]
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.ProdFnIsLocallyConstantHasCompactSupport
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

private theorem one_apply_pi (i j : Fin n) (w : PlacesOver E v) :
    (1 : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i j w =
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij]

private noncomputable def glGlue (x : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E)) :
    GL (Fin n) (CompletionsOver E v) where
  val := Matrix.of fun i j w => (x w).val i j
  inv := Matrix.of fun i j w => ((x w)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).val_inv i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1
  inv_val := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).inv_val i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1

private theorem glGlue_continuous :
    Continuous (glGlue (E := E) (n := n) (v := v)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply w)
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_inv.comp (continuous_apply w))

private theorem glGlue_cmp (g : GL (Fin n) (CompletionsOver E v)) :
    glGlue (fun w => UpperTheory.ConvolutionTheory.GM.cmp w g) = g := by
  ext i j w
  rfl

end

theorem UpperTheory.prodFn_isLocallyConstant_hasCompactSupport :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ),
        (∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) →
        IsLocallyConstant (prodFn h) ∧ HasCompactSupport (prodFn h) := by
  intro F E _ _ _ _ _ n v h hh
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  have hp : prodFn h = fun g => ∏ w, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
    funext g
    exact finprod_eq_prod_of_fintype _
  constructor
  · have key : ∀ s : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ s, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hh a).1.comp_continuous (cmp_continuous a)).mul ih
    rw [hp]
    exact key Finset.univ
  · have hK : IsCompact (glGlue '' Set.pi Set.univ fun w : PlacesOver E v => tsupport (h w)) :=
      (isCompact_univ_pi fun w => (hh w).2).image glGlue_continuous
    set_option synthInstance.maxHeartbeats 200000 in
      refine HasCompactSupport.of_support_subset_isCompact hK fun g hg => ?_
    refine ⟨fun w => UpperTheory.ConvolutionTheory.GM.cmp w g, fun w _ => subset_tsupport _ ?_, glGlue_cmp g⟩
    rw [Function.mem_support, hp] at hg
    intro h0
    exact hg (Finset.prod_eq_zero (Finset.mem_univ w) h0)
end

