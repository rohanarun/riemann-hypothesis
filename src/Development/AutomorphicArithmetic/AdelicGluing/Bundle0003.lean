module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistUnitary
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
public import Development.AutomorphicArithmetic.AdelicGluing.Bundle0001
public import Development.AutomorphicArithmetic.AdelicGluing.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.FinprodLocalFactorsWithIwahoriAtPlace
section
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_atFin {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

private theorem fin_above (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem a_fin (U : Set (Pl E)) (hU : U.Finite) (f : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ)
    (hf : ∀ w ∉ U, f w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1)
    (x : AdelicGLn.FiniteAdelicGL E n) : (Function.mulSupport fun w => f w (cf w x)).Finite := by
  have h := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL E n (finEmb E n x))
  refine (h.union hU).subset fun v hv => ?_
  by_contra hc
  rw [Set.mem_union, not_or] at hc
  have h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion E) n := not_not.1 hc.1
  apply hv
  simp only [hf v hc.2]
  exact Set.indicator_of_mem (by exact h1) _

open Classical in
private theorem iw_split {q : Pl F} (w₀ : PlacesOver E q) (m : Fin n → ℤ) (x : AdelicGLn.FiniteAdelicGL E n) :
    iwFn w₀ m (mapGL n (atFin q) (finEmb E n x)) = (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) *
      ∏ᶠ w : PlacesOver E q, if w = w₀ then 1 else (iwCoset w.1 (0 : Fin n → ℤ)).indicator 1 (cf w.1 x) := by
  unfold iwFn prodFn
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  have key : ∀ w : PlacesOver E q, (iwCoset w.1 (if w = w₀ then m else 0)).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cmp w (mapGL n (atFin q) (finEmb E n x))) =
      (if w = w₀ then (iwCoset w₀.1 m).indicator (1 : GL (Fin n) (w₀.1.adicCompletion E) → ℂ) (cf w₀.1 x) else 1) *
        (if w = w₀ then 1 else (iwCoset w.1 (0 : Fin n → ℤ)).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cf w.1 x)) := by
    intro w
    rw [cmp_atFin]
    by_cases hw : w = w₀
    · subst hw
      simp [cf]
    · simp [hw, cf]
  rw [Finset.prod_congr rfl fun w _ => key w, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ w₀]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.finprod_local_factors_with_iwahori_at_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F), q ∉ S → ∀ (w₀ : PlacesOver E q)
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)),
        (∀ w ∈ κ, w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q) →
        ∀ (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) →
        ∀ (m : Fin n → ℤ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
        (∀ v ∈ S, φ v = ψ v) → φ q = iwFn w₀ m →
        (∀ v ∉ S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1) → ∀ x : AdelicGLn.FiniteAdelicGL E n,
        ∏ᶠ v, φ v (mapGL n (atFin v) (finEmb E n x)) =
          rF S w₀ ψ κ x * (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) * ∏ w ∈ κ, h w (cf w x) := by
  intro F E _ _ _ _ _ n S q hq w₀ ψ κ hκ h hh m φ hS hqφ hoff x
  classical
  let T : Set (Pl E) := {w | w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q}
  have hTfin : T.Finite := by
    refine ((insert q S : Finset (Pl F)).finite_toSet.biUnion fun v _ => fin_above (E := E) v).subset ?_
    intro w hw
    refine Set.mem_biUnion (x := w.under (𝓞 F)) ?_ rfl
    rcases hw with hw | hw
    · simp [hw]
    · simp [hw]
  let h' : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ := fun w => if w ∈ T then 1 else h w
  have hh'T : ∀ w ∈ T, h' w = 1 := fun w hw => by simp only [h', if_pos hw]
  have hh'N : ∀ w ∉ T, h' w = h w := fun w hw => by simp only [h', if_neg hw]
  have hUfin : (T ∪ (κ : Set (Pl E))).Finite := hTfin.union κ.finite_toSet
  have hU : ∀ w ∉ T ∪ (κ : Set (Pl E)), h' w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1 := by
    intro w hw
    rw [Set.mem_union, not_or] at hw
    rw [hh'N w hw.1]
    exact hh w hw.2
  have hafin := a_fin _ hUfin h' hU x
  have hten := UpperTheory.ConvolutionTheory.Tf.tensEProd F E n h'
    (Filter.eventually_cofinite.2 (hUfin.subset fun w hw => by_contra fun hc => hw (hU w hc))) (finEmb E n x)
  let X : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) := fun v => mapGL n (atFin v) (finEmb E n x)
  let B : Pl F → ℂ := fun v => prodFn (v := v) (fun w => h' w.1) (X v)
  let A : Pl F → ℂ := fun v => if v ∈ insert q S then φ v (X v) else 1
  have hB1 : ∀ v ∈ insert q S, B v = 1 := by
    intro v hv
    have hw : ∀ w : PlacesOver E v, h' w.1 (cmp w (X v)) = 1 := by
      intro w
      have : w.1 ∈ T := by
        have := Finset.mem_insert.1 hv
        rcases this with rfl | hv
        · exact Or.inr (under_over w)
        · exact Or.inl ((under_over w).symm ▸ hv)
      rw [hh'T _ this]
      rfl
    simp only [B, prodFn, hw, finprod_one]
  have hfac : ∀ v, φ v (X v) = A v * B v := by
    intro v
    by_cases hv : v ∈ insert q S
    · simp only [A, if_pos hv, hB1 v hv, mul_one]
    · have hv' := Finset.mem_insert.not.1 hv
      push_neg at hv'
      simp only [A, if_neg hv, one_mul, B]
      rw [hoff v hv'.2 hv'.1]
      unfold prodFn
      refine finprod_congr fun w => ?_
      show h w.1 (cmp w (X v)) = h' w.1 (cmp w (X v))
      rw [hh'N]
      rintro (h1 | h1)
      · exact hv'.2 (under_over w ▸ h1)
      · exact hv'.1 ((under_over w).symm.trans h1)
  have hAsub : Function.mulSupport A ⊆ (insert q S : Finset (Pl F)) := by
    intro v hv
    by_contra hc
    exact hv (if_neg hc)
  have hAfin : (Function.mulSupport A).Finite := (Finset.finite_toSet _).subset hAsub
  have hBfin : (Function.mulSupport B).Finite := by
    refine (hafin.image fun w : Pl E => w.under (𝓞 F)).subset ?_
    intro v hv
    by_contra hc
    apply hv
    have hw : ∀ w : PlacesOver E v, h' w.1 (cmp w (X v)) = 1 := by
      intro w
      by_contra hne
      refine hc ⟨w.1, ?_, under_over w⟩
      intro h0
      apply hne
      rw [show cmp w (X v) = cf w.1 x from cmp_atFin w _]
      exact h0
    simp only [B, prodFn, hw, finprod_one]
  have hAprod : ∏ᶠ v, A v = iwFn w₀ m (X q) * ∏ v ∈ S, ψ v (X v) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hAsub, Finset.prod_insert hq]
    congr 1
    · simp only [A, Finset.mem_insert_self, if_true, hqφ]
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [A, if_pos (Finset.mem_insert_of_mem hv), hS v hv]
  have hBprod : ∏ᶠ v, B v = ∏ᶠ w, h' w (cf w x) := hten
  have haprod : ∏ᶠ w, h' w (cf w x) = (Cnd S q κ).indicator 1 x * ∏ w ∈ κ, h w (cf w x) := by
    by_cases hx : x ∈ Cnd S q κ
    · have hsub : Function.mulSupport (fun w => h' w (cf w x)) ⊆ κ := by
        intro w hw
        by_contra hc
        apply hw
        show h' w (cf w x) = 1
        by_cases hT : w ∈ T
        · rw [hh'T w hT]
          rfl
        · rw [hU w (by simp only [Set.mem_union, not_or]; exact ⟨hT, hc⟩)]
          have hT' : w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q := by
            simpa [T, not_or] using hT
          exact Set.indicator_of_mem (hx w hc hT'.1 hT'.2) _
      rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Set.indicator_of_mem hx]
      simp only [Pi.one_apply, one_mul]
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [hh'N]
      rintro (h1 | h1)
      · exact (hκ w hw).1 h1
      · exact (hκ w hw).2 h1
    · have hex : ∃ w, w ∉ κ ∧ w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q ∧
          cf w x ∉ GLnLocal.integralGL (w.adicCompletion E) n := by
        by_contra hc
        push_neg at hc
        exact hx fun w h1 h2 h3 => hc w h1 h2 h3
      obtain ⟨w, hwκ, hwS, hwq, hnot⟩ := hex
      have hwT : w ∉ T := by
        rintro (h1 | h1)
        · exact hwS h1
        · exact hwq h1
      have h0 : h' w (cf w x) = 0 := by
        rw [hU w (by simp only [Set.mem_union, not_or]; exact ⟨hwT, hwκ⟩)]
        exact Set.indicator_of_notMem hnot _
      rw [finprod_eq_zero (fun w => h' w (cf w x)) w h0 hafin, Set.indicator_of_notMem hx, zero_mul]
  have hfinal : ∏ᶠ v, φ v (X v) = (∏ᶠ v, A v) * ∏ᶠ v, B v := by
    rw [← finprod_mul_distrib hAfin hBfin]
    exact finprod_congr hfac
  show ∏ᶠ v, φ v (X v) = _
  rw [hfinal, hAprod, hBprod, haprod, iw_split]
  unfold rF
  ring
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.GaloisTwistCompUOperatorEqUOperatorSmulPlace
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

private theorem prj_map {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H ≃ₗᵢ[ℂ] H) (W W' : Submodule ℂ H) (hW : IsClosed (W : Set H)) (hW' : IsClosed (W' : Set H))
    (hU : ∀ v, U v ∈ W' ↔ v ∈ W) (v : H) : U (prj W v) = prj W' (U v) := by
  have hc : W.topologicalClosure = W := hW.submodule_topologicalClosure_eq
  have hc' : W'.topologicalClosure = W' := hW'.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ W.topologicalClosure ↔ v ∈ W := fun v => by rw [hc]
  have hm' : ∀ v, v ∈ W'.topologicalClosure ↔ v ∈ W' := fun v => by rw [hc']
  have a1 : prj W v ∈ W := (hm _).1 (Submodule.starProjection_apply_mem _ v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hm' _).2 ((hU _).2 a1)) fun u hu => ?_
  have hu' : U.symm u ∈ W := (hU _).1 (by simpa using (hm' _).1 hu)
  have e : u = U (U.symm u) := by simp
  rw [e, ← map_sub, LinearIsometryEquiv.inner_map_map]
  exact Submodule.starProjection_inner_eq_zero v _ ((hm _).2 hu')

private theorem mk_iff {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (a b : G) :
    (QuotientGroup.mk (s a) : G' ⧸ J') = QuotientGroup.mk (s b) ↔
      (QuotientGroup.mk a : G ⧸ J) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, QuotientGroup.eq, hJ, map_mul, map_inv]

private theorem cosets {G G' : Type} [Group G] [Group G'] (s : G ≃* G') (J : Subgroup G) (J' : Subgroup G')
    (hJ : ∀ g, g ∈ J ↔ s g ∈ J') (x : G)
    (hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → G),
      Function.Injective (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) ∧
      Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} ∧
      Function.Injective (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) ∧
      Set.range (fun i => (QuotientGroup.mk (s (y i)) : G' ⧸ J')) =
        {c | ∃ k ∈ J', c = QuotientGroup.mk (k * s x)} := by
  classical
  let S := {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}
  haveI : Fintype S := hS.fintype
  have hout : ∀ c : S, (QuotientGroup.mk (c.1.out) : G ⧸ J) = c.1 := fun c => QuotientGroup.out_eq' c.1
  refine ⟨S, inferInstance, fun c => c.1.out, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    have h' : (QuotientGroup.mk (a.1.out) : G ⧸ J) = QuotientGroup.mk (b.1.out) := h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      have : (QuotientGroup.mk (i.1.out) : G ⧸ J) ∈ S := by rw [hout]; exact i.2
      exact this
    · intro hc
      exact ⟨⟨c, hc⟩, hout ⟨c, hc⟩⟩
  · intro a b h
    apply Subtype.ext
    have h' := (mk_iff s J J' hJ _ _).1 h
    rwa [hout, hout] at h'
  · ext c
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk, e⟩ := i.2
      refine ⟨s k, (hJ k).1 hk, ?_⟩
      have h1 : (QuotientGroup.mk (i.1.out) : G ⧸ J) = QuotientGroup.mk (k * x) := (hout i).trans e
      have h2 := (mk_iff s J J' hJ _ _).2 h1
      rw [map_mul] at h2
      exact h2
    · rintro ⟨k, hk, rfl⟩
      have hk0 : s.symm k ∈ J := (hJ _).2 (by simpa using hk)
      have hc : (QuotientGroup.mk (s.symm k * x) : G ⧸ J) ∈ S := ⟨_, hk0, rfl⟩
      refine ⟨⟨_, hc⟩, ?_⟩
      have h2 := (mk_iff s J J' hJ _ _).2 (hout ⟨_, hc⟩)
      rw [map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2

private theorem cosets_eq {G : Type} [Group G] (J : Subgroup G) (a b x : G) (ha : a ∈ J) (hb : b ∈ J) :
    {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * (a * x * b))} =
      {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} := by
  have key : ∀ k : G, (QuotientGroup.mk (k * (a * x * b)) : G ⧸ J) = QuotientGroup.mk (k * a * x) := fun k => by
    rw [QuotientGroup.eq]
    have e : (k * (a * x * b))⁻¹ * (k * a * x) = b⁻¹ := by group
    rw [e]
    exact J.inv_mem hb
  ext c
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * a, J.mul_mem hk ha, key k⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, J.mul_mem hk (J.inv_mem ha), ?_⟩
    rw [key]
    simp

private theorem fixL_iff {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v := by
  unfold fixL
  rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.1]
  constructor
  · exact fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.galoisTwist_comp_uOperator_eq_uOperator_smul_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n →
          ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (w : Pl E) (ν : Fin n → ℤ),
            θ.U ∘L Uiw μ w ν = Uiw μ (σ • w) ν ∘L θ.U := by
  intro F E _ _ _ _ _ _ σ n hn μ _ θ hθ w ν
  obtain ⟨s, hs1, hs2, hs3⟩ := UpperTheory.exists_galois_transport_localGL_preserving_iwahori F E σ n hn w
  obtain ⟨U, hU, hint, -⟩ := UpperTheory.ConvolutionTheory.C.twistUnitary E n μ θ
  have hO := GLnLocal.isOpen_iwahori (w.adicCompletion E) n
  have hC := GLnLocal.isCompact_iwahori (w.adicCompletion E) n
  have hO' := GLnLocal.isOpen_iwahori ((σ • w).adicCompletion E) n
  have hC' := GLnLocal.isCompact_iwahori ((σ • w).adicCompletion E) n
  have hrho : ∀ g v, U (rhoL μ w g v) = rhoL μ (σ • w) (s g) (U v) := fun g v => by
    have e := UpperTheory.galTwist_finProj_eq_of_galAd_finEmb_eq F E σ n hn μ θ hθ _ _ (hs1 g)
    show U (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding w g)) v) =
      rightRegularRep (rationalGLOne (K := E) (n := n)) μ (MultiplicityOne.finProj E n (AdelicGLn.localEmbedding (σ • w) (s g))) (U v)
    rw [hint, e]
  have hfx : ∀ v, U v ∈ fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) ↔
      v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) := fun v => by
    rw [fixL_iff, fixL_iff]
    constructor
    · intro h k hk
      apply U.injective
      rw [hrho]
      exact h _ ((hs2 k).1 hk)
    · intro h k' hk'
      have e : k' = s (s.symm k') := by simp
      rw [e, ← hrho, h _ ((hs2 _).2 (by simpa using hk'))]
  have hP : ∀ v, U (prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v) =
      prj (fixL μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n)) (U v) :=
    prj_map U _ _ (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).1 hfx
  obtain ⟨hf, -, hHP, hsum, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w _
    (Cartan.diagPow (w.adicCompletion E) n ν) hO hC
  obtain ⟨-, -, hHP', hsum', -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ (σ • w) _
    (s (Cartan.diagPow (w.adicCompletion E) n ν)) hO' hC'
  obtain ⟨ι, _, y, i1, r1, i2, r2⟩ := cosets s _ _ hs2 _ hf
  have hmain : ∀ v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n),
      U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
        Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v) := fun v hv => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum ι y i1 r1 v hv, hsum' ι (fun i => s (y i)) i2 r2 (U v) ((hfx v).2 hv), map_sum]
    exact Finset.sum_congr rfl fun i _ => hrho _ _
  obtain ⟨a, ha, b, hb, hab⟩ := hs3 ν
  have hH : Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) =
      Uiw μ (σ • w) ν := by
    unfold Uiw Hop
    rw [hab, cosets_eq _ a b _ ha hb]
  rw [← hU, ← hH]
  refine ContinuousLinearMap.ext fun v => ?_
  have e1 := DFunLike.congr_fun hHP v
  have e2 := DFunLike.congr_fun hHP' (U v)
  simp only [ContinuousLinearMap.comp_apply] at e1 e2
  have hm : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n)) v ∈ fixL μ w (GLnLocal.iwahori (w.adicCompletion E) n) :=
    (UpperTheory.ConvolutionTheory.Tf.commPrj E n μ _).2.2.1 v
  show U (Hop μ w (GLnLocal.iwahori (w.adicCompletion E) n) (Cartan.diagPow (w.adicCompletion E) n ν) v) =
    Hop μ (σ • w) (GLnLocal.iwahori ((σ • w).adicCompletion E) n) (s (Cartan.diagPow (w.adicCompletion E) n ν)) (U v)
  rw [← e1, hmain _ hm, hP, e2]
end

-- bundled from Development.AutomorphicArithmetic.AdelicGluing.HeightBoundedOnSupportOfCompactTestFunctions
section
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
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

private theorem loc_bd (w : Pl E) {C : Set (GL (Fin n) (w.adicCompletion E))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion E) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) : infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem lies_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_of_lies {w : Pl E} {v : Pl F} (hl : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 F) = v := by
  ext1
  exact (hl.over).symm

end

theorem UpperTheory.height_bounded_on_support_of_compact_test_functions :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E))
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ v ∈ S, HasCompactSupport (ψ v)) → (∀ w ∈ κ, HasCompactSupport (h w)) →
        ∃ Yf : ℝ, 1 ≤ Yf ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) →
          (∀ w ∈ κ, h w (cf w x) ≠ 0) → x ∈ Cnd S q κ → heightOff q (finEmb E n x) ≤ Yf := by
  classical
  intro F E _ _ _ _ _ n S q κ ψ h hψ hh
  have key : ∀ w : Pl E, ∃ M : ℝ, 1 ≤ M ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n,
      (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) → (∀ w ∈ κ, h w (cf w x) ≠ 0) →
      (w ∈ κ ∨ w.under (𝓞 F) ∈ S) → locHeight (cf w x) ≤ M := by
    intro w
    by_cases hk : w ∈ κ
    · obtain ⟨B, hB1, hB⟩ := loc_bd w (hh w hk).isCompact
      exact ⟨B, hB1, fun x _ h2 _ => hB _ (subset_tsupport _ (Function.mem_support.2 (h2 w hk)))⟩
    · by_cases hs : w.under (𝓞 F) ∈ S
      · have hc := (hψ _ hs).isCompact.image (cmp_continuous (n := n) (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))))
        obtain ⟨B, hB1, hB⟩ := loc_bd w hc
        refine ⟨B, hB1, fun x h1 _ _ => ?_⟩
        have e : UpperTheory.ConvolutionTheory.GM.cmp (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F)))
            (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) = cf w x := by
          ext i j
          rfl
        rw [← e]
        exact hB _ ⟨_, subset_tsupport _ (Function.mem_support.2 (h1 _ hs)), rfl⟩
      · exact ⟨1, le_rfl, fun x _ _ hd => absurd hd (by simp [hk, hs])⟩
  choose M hM1 hM using key
  let W : Finset (Pl E) := κ ∪ S.biUnion fun v => (Finset.univ : Finset (PlacesOver E v)).image Subtype.val
  have hW : ∀ w, w ∈ W ↔ (w ∈ κ ∨ w.under (𝓞 F) ∈ S) := by
    intro w
    simp only [W, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    refine or_congr Iff.rfl ⟨?_, fun hs => ⟨_, hs, ⟨w, lies_under w⟩, rfl⟩⟩
    rintro ⟨v, hv, p, rfl⟩
    rwa [under_of_lies p.2]
  refine ⟨∏ w ∈ W, M w, Finset.prod_induction _ (fun y : ℝ => 1 ≤ y)
    (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun w _ => hM1 w, ?_⟩
  intro x h1 h2 hx
  unfold heightOff
  have hi : (∏ w : InfinitePlace E, locHeight (infAt w (finEmb E n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (finEmb E n x))) =
      if w.under (𝓞 F) ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := W)]
  · refine Finset.prod_le_prod₀ (fun w _ => ?_) fun w hw => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact hM w x h1 h2 ((hW w).1 hw)
      · exact hM1 w
  · intro w hw
    by_contra hc
    apply hw
    have hc' : w ∉ W := hc
    rw [hW, not_or] at hc'
    by_cases hq : w.under (𝓞 F) = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact locHeight_eq_one_of_mem_integralGL (hx w hc'.1 hc'.2 hq)
end

