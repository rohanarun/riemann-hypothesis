module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0001
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0008
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0009
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CommutingSmoothIrreducibleFixedVectors
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_res {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Submodule ℂ H) :
    ∀ (r : ℕ) (T : Fin r → H →L[ℂ] H) (t : Fin r → Module.End ℂ X), (∀ i (v : X), ((t i v : X) : H) = T i v) →
      ∀ v : X, (((List.ofFn t).prod v : X) : H) = (List.ofFn T).prod v := by
  intro r
  induction r with
  | zero => intro T t _ v; simp
  | succ r ih =>
    intro T t h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, h,
      ih (fun i => T i.succ) (fun i => t i.succ) (fun i => h _) v]
    rfl

private theorem comm_adj {A : Type} [Ring A] [Algebra ℂ A] {s t : Set A} (h : ∀ a ∈ s, ∀ b ∈ t, Commute a b) {a b : A}
    (ha : a ∈ Algebra.adjoin ℂ s) (hb : b ∈ Algebra.adjoin ℂ t) : Commute a b :=
  Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun y hy =>
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha fun x hx => (h x hx y hy).symm).symm

set_option maxHeartbeats 800000 in
theorem UpperTheory.commuting_smooth_irreducible_fixed_vectors :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → ∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) → (Z ⊓ ⨅ i, fixU (π i) (U i)) ≠ ⊥ → (∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥) ∧ ∃ N : ℕ, ∀ (T : Fin r → H →L[ℂ] H) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i, ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), T i v ∈ (Z ⊓ ⨅ i, fixU (π i) (U i))) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x : fixedVectors (τ i) (U i), T i (f x) = f (B i x)) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) (List.ofFn T).prod = N * ∏ i, LinearMap.trace ℂ (fixedVectors (τ i) (U i)) (B i) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV U hU hfd hne
  set X := Z ⊓ ⨅ i, fixU (π i) (U i) with hX
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hDc : ∀ i, IsClosed (D i : Set H) := fun i => by
    have : (D i : Set H) = (Z : Set H) ∩ ⋂ j, ⋂ _ : j ≠ i, (fixU (π j) (U j) : Set H) := by
      ext v; rw [SetLike.mem_coe, hD]; simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    exact hZc.inter (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_fixU _ _)
  have hDi : ∀ i, (π i).IsInvariant (D i) := fun i g v hv => (hD i _).2 ⟨hZi i g v ((hD i v).1 hv).1, fun j hj u hu => by
    rw [hcm j i hj, ((hD i v).1 hv).2 j hj u hu]⟩
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hle : ∀ i, X ≤ spanFix (τ i) (π i) (D i) (U i) := fun i => (hXD i).le.trans
    (UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll (G i) H (S i) (τ i) (hsm i) (π i) (U i) (hU i).1 (hU i).2 V (D i) (hDc i) (hDi i) (inf_le_left.trans hZV) (hV i)
      (hXD i ▸ hfd))
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  have h1 : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (U i)) ∧ fixedVectors (τ i) (U i) ≠ ⊥ := fun i => by
    obtain ⟨f, hf, x, hx, h0⟩ : ∃ f, Eqv (τ i) (π i) (D i) f ∧ ∃ x ∈ fixedVectors (τ i) (U i), f x ≠ 0 := by
      by_contra hno
      push Not at hno
      refine hne (le_bot_iff.1 ((hle i).trans (Submodule.span_le.2 ?_)))
      rintro _ ⟨f, hf, x, hx, rfl⟩
      exact hno f hf x hx
    have := hirr i
    have hinj : Function.Injective f := by
      rcases eq_bot_or_eq_top (⟨LinearMap.ker f, fun g v hv => by
        rw [LinearMap.mem_ker] at hv ⊢; rw [hf.map, hv, map_zero]⟩ : Subrepresentation (τ i)) with e | e
      · exact LinearMap.ker_eq_bot.1 (congrArg Subrepresentation.toSubmodule e)
      · exact (h0 (by rw [LinearMap.ker_eq_top.1 (congrArg Subrepresentation.toSubmodule e)]; rfl)).elim
    refine ⟨Module.Finite.of_injective ((f ∘ₗ (fixedVectors (τ i) (U i)).subtype).codRestrict X (hm i f hf)) fun a b e =>
      Subtype.ext (hinj (congrArg Subtype.val e)), fun e => h0 ?_⟩
    rw [e] at hx
    rw [(Submodule.mem_bot ℂ).1 hx, map_zero]
  refine ⟨h1, ?_⟩
  have := fun i => (h1 i).1
  have := fun i => Submodule.nontrivial_iff_ne_bot.2 (h1 i).2
  choose c hc1 hc2 using fun i => UpperTheory.exists_algHom_end_fixedVectors_to_fixed_subspace (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (U i) (hU i).1 (hU i).2 (D i) X
    (hDc i) (hDi i) (hXD i) (hle i)
  obtain ⟨N, hN⟩ := UpperTheory.trace_pairing_separates_endomorphisms r X (fun i => fixedVectors (τ i) (U i)) c fun i j hij s t => by
    refine comm_adj ?_ (hc2 i s) (hc2 j t)
    rintro a ⟨g, ha⟩ b ⟨h, hb⟩
    obtain ⟨q1, q2⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (U i) (U j)).2.2.2 (hcm i j hij)
    obtain ⟨q3, -⟩ := (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (U j) (U i)).2.2.2 (hcm j i hij.symm)
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, ha, hb, hb, ha, ← q3, ← q1, q2, hcm i j hij]
  refine ⟨N, fun T B hT hB => ?_⟩
  rw [← hN B]
  refine (UpperTheory.trOn_restrict_and_eq_of_maps_into H X X _).1 _ (prod_res X r T _ fun i v => ?_)
  have key : ∀ y ∈ spanFix (τ i) (π i) (D i) (U i), ∃ h : y ∈ X, ((c i (B i) ⟨y, h⟩ : X) : H) = T i y := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      exact ⟨hm i f hf ⟨x, hx⟩, (hc1 i (B i) f hf ⟨x, hx⟩ _ rfl).trans (hB i f ⟨fun _ => trivial, hf.map⟩ ⟨x, hx⟩).symm⟩
    | zero => exact ⟨X.zero_mem, (congrArg Subtype.val (map_zero (c i (B i)))).trans (map_zero (T i)).symm⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      refine ⟨X.add_mem a b, (congrArg Subtype.val (map_add (c i (B i)) ⟨u, a⟩ ⟨v, b⟩)).trans ?_⟩
      rw [map_add (f := _), ← ha, ← hb]; rfl
    | smul k u _ h1 =>
      obtain ⟨a, ha⟩ := h1
      refine ⟨X.smul_mem k a, (congrArg Subtype.val (map_smul (c i (B i)) k ⟨u, a⟩)).trans ?_⟩
      rw [map_smul, ← ha]; rfl
  exact (key v (hle i v.2)).2
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsPosConstProdLocalHeckeOperators
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

theorem UpperTheory.exists_pos_const_prod_localHeckeOperators :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure],
      ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI K n) (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
        (mw : ∀ i, Measure (Gw n (w i))) (f : ∀ v : Pl K, Gw n v → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (g : TG K n),
        Function.Injective w → (∀ i, (mw i).IsHaarMeasure ∧ mw i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
        (∀ i, Test (f (w i))) →
        (∀ v, v ∉ Set.range w → f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set (Gw n v)).indicator 1) →
        (∀ i, IsOloc μ (w i) (mw i) (f (w i)) (T i)) → (∀ x, g x = PositivityTheory.Rg.Tf.Geo.avg (tensF (onInf a) f) x) →
        RR μ g = (κ : ℂ) • (Oinf μ ν a ∘L (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))) := by
  intro K _ _ n hn μ _ ν _
  obtain ⟨m, _, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  refine ⟨m.real (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)), ?_, ?_⟩
  · have ho := AdelicGLn.isOpen_integralFiniteGL K n
    have hc := AdelicGLn.isCompact_integralFiniteGL K n
    exact ENNReal.toReal_pos (ho.measure_pos m ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne
  intro a r w _ _ mw f T g hw hm ht hoff hT hg
  obtain ⟨e, he, -, hO⟩ := UpperTheory.ConvolutionTheory.Tf.finTens K n μ m r w hw f ht hoff
  have hge : g = tens a e := by
    obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.Tf.avgTens K n hn a e (fun g => a (infPart K n g) * e (finPart K n g)) (fun _ => rfl)
    have hΦ : tensF (onInf a) f = fun g => a (infPart K n g) * e (finPart K n g) := by
      funext g
      simp only [tensF, onInf]
      rw [h2 g, he (finPart K n g)]
      congr 1
    refine DFunLike.ext _ _ fun x => ?_
    rw [hg x, hΦ, h1 x]
  have hUS : ∀ h, h ∈ levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _)) ↔
      h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) = 1 := by
    intro h
    rw [AdelicGLn.mem_integralFiniteGL_iff_forall]
    change (∀ v, finAt v (finEmb K n h) ∈ if v ∈ Finset.univ.image w then (⊥ : Subgroup _)
      else GLnLocal.integralGL (v.adicCompletion K) n) ↔ _
    constructor
    · intro H
      refine ⟨fun v => ?_, fun i => ?_⟩
      · have := H v
        split_ifs at this with hv
        · rw [Subgroup.mem_bot] at this
          change finAt v (finEmb K n h) ∈ _
          rw [this]
          exact one_mem _
        · exact this
      · have := H (w i)
        rw [if_pos (by simp)] at this
        exact Subgroup.mem_bot.1 this
    · rintro ⟨H1, H2⟩ v
      split_ifs with hv
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
        exact Subgroup.mem_bot.2 (H2 i)
      · exact H1 v
  have hfix : fixF μ (levOn (Finset.univ.image w) (fun _ => (⊥ : Subgroup _))) = sphOff μ (Finset.univ.image w) := by
    rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ (Finset.univ.image w) (fun _ => ⊥)]
    have htop : ∀ v : Pl K, fixL μ v (⊥ : Subgroup (Gw n v)) = ⊤ := by
      intro v
      simp [fixL, fixF, rhoF, Subgroup.map_bot]
      rfl
    simp [htop]
  have hOf := hO mw (fun i => (hm i).1) (fun i => (hm i).2) T hT _ hUS
  rw [hfix] at hOf
  rw [hge, UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ ν m hC a e, hOf, ContinuousLinearMap.comp_smul]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalEigenspaceInfFixedCompactOpen
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped Classical

theorem UpperTheory.finiteDimensional_eigenspace_inf_fixed_compactOpen :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (r : ℕ) (w : Fin r → Pl K), IsSummand μ V → x ≠ 0 → Function.Injective w →
        ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
          FiniteDimensional ℂ ↥((eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i)) := by
  intro K _ _ n hn μ _ ν _ V a x r w hV hx hw U hCO
  let U' : ∀ v : Pl K, Subgroup (Gw n v) := fun v =>
    if h : ∃ i, w i = v then h.choose_spec ▸ U h.choose else ⊥
  have hU' : ∀ i, U' (w i) = U i := by
    intro i
    have h : ∃ j, w j = w i := ⟨i, rfl⟩
    have key : ∀ (j : Fin r) (e : w j = w i), (e ▸ U j : Subgroup (Gw n (w i))) = U i := by
      intro j e
      obtain rfl := hw e
      rfl
    simp only [U', dif_pos h]
    exact key _ _
  have hCO' : ∀ v ∈ Finset.univ.image w, CO (U' v) := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [hU']
    exact hCO i
  have hfin := UpperTheory.ConvolutionTheory.C.eigAdm K n hn μ ν a x hx (Finset.univ.image w) U' hCO'
  have hVc : V ≤ cuspidalL2 μ := hV.le
  have hle : (eigIn V (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w)) ⊓ ⨅ i, fixL μ (w i) (U i) ≤
      eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ (Finset.univ.image w) ⊓
        ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v) := by
    intro u hu
    obtain ⟨⟨he, hs⟩, hf⟩ := hu
    refine ⟨⟨?_, hs⟩, ?_⟩
    · have hmem : ∀ (W : Submodule ℂ (LL μ)) (y : LL μ), y ∈ eigIn W (Oinf μ ν a) x ↔ y ∈ W ∧ Oinf μ ν a y = (x : ℂ) • y := by
        intro W y
        simp [eigIn, Module.End.mem_eigenspace_iff]
      have he' := (hmem V u).1 he
      exact (hmem _ u).2 ⟨hVc he'.1, he'.2⟩
    · have hf' : u ∈ ⨅ i, fixL μ (w i) (U i) := hf
      rw [Submodule.mem_iInf] at hf'
      change u ∈ ⨅ v ∈ Finset.univ.image w, fixL μ v (U' v)
      simp only [Submodule.mem_iInf]
      intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hU']
      exact hf' i
  haveI := hfin
  exact Submodule.finiteDimensional_of_le hle
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubmoduleProductDecomposition
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_submodule_product_decomposition :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) (J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i))), (∀ i (x : fixedVectors (τ i) (K i)), ((J i x : fixedVectors (τ i) (K i)) : S i) = I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) → (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∀ (x : fixedVectors (τ i) (K i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (K i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i)) → ∃ ρ : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), (∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), ((ρ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod v)) ∧ ∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J hJ hcf hsp
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (K i)
  let Pr : H →L[ℂ] H := (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have hPr : ∀ v ∈ Z, Pr v ∈ (Z ⊓ ⨅ j, fixU (π j) (L j)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hc i j hij)).1 h v)
  have hRX : ∀ v ∈ Z, R (Pr v) ∈ X := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hPr v hv)
    refine Submodule.mem_inf.2 ⟨hRZ _ h1, (Submodule.mem_iInf _).2 fun j u hu => ?_⟩
    have h := hRs j ((s j).symm u) _ h1
    rw [(s j).apply_symm_apply] at h
    rw [← h, (Submodule.mem_iInf _).1 h2 j _ (hsK j u hu)]
  have hm : ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f →
      ∀ x ∈ fixedVectors (τ i) (K i), f x ∈ X := fun i f hf x hx => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hf.mem x)
    refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      exact fun u hu => by rw [← hf.map, mem_fixedVectors.1 hx u hu]
    · exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 j) e
  let ρ : Module.End ℂ X := ((R : H →ₗ[ℂ] H) ∘ₗ (Pr : H →ₗ[ℂ] H) ∘ₗ X.subtype).codRestrict X
    fun v => hRX _ (Submodule.mem_inf.1 v.2).1
  refine ⟨ρ, fun v => rfl, fun i a b hab => ?_⟩
  have key : ∀ y ∈ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i),
      ∃ h : y ∈ X, ρ (c i a ⟨y, h⟩) = c i b (ρ ⟨y, h⟩) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      obtain ⟨f', hf', hff⟩ := UpperTheory.isotypic_projection_product_commute r G H S π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
      have hρ : ∀ (x' : fixedVectors (τ i) (K i)) (h : f x' ∈ X), ((ρ ⟨f x', h⟩ : X) : H) = f' (J i x') := by
        intro x' h
        rw [hJ]
        exact hff x'
      have hy := hm i f hf x hx
      refine ⟨hy, Subtype.ext ?_⟩
      have e1 : c i a ⟨f x, hy⟩ = ⟨f (a ⟨x, hx⟩), hm i f hf _ (a ⟨x, hx⟩).2⟩ :=
        Subtype.ext (hcf i a f hf ⟨x, hx⟩ _ rfl)
      have e2 : ((c i b (ρ ⟨f x, hy⟩) : X) : H) = f' (b (J i ⟨x, hx⟩)) :=
        hcf i b f' hf' (J i ⟨x, hx⟩) _ (hρ ⟨x, hx⟩ hy)
      have e3 : b (J i ⟨x, hx⟩) = J i (a ⟨x, hx⟩) := LinearMap.congr_fun hab ⟨x, hx⟩
      rw [e1, e2, e3]
      exact hρ _ _
    | zero => exact ⟨X.zero_mem, by
        show ρ (c i a 0) = c i b (ρ 0)
        simp only [map_zero]⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨p, hp⟩ := h1
      obtain ⟨q, hq⟩ := h2
      refine ⟨X.add_mem p q, ?_⟩
      show ρ (c i a (⟨u, p⟩ + ⟨v, q⟩)) = c i b (ρ (⟨u, p⟩ + ⟨v, q⟩))
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | smul k u _ h1 =>
      obtain ⟨p, hp⟩ := h1
      refine ⟨X.smul_mem k p, ?_⟩
      show ρ (c i a (k • ⟨u, p⟩)) = c i b (ρ (k • ⟨u, p⟩))
      rw [map_smul, map_smul, map_smul, map_smul, hp]
  exact LinearMap.ext fun v => (key v (hsp i v.2)).2
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TwistedIntertwinerFixedVectorsOfIrreducible
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (s : G ≃ₜ* G) (I : S ≃ₗ[ℂ] S), (∀ g x, I (τ g x) = τ (s g) (I x)) → (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K)) → ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → fixedVectors τ K ≠ ⊥ → ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (t : ℂ), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ HasFinTrace (A ∘ₗ (I : S →ₗ[ℂ] S)) t ∧ t ≠ 0 := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π s I hI hfd K hKc hKo hne
  let sK : Subgroup G := K.map s.toMulEquiv.toMonoidHom
  have hsKc : IsCompact (sK : Set G) := by
    have : (sK : Set G) = s '' (K : Set G) := rfl
    rw [this]
    exact hKc.image s.continuous
  have hsKo : IsOpen (sK : Set G) := by
    have : (sK : Set G) = s.toHomeomorph '' (K : Set G) := rfl
    rw [this]
    exact s.toHomeomorph.isOpenMap _ hKo
  let K₁ : Subgroup G := K ⊓ sK
  have hK₁c : IsCompact (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKc.inter hsKc
  have hK₁o : IsOpen (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hsKo
  have hPle : ∀ x ∈ fixedVectors τ K, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.1
  have hsle : ∀ x ∈ fixedVectors τ sK, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.2
  have hne₁ : fixedVectors τ K₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := hPle x hx
    rwa [h] at this
  have hIm : ∀ x ∈ fixedVectors τ K, I x ∈ fixedVectors τ sK := by
    rintro x hx _ ⟨k, hk, rfl⟩
    show τ (s k) (I x) = I x
    rw [← hI, hx k hk]
  have hIs : ∀ y ∈ fixedVectors τ sK, I.symm y ∈ fixedVectors τ K := by
    intro y hy k hk
    apply I.injective
    rw [hI, I.apply_symm_apply]
    exact hy _ ⟨k, hk, rfl⟩
  let ε : S →ₗ[ℂ] fixedVectors τ sK := fixedProj τ hτ hsKc hsKo
  let h : Module.End ℂ (fixedVectors τ K₁) :=
    LinearMap.codRestrict (fixedVectors τ K₁)
      ((I.symm : S →ₗ[ℂ] S) ∘ₗ (fixedVectors τ sK).subtype ∘ₗ ε ∘ₗ (fixedVectors τ K₁).subtype)
      (fun x => hPle _ (hIs _ (ε x).2))
  obtain ⟨T₀, A₀, ⟨c1, c2, c3, c4, c5⟩, c6⟩ :=
    UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible G H S τ hτ hirr π K₁ hK₁c hK₁o (hfd K₁ hK₁c hK₁o) hne₁ h
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let A : S →ₗ[ℂ] S := (fixedVectors τ K).subtype ∘ₗ e ∘ₗ A₀
  let B : S →ₗ[ℂ] S := A ∘ₗ (I : S →ₗ[ℂ] S)
  have hB : ∀ x ∈ fixedVectors τ K, B x = x := by
    intro x hx
    have hIx := hIm x hx
    have h1 : A₀ (I x) = x := by
      have h2 := c6 ⟨I x, hsle _ hIx⟩
      have h3 : ((ε (I x) : fixedVectors τ sK) : S) = I x := fixedProj_apply_of_mem hτ hsKc hsKo hIx
      have h4 : ((h ⟨I x, hsle _ hIx⟩ : fixedVectors τ K₁) : S) = I.symm (ε (I x) : fixedVectors τ sK) := rfl
      rw [h4, h3, I.symm_apply_apply] at h2
      exact h2
    show ((e (A₀ (I x)) : fixedVectors τ K) : S) = x
    rw [h1]
    exact fixedProj_apply_of_mem hτ hKc hKo hx
  have hR : LinearMap.range B = fixedVectors τ K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (e _).2
    · intro x hx
      exact ⟨x, hB x hx⟩
  haveI hfdR : FiniteDimensional ℂ (LinearMap.range B) := by
    rw [hR]
    exact hfd K hKc hKo
  haveI : Nontrivial (LinearMap.range B) := by
    rw [hR]
    exact Submodule.nontrivial_iff_ne_bot.2 hne
  have hrest : (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (hB y (hR ▸ y.2))
  refine ⟨prj (fixU π K) ∘L T₀, A, (Module.finrank ℂ (LinearMap.range B) : ℂ),
    ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ⟨hfdR, ?_⟩, ?_⟩
  · intro D hD hinv v hv
    exact p3 D hD hinv _ (c3 D hD hinv v hv)
  · intro G' _ _ π' hc g v
    show prj (fixU π K) (T₀ (π' g v)) = π' g (prj (fixU π K) (T₀ v))
    rw [c4 G' π' hc, ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1]
  · intro f hf x
    show prj (fixU π K) (T₀ (f x)) = f (e (A₀ x))
    rw [c5 f hf]
    exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf _
  · show LinearMap.trace ℂ (LinearMap.range B) (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = _
    rw [hrest, LinearMap.trace_id]
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
end

