module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_keep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Submodule ℂ H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, ∀ v ∈ Y, a v ∈ Y) → ∀ v, (v ∈ Y ∨ ∃ a ∈ l, ∀ v, a v ∈ Y) → l.prod v ∈ Y
  | [], _, v, h => by simpa using h
  | a :: l, hl, v, h => by
    rw [List.prod_cons]
    show a (l.prod v) ∈ Y
    have ih := prod_keep Y l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) v
    rcases h with h | ⟨b, hb, h⟩
    · exact hl a List.mem_cons_self _ (ih (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h _
      · exact hl a List.mem_cons_self _ (ih (Or.inr ⟨b, hb, h⟩))

theorem UpperTheory.mem_fixedVectors_of_product_of_compactOpen :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : ∀ i, UnitaryRep (G i) H) (Z : Submodule ℂ H) (L : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → ∀ v ∈ Z, (List.ofFn T).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ π Z L T h1 h2 h3 v hv
  have k1 : ∀ i j, ∀ v ∈ fixU (π j) (L j), T i v ∈ fixU (π j) (L j) := fun i j v hv u hu => by
    by_cases e : i = j
    · subst e; exact h1 i v u hu
    · rw [← h3 i j e, hv u hu]
  refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun j => ?_⟩
  · exact prod_keep Z _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h2 i) v (Or.inl hv)
  · exact prod_keep _ _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact k1 i j) v
      (Or.inr ⟨T j, List.mem_ofFn.2 ⟨j, rfl⟩, h1 j⟩)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.SummandLeClosureSpanLocalTypeImages
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open GroundTheory.Automorphic.AutomorphicForm

private theorem adelicSplit {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (u : AdelicGLn.FiniteAdelicGL K n) :
    ∃ (a : Gw n w) (h : AdelicGLn.FiniteAdelicGL K n), u = AdelicGLn.localEmbedding w a * h ∧
      ∀ g : Gw n w, AdelicGLn.localEmbedding w g * h = h * AdelicGLn.localEmbedding w g := by
  obtain ⟨-, h2, -, -, h5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  refine ⟨finAt w (finEmb K n u), (AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u, ?_, ?_⟩
  · rw [mul_inv_cancel_left]
  · refine h5 _ ?_
    have e : finAt w (finEmb K n (AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))) *
        finAt w (finEmb K n ((AdelicGLn.localEmbedding w (finAt w (finEmb K n u)))⁻¹ * u)) =
        finAt w (finEmb K n u) := by
      rw [← finAt_mul, ← map_mul, mul_inv_cancel_left]
    rw [h2] at e
    exact mul_left_cancel (e.trans (mul_one _).symm)

private theorem eqv_translate {L G H S : Type} [Group L] [TopologicalSpace L] [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (τ : Representation ℂ L S) (ρ : UnitaryRep L H) (π : UnitaryRep G H) (D : Submodule ℂ H) (hD : π.IsInvariant D)
    (j : L → G) (hρ : ∀ g v, ρ g v = π (j g) v) (c : G) (hc : ∀ g, c * j g = j g * c) (f : S →ₗ[ℂ] H) (hf : Eqv τ ρ D f)
    (a : L) (y : S) : π (c * j a) (f y) ∈ spanAll τ ρ D := by
  have hE : Eqv τ ρ D (((π c : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ f) := by
    refine ⟨fun y => hD c _ (hf.mem y), fun g y => ?_⟩
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hf.map, hρ, hρ, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, hc g]
  have hx : π (c * j a) (f y) = (((π c : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ f) (τ a y) := by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hf.map, hρ, UnitaryRep.map_mul_apply]
  rw [hx]
  exact Submodule.subset_span ⟨_, hE, _, rfl⟩

private theorem exists_factor {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (x : normOneGL (K := K) (n := n)) :
    ∃ (c : normOneGL (K := K) (n := n)) (a : Gw n w), x = c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w a) ∧
      ∀ g : Gw n w, c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) =
        MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) * c := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj x
  obtain ⟨a, h, rfl, hc⟩ := adelicSplit w u
  refine ⟨archProj K n A * MultiplicityOne.finProj K n h, a, ?_, fun g => ?_⟩
  · rw [hc a, map_mul, mul_assoc]
  · rw [mul_assoc, ← map_mul, ← hc g, map_mul, ← mul_assoc, ← mul_assoc,
      MultiplicityOne.finProj_mul_archProj_comm]

private theorem dense_of_invariant {G H S L : Type} [Group G] [TopologicalSpace G] [Group L] [TopologicalSpace L]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (π : UnitaryRep G H) (W V : Submodule ℂ H) (hV : IsSummandOf π W V) (τ : Representation ℂ L S) (ρ : UnitaryRep L H)
    (f : S →ₗ[ℂ] H) (hf0 : f ≠ 0) (hf : Eqv τ ρ V f) (hinv : π.IsInvariant (spanAll τ ρ V)) :
    V ≤ (spanAll τ ρ V).topologicalClosure := by
  have hle : spanAll τ ρ V ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', hf', x, rfl⟩
    exact hf'.mem x
  have hCle : (spanAll τ ρ V).topologicalClosure ≤ V :=
    Submodule.topologicalClosure_minimal _ hle hV.closed
  have hne : (spanAll τ ρ V).topologicalClosure ≠ ⊥ := by
    intro hbot
    apply hf0
    refine LinearMap.ext fun x => ?_
    have h1 : f x ∈ (spanAll τ ρ V).topologicalClosure :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, x, rfl⟩)
    rw [hbot] at h1
    simpa using h1
  rcases hV.irred _ hCle (Submodule.isClosed_topologicalClosure _) hinv.topologicalClosure with h | h
  · exact absurd h hne
  · exact h.ge

private theorem invariant_of_translate {L G H S : Type} [Group L] [TopologicalSpace L] [Group G] [TopologicalSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S]
    (τ : Representation ℂ L S) (ρ : UnitaryRep L H) (π : UnitaryRep G H) (D : Submodule ℂ H)
    (h : ∀ x f, Eqv τ ρ D f → ∀ y, π x (f y) ∈ spanAll τ ρ D) : π.IsInvariant (spanAll τ ρ D) := by
  intro x v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨f', hf', y, rfl⟩ := hv
    exact h x f' hf' y
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private theorem locU_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (g : Gw n w) (v : LL μ) :
    locU μ w g v = rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v := by
  rw [locU_apply]
  rfl

theorem UpperTheory.summand_le_closure_span_local_type_images :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) (w : Pl K) (σ : SmIrr (Gw n w)), IsSummand μ V → Occurs μ V w σ → V ≤ (spanAll σ.ρ (locU μ w) V).topologicalClosure := by
  intro K _ _ n μ _ V w σ hV hO
  obtain ⟨f, hf0, hfm, hfe⟩ := hO
  have hf : Eqv σ.ρ (locU μ w) V f := ⟨hfm, fun g x => by rw [hfe, locU_apply]⟩
  refine dense_of_invariant (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) (cuspidalL2 μ) V hV σ.ρ (locU μ w) f hf0 hf ?_
  refine invariant_of_translate σ.ρ (locU μ w) _ V fun x f' hf' y => ?_
  obtain ⟨c, a, rfl, hc⟩ := exists_factor w x
  exact eqv_translate σ.ρ (locU μ w) (rightRegularRep (rationalGLOne (K := K) (n := n)) μ) V (IsSummandOf.inv hV)
    (fun g => MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) (locU_eq μ w) c hc f' hf' a y
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TrOnEqMulOfEqSmulOnSubspace
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Submodule ℂ H) (B C : H →L[ℂ] H) (c : ℂ),
        FiniteDimensional ℂ W → (∀ v ∈ W, B v = c • C v) → trOn W B = c * trOn W C := by
  intro H _ _ _ W B C c hW h
  haveI := hW
  have hcl : W.topologicalClosure = W :=
    (Submodule.closed_of_finiteDimensional W).submodule_topologicalClosure_eq
  have hmem : ∀ x, UpperTheory.ConvolutionTheory.C.prj W x ∈ W := by
    intro x
    have hx : UpperTheory.ConvolutionTheory.C.prj W x ∈ W.topologicalClosure := by
      simp [UpperTheory.ConvolutionTheory.C.prj]
    rwa [hcl] at hx
  simp only [UpperTheory.ConvolutionTheory.C.trOn, GroundTheory.Automorphic.trace]
  rw [← tsum_mul_left]
  refine tsum_congr fun i => ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [h _ (hmem _), map_smul, inner_smul_right]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TrOnRestrictAndEqOfMapsInto
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : UpperTheory.ConvolutionTheory.C.prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold UpperTheory.ConvolutionTheory.C.prj
  congr 1

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjection : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    UpperTheory.ConvolutionTheory.C.trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, UpperTheory.ConvolutionTheory.C.trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert (preTransparency := .reducible) h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem trOn_of_restrict (E : Submodule ℂ H) [FiniteDimensional ℂ E] (B : H →L[ℂ] H) (b : Module.End ℂ E)
    (hb : ∀ v : E, ((b v : E) : H) = B v) : UpperTheory.ConvolutionTheory.C.trOn E B = LinearMap.trace ℂ E b := by
  rw [trOn_eq]
  congr 1
  ext v
  rw [cprs_coe, ← hb, Submodule.starProjection_eq_self_iff.2 (b v).2]

end SlopeTestRemainingChoices

theorem UpperTheory.trOn_restrict_and_eq_of_maps_into :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (X Y : Submodule ℂ H) [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] (B : H →L[ℂ] H), (∀ b : Module.End ℂ X, (∀ v : X, ((b v : X) : H) = B v) → trOn X B = LinearMap.trace ℂ X b) ∧ (X ≤ Y → (∀ v ∈ Y, B v ∈ X) → trOn Y B = trOn X B) := by
  intro H _ _ _ X Y _ _ B
  refine ⟨fun b hb => trOn_of_restrict X B b hb, fun hXY hY => ?_⟩
  let p : Y →ₗ[ℂ] X := LinearMap.codRestrict X ((B : H →ₗ[ℂ] H) ∘ₗ Y.subtype) fun v => hY v v.2
  let i : X →ₗ[ℂ] Y := Submodule.inclusion hXY
  rw [trOn_of_restrict Y B (i ∘ₗ p) fun v => rfl, trOn_of_restrict X B (p ∘ₗ i) fun v => rfl]
  exact LinearMap.trace_comp_comm' p i
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TraceRestrictEqOfHasFinTrace
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.trace_restrict_eq_of_hasFinTrace :
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (Q Q' : Submodule ℂ S) [FiniteDimensional ℂ Q'] (g : S →ₗ[ℂ] S) (t : ℂ) (m : Module.End ℂ Q') (e : Q' →ₗ[ℂ] S), Q ≤ Q' → HasFinTrace g t → (∀ x, g x ∈ Q) → (∀ x : Q', ((m x : Q') : S) = g (e x)) → (∀ x : Q', (x : S) ∈ Q → e x = x) → LinearMap.trace ℂ Q' m = t := by
  intro S _ _ Q Q' _ g t m e hQ hg hgQ hm he
  obtain ⟨hfd, hr⟩ := hg
  haveI := hfd
  have hWQ : LinearMap.range g ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hgQ x
  let p : Q' →ₗ[ℂ] LinearMap.range g :=
    (g ∘ₗ e).codRestrict (LinearMap.range g) fun x => LinearMap.mem_range_self g (e x)
  let q : LinearMap.range g →ₗ[ℂ] Q' := Submodule.inclusion (hWQ.trans hQ)
  have e1 : m = q ∘ₗ p := by
    ext x
    exact hm x
  have e2 : g.restrict (p := LinearMap.range g) (q := LinearMap.range g)
      (fun v _ => LinearMap.mem_range_self g v) = p ∘ₗ q := by
    ext x
    exact congrArg g (he (q x) (hWQ x.2)).symm
  rw [e1, LinearMap.trace_comp_comm', ← e2, hr]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.UiwPowCompEqOfAntitone
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

private theorem iw_scale {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure]
    (ν : Fin n → ℤ) (T : LL μ →L[ℂ] LL μ) (hT : IsOloc μ w m ((iwCoset w ν).indicator 1) T) :
    T = (((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal : ℝ) : ℂ) • Uiw μ w ν := by
  have hCO : CO (GLnLocal.iwahori (w.adicCompletion K) n) :=
    ⟨GLnLocal.isCompact_iwahori _ n, GLnLocal.isOpen_iwahori _ n⟩
  have h0 : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ 0 :=
    (hCO.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) ≠ ⊤ := hCO.1.measure_lt_top.ne
  obtain ⟨d, hd⟩ : ∃ d, d = (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)))⁻¹ := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := hd ▸ ENNReal.inv_ne_zero.2 ht
  have hdt : d ≠ ⊤ := hd ▸ ENNReal.inv_ne_top.2 h0
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w)) = 1 := by
    rw [Measure.smul_apply, hd, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hop := UpperTheory.ConvolutionTheory.C.hopOloc K n μ w (d • m) (GLnLocal.iwahori (w.adicCompletion K) n)
    (Cartan.diagPow (w.adicCompletion K) n ν) hCO h1
  have hc : (m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩
  have hdc : d.toReal = ((m (GLnLocal.iwahori (w.adicCompletion K) n : Set (Gw n w))).toReal)⁻¹ := by
    rw [hd, ENNReal.toReal_inv]
  ext1 v
  refine ext_inner_left ℂ fun u => ?_
  have e1 : ⟪u, Uiw μ w ν v⟫_ℂ = d.toReal • ∫ g, (iwCoset w ν).indicator 1 g * ⟪u, rhoL μ w g v⟫_ℂ ∂m := by
    have := hop u v
    rw [integral_smul_measure] at this
    exact this
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, e1, hT u v, hdc, Complex.real_smul, ← mul_assoc,
    Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hc), one_mul]

theorem UpperTheory.Uiw_pow_comp_eq_of_antitone :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)]
        (m : Measure (Gw n w)) [m.IsHaarMeasure] (e : Fin n → ℤ) (j : ℕ) (T T' : LL μ →L[ℂ] LL μ), Antitone e →
        IsOloc μ w m ((iwCoset w 0).indicator 1) T → IsOloc μ w m ((iwCoset w (j • e)).indicator 1) T' →
        (Uiw μ w e ^ j) ∘L T = T' := by
  intro K _ _ n μ _ w _ _ m _ e j T T' he hT hT'
  have h0 : prj (fixL μ w (GLnLocal.iwahori (w.adicCompletion K) n)) = Uiw μ w 0 := by
    have := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he 0
    rw [pow_zero, zero_smul] at this
    exact this
  have h1 := UpperTheory.ConvolutionTheory.C.uiwPow K n μ w e he j
  rw [iw_scale μ w m 0 T hT, iw_scale μ w m _ T' hT', ← h0, ← h1]
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
end

