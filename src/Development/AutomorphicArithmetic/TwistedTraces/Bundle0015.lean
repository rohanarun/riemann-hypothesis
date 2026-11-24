module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistYA
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0008
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0009
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0012
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.GaloisTwistCommuteArchOperatorAndOffProjection
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

set_option maxHeartbeats 1600000 in
theorem UpperTheory.galoisTwist_commute_archOperator_and_offProjection :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ,
        ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
        ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
          (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
        ∀ (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀),
          Commute θ.U (Oinf μ νE aE) ∧ Commute θ.U (prj (offN μ T)) := by
  intro F E _ _ _ _ _ _ σ hσ k n μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ T
  obtain ⟨tp1, -, tp3⟩ := twistPerm F E σ hσ k n μ θ hθ
  refine ⟨?_, tp3 q w₀ T (nsS T : Set (Pl F))⟩
  obtain ⟨-, -, ag3, -⟩ := archBasic F E σ k D n
  let O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a
  have hOi : Oinf μ νE aE = (List.ofFn O).prod :=
    tensOp F E σ k D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens
  have hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h) := fun i j hij g h => by
    rw [hposition, hposition]
    show _ * _ = _ * _
    rw [← ag3, ← ag3]
    exact congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (k + 1) => archGroup F n) hij g h).eq
  have hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s i g)))) →
      Commute B (O i) := fun B i h => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v
  have hrep : ∀ x y : normOneGL (K := E) (n := n), Commute x y →
      Commute (rightRegularRep (rationalGLOne (K := E) (n := n)) μ x) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ y) := fun x y h =>
    ContinuousLinearMap.ext fun v => by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]
  have hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s j g))) :=
    fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm
  have hOO : ∀ i j, Commute (O i) (O j) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact hOc _ j (hOa i j e)
  have hUO : ∀ i, θ.U * O (i + 1) = O i * θ.U := fun i => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) v
  have key : ∀ l : List (Fin (k + 1)), θ.U * (l.map fun i => O (i + 1)).prod = (l.map O).prod * θ.U := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, hUO, mul_assoc, ih, mul_assoc]
  have hperm : (List.ofFn fun i => O (i + 1)).prod = (List.ofFn O).prod := by
    refine List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm (Equiv.addRight (1 : Fin (k + 1))) O) ?_
    rw [List.ofFn_eq_map, List.pairwise_map]
    exact List.pairwise_of_forall fun x y => hOO _ _
  have h := key (List.finRange (k + 1))
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, hperm] at h
  rw [hOi]
  exact h
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.IsotypicMultiplicityTensorProduct
section
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_multiplicity_tensor_product :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
  by_cases hZ : Z = ⊥
  · refine ⟨0, fun U T A t hU _ _ _ _ _ _ => ?_⟩
    have hb : (Z ⊓ ⨅ i, fixU (π i) (U i)) = ⊥ := by rw [hZ, bot_inf_eq]
    haveI := hadm U hU
    rw [zero_mul, (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i))
      ((List.ofFn T).prod ∘L R)).1 0 ?_, map_zero]
    intro v
    have hv0 : (v : H) = 0 := by
      have h : ∀ w ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), w = 0 := by
        rw [hb]
        simp
      exact h _ v.2
    simp [hv0]
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hZ
  obtain ⟨hS, -⟩ := UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm hZ
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmF : ∀ i (L U : Subgroup (G i)), L ≤ U → ∀ v ∈ fixU (π i) U, v ∈ fixU (π i) L :=
    fun i L U h v hv u hu => hv u (h hu)
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hSK : ∀ i (K : Subgroup (G i)), IsCompact (K : Set (G i)) → IsOpen (K : Set (G i)) →
      FiniteDimensional ℂ (fixedVectors (τ i) K) := by
    intro i K hc ho
    have h := hS (Function.update U₀ i K) (fun j => by
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        exact ⟨hc, ho⟩
      · rw [Function.update_of_ne e]
        exact hU₀ j) i
    rwa [Function.update_self] at h
  haveI hfd0 : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) := hadm U₀ hU₀
  obtain ⟨h1, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV U₀ hU₀ hfd0 h0
  have hex := fun i => UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (s i) (I i) (hI i)
    (hSK i) (U₀ i) (hU₀ i).1 (hU₀ i).2 (h1 i).2
  choose T₀ A₀ t₀ hP ht₀ ht₀0 using hex
  have a1 : ∀ i v, T₀ i v ∈ fixU (π i) (U₀ i) := fun i => (hP i).1
  have a2 : ∀ i, ∀ x, A₀ i x ∈ fixedVectors (τ i) (U₀ i) := fun i => (hP i).2.1
  have a3 : ∀ i, ∀ v ∈ Z, T₀ i v ∈ Z := fun i => (hP i).2.2.1 Z hZc (hZi i)
  have a4 : ∀ i j, i ≠ j → ∀ h v, T₀ i (π j h v) = π j h (T₀ i v) := fun i j hij =>
    (hP i).2.2.2.1 (G j) (π j) (hcm i j hij)
  have a5 : ∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T₀ i (f x) = f (A₀ i x) := fun i => (hP i).2.2.2.2
  have hprod : (∏ i, t₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht₀0 i
  obtain ⟨κ₀, hκ₀⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI U₀ hU₀ h0
  refine ⟨κ₀, fun U T A t hU b1 b3 b4 b5 b2 bt => ?_⟩
  have hL : ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hle0 := hmono (fun i => U i ⊓ U₀ i) U₀ fun i => inf_le_right
  have hleU := hmono (fun i => U i ⊓ U₀ i) U fun i => inf_le_left
  have hneL : (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun e => h0 (le_bot_iff.1 (e ▸ hle0))
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) := hadm _ hL
  haveI hfdU : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) := hadm U hU
  obtain ⟨κ, hκ⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
    (fun i => U i ⊓ U₀ i) hL hneL
  have e1 := hκ T₀ A₀ t₀ (fun i v => hmF i _ _ inf_le_right _ (a1 i v)) a3 a4 a5
    (fun i x => hmS i _ _ inf_le_right (a2 i x)) ht₀
  have e2 := hκ₀ T₀ A₀ t₀ a1 a3 a4 a5 a2 ht₀
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T₀).prod ∘L R)).2 hle0 fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U₀ T₀ a1 a3 a4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  have hκκ : κ = κ₀ := mul_right_cancel₀ hprod (by rw [← e1, ← e2, e3])
  have e4 := hκ T A t (fun i v => hmF i _ _ inf_le_left _ (b1 i v)) b3 b4 b5
    (fun i x => hmS i _ _ inf_le_left (b2 i x)) bt
  have e5 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T).prod ∘L R)).2 hleU fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U T b1 b3 b4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  rw [← e5, e4, hκκ]
end

