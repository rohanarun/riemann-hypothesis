module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactModuleTopology
section
open Polynomial TensorProduct

noncomputable section

namespace GlobalTheory.JR.EtExist

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def conjAlg [h : Unram F E] : E →ₐ[F] E :=
  { starRingEnd E with commutes' := fun x => h.star_fix x }

theorem conjAlg_apply [Unram F E] (y : E) : conjAlg F E y = star y := rfl

variable (K : Type) [CommRing K] [Algebra F K]

def conjT [Unram F E] : E ⊗[F] K →ₐ[F] E ⊗[F] K := Algebra.TensorProduct.map (conjAlg F E) (AlgHom.id F K)

theorem conjT_conjT [Unram F E] (z : E ⊗[F] K) : conjT F E K (conjT F E K z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjT, conjAlg_apply]
  | add a b ha hb => simp [ha, hb]

@[reducible] def starT [Unram F E] : StarRing (E ⊗[F] K) where
  star := conjT F E K
  star_involutive := conjT_conjT F E K
  star_mul a b := by
    change conjT F E K (a * b) = conjT F E K b * conjT F E K a
    rw [map_mul, mul_comm]
  star_add a b := map_add (conjT F E K) a b

theorem locallyCompact_moduleTopology [LocallyCompactSpace F] [Module.Finite F K] :
    @LocallyCompactSpace K (moduleTopology F K) := by
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  let b := (Module.finBasis F K).equivFun
  have h1 : Continuous b := IsModuleTopology.continuous_of_linearMap b.toLinearMap
  haveI : ContinuousAdd K := IsModuleTopology.toContinuousAdd F K
  have h2 : Continuous b.symm := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  let e : K ≃ₜ (Fin (Module.finrank F K) → F) := { b.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  exact e.isClosedEmbedding.locallyCompactSpace

def ofAlgebra [h : Unram F E] [Module.Finite F K] [IsReduced K] : Et F E :=
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[F] K) := moduleTopology F (E ⊗[F] K)
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  { K := K
    L := E ⊗[F] K
    trK := IsModuleTopology.isTopologicalRing F K
    lcK := haveI := h.lcF; locallyCompact_moduleTopology F K
    mK := borel K
    bK := @BorelSpace.mk _ _ (borel K) rfl
    stL := starT F E K
    mtL := ⟨rfl⟩
    mL := borel (E ⊗[F] K)
    bL := @BorelSpace.mk _ _ (borel (E ⊗[F] K)) rfl
    push := inferInstance
    star_K := fun x => by
      change conjT F E K (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [conjT]
    star_E := fun y => by
      change conjT F E K (y ⊗ₜ 1) = star y ⊗ₜ 1
      simp [conjT, conjAlg_apply] }

theorem exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  set P : F[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : F[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite F (AdjoinRoot P) := pb.finite
  haveI : IsReduced (AdjoinRoot P) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      ((isRadical_iff_span_singleton).1 hs.squarefree.isRadical)
  refine ⟨ofAlgebra F E (AdjoinRoot P), AdjoinRoot.root P, ?_, ?_, ?_⟩
  · change LinearIndependent F (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ))
    have := pb.basis.linearIndependent.comp (Fin.cast (show r = pb.dim from hd.symm)) (Fin.cast_injective _)
    have e : (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ)) = pb.basis ∘ Fin.cast (show r = pb.dim from hd.symm) := by
      funext i
      rw [Function.comp_apply, pb.basis_eq_pow]
      rfl
    rw [e]; exact this
  · change Module.finrank F (AdjoinRoot P) = r
    rw [pb.finrank]; exact hd
  · change AdjoinRoot.root P ^ r + ∑ i, p i • AdjoinRoot.root P ^ (i : ℕ) = 0
    have := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at this
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]) = 0 := this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    simpa only [Algebra.smul_def] using h2

end GlobalTheory.JR.EtExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyConstantCompactSupportSlicesOperatorApply
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem slices_test {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P]
    [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ) (hT : ∀ φ, IsTest φ → IsTest (T φ)) (hT0 : T 0 = 0)
    (f : P × V × Q → ℂ) (hf : IsTest f) :
    (∀ p q, IsTest (fun v => f (p, v, q))) ∧
      IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) := by
  obtain ⟨hlc, hcs⟩ := hf
  have hC : IsCompact (tsupport f) := hcs
  have hz : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have h1 : ∀ p q, IsTest (fun v => f (p, v, q)) := by
    intro p q
    refine ⟨hlc.comp_continuous (by fun_prop), ?_⟩
    have hcl : IsClosed ({x : P × V × Q | x.1 = p} ∩ {x | x.2.2 = q}) :=
      (isClosed_eq continuous_fst continuous_const).inter
        (isClosed_eq (continuous_snd.comp continuous_snd) continuous_const)
    refine HasCompactSupport.intro ((hC.inter_right hcl).image (continuous_fst.comp continuous_snd)) ?_
    intro v hv
    apply hz
    intro hmem
    exact hv ⟨(p, v, q), ⟨hmem, rfl, rfl⟩, rfl⟩
  refine ⟨h1, ?_⟩
  set Φ : P × Q → V → ℂ := fun a v => f (a.1, v, a.2) with hΦdef
  set CV : Set V := (fun x : P × V × Q => x.2.1) '' tsupport f with hCV
  have hCVc : IsCompact CV := hC.image (continuous_fst.comp continuous_snd)
  have hoff : ∀ (a : P × Q) v, v ∉ CV → f (a.1, v, a.2) = 0 := by
    intro a v hv
    exact hz _ (fun h => hv ⟨_, h, rfl⟩)
  have hΦ : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a0
    have hn : IsOpen {z : (P × Q) × V | f (z.1.1, z.2, z.1.2) = f (a0.1, z.2, a0.2)} := by
      have g1 : IsLocallyConstant (fun z : (P × Q) × V => f (z.1.1, z.2, z.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have g2 : IsLocallyConstant (fun z : (P × Q) × V => f (a0.1, z.2, a0.2)) :=
        hlc.comp_continuous (by fun_prop)
      refine isOpen_iff_mem_nhds.2 fun z hz' => ?_
      filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 g1 z, (IsLocallyConstant.iff_eventually_eq _).1 g2 z]
        with y hy1 hy2
      show f (y.1.1, y.2, y.1.2) = f (a0.1, y.2, a0.2)
      rw [hy1, hy2]
      exact hz'
    obtain ⟨u, w, hu, -, hau, hCVw, huw⟩ :=
      generalized_tube_lemma (isCompact_singleton (x := a0)) hCVc hn (by
        rintro ⟨a, v⟩ ⟨ha, -⟩
        rw [Set.mem_singleton_iff] at ha
        subst ha
        rfl)
    filter_upwards [hu.mem_nhds (hau rfl)] with a ha
    funext v
    by_cases hv : v ∈ CV
    · exact huw (show (a, v) ∈ u ×ˢ w from ⟨ha, hCVw hv⟩)
    · show f (a.1, v, a.2) = f (a0.1, v, a0.2)
      rw [hoff a v hv, hoff a0 v hv]
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x0
    have e1 : ∀ᶠ x in 𝓝 x0, Φ (x.1, x.2.2) = Φ (x0.1, x0.2.2) :=
      ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 hΦ _)
    have e2 : ∀ᶠ x in 𝓝 x0, T (Φ (x0.1, x0.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1 :=
      ((continuous_fst.comp continuous_snd).tendsto x0).eventually
        ((IsLocallyConstant.iff_eventually_eq _).1 (hT _ (h1 _ _)).1 _)
    filter_upwards [e1, e2] with x h h'
    show T (Φ (x.1, x.2.2)) x.2.1 = T (Φ (x0.1, x0.2.2)) x0.2.1
    rw [h]
    exact h'
  · set K : Set (P × Q) := (fun x : P × V × Q => (x.1, x.2.2)) '' tsupport f with hKdef
    have hK : IsCompact K := hC.image (by fun_prop)
    have hΦK : ∀ a, a ∉ K → Φ a = 0 := by
      intro a ha
      funext v
      exact hz _ (fun h => ha ⟨_, h, rfl⟩)
    haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
    have hfin : (Set.range (fun a : K => Φ a)).Finite :=
      (hΦ.comp_continuous continuous_subtype_val).range_finite
    set U : Set V := ⋃ h ∈ Set.range (fun a : K => Φ a), tsupport (T h) with hUdef
    have hU : IsCompact U := hfin.isCompact_biUnion (fun h hh => by
      obtain ⟨a, rfl⟩ := hh
      exact (hT _ (h1 _ _)).2.isCompact)
    have hL : IsCompact ((fun z : (P × Q) × V => (z.1.1, z.2, z.1.2)) '' (K ×ˢ U)) :=
      (hK.prod hU).image (by fun_prop)
    refine HasCompactSupport.intro hL ?_
    intro x hx
    by_contra hne
    apply hx
    have ha : (x.1, x.2.2) ∈ K := by
      by_contra hK'
      apply hne
      show T (Φ (x.1, x.2.2)) x.2.1 = 0
      rw [hΦK _ hK', hT0]
      rfl
    refine ⟨((x.1, x.2.2), x.2.1), ⟨ha, ?_⟩, rfl⟩
    exact Set.mem_biUnion ⟨⟨(x.1, x.2.2), ha⟩, rfl⟩ (subset_tsupport _ hne)

theorem slices_test' : ∀ {P V Q : Type} [TopologicalSpace P] [TopologicalSpace V] [TopologicalSpace Q] [T2Space P] [T2Space V] [T2Space Q] (T : (V → ℂ) → V → ℂ), (∀ φ, IsTest φ → IsTest (T φ)) → T 0 = 0 → ∀ f : P × V × Q → ℂ, IsTest f → (∀ p q, IsTest (fun v => f (p, v, q))) ∧ IsTest (fun x : P × V × Q => T (fun v => f (x.1, v, x.2.2)) x.2.1) :=
  fun T hT hT0 f hf => slices_test T hT hT0 f hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAdjoinOfMulEqOne
section
namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  exact GlobalTheory.UnitLemma.UnitBase.mem_adjoin_of_mul_eq_one' h ht

theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  classical
  let b := Module.Free.chooseBasis K.E B.A
  have hsm : ∀ (e : K.E) (y : B.A), B.σ (e • y) = K.c e • B.σ y := by
    intro e y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  have hli : LinearIndependent K.E ((B.σ : B.A →+ B.A) ∘ b) := by
    refine b.linearIndependent.map_of_injective_injective (fun r => K.c.symm r) (B.σ : B.A →+ B.A) ?_ ?_ ?_
    · intro r hr
      simpa using hr
    · intro m hm
      have : B.σ m = 0 := hm
      simpa using this
    · intro r m
      show B.σ (K.c.symm r • m) = r • B.σ m
      rw [hsm, RingEquiv.apply_symm_apply]
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range ((B.σ : B.A →+ B.A) ∘ b)) := by
    intro y _
    have h1 : y = ∑ j, K.c (b.repr (B.σ.symm y) j) • B.σ (b j) := by
      conv_lhs => rw [← B.σ.apply_symm_apply y, ← b.sum_repr (B.σ.symm y)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hsm _ _
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K.E B.A) K.E B.A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = B.σ (b i) := fun i => by
    simp only [b', Module.Basis.mk_apply]
    rfl
  have hrepr : ∀ y i, b'.repr (B.σ y) i = K.c (b.repr y i) := by
    intro y i
    have h1 : B.σ y = ∑ j, K.c (b.repr y j) • b' j := by
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hsm, hb']
    rw [h1, b'.repr_sum_self]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [hb', ← map_mul, hrepr]

theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := _root_.GlobalTheory.UnitLemma.UnitBase.exists_unit_base K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := mem_adjoin_of_mul_eq_one hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, Units.val_mul, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)

def mulMat {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' ((j : A.L →ₗ[E] (Fin r → E)) ∘ₗ LinearMap.mulLeft E y ∘ₗ (j.symm : (Fin r → E) →ₗ[E] A.L))

theorem mulMat_mulVec {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y : A.L) (v : Fin r → E) :
    A.mulMat j y *ᵥ v = j (y * j.symm v) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem mulMat_mulVec_apply {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y z : A.L) :
    A.mulMat j y *ᵥ j z = j (y * z) := by
  simp [mulMat_mulVec]

theorem mulMat_mul {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) (y y' : A.L) :
    A.mulMat j (y * y') = A.mulMat j y * A.mulMat j y' := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulMat_mulVec, LinearEquiv.symm_apply_apply, mul_assoc]

theorem mulMat_one {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) : A.mulMat j 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [mulMat_mulVec]

theorem mulMat_mem_unitaryGroup {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j)
    (t : unitary A.L) : A.mulMat j t ∈ Matrix.unitaryGroup (Fin r) E := by
  rw [Matrix.mem_unitaryGroup_iff']
  set N := star (A.mulMat j t) * A.mulMat j t
  have key : ∀ v w : Fin r → E, star v ⬝ᵥ (N *ᵥ w) = star v ⬝ᵥ w := by
    intro v w
    obtain ⟨a, rfl⟩ := j.surjective v
    obtain ⟨b, rfl⟩ := j.surjective w
    have h1 : star (j a) ⬝ᵥ (N *ᵥ j b) = star (A.mulMat j t *ᵥ j a) ⬝ᵥ (A.mulMat j t *ᵥ j b) := by
      simp only [N, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    rw [h1, mulMat_mulVec_apply, mulMat_mulVec_apply, hx, hx]
    congr 1
    have ht : star (t : A.L) * t = 1 := Unitary.star_mul_self_of_mem t.2
    calc algebraMap A.K A.L x * star ((t : A.L) * a) * ((t : A.L) * b)
        = algebraMap A.K A.L x * star a * b * (star (t : A.L) * t) := by rw [star_mul]; ring
      _ = _ := by rw [ht, mul_one]
  have hw : ∀ w, N *ᵥ w = w := by
    intro w
    funext i
    have := key (Pi.single i 1) w
    simpa [single_dotProduct] using this
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  simp [hw]

def uHom {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) :
    unitary A.L →* Matrix.unitaryGroup (Fin r) E where
  toFun t := ⟨A.mulMat j t, A.mulMat_mem_unitaryGroup hx t⟩
  map_one' := by ext1; simp [mulMat_one]
  map_mul' t t' := by ext1; simp [mulMat_mul]

theorem uHom_apply {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (t : unitary A.L) :
    (A.uHom hx t : Matrix (Fin r) (Fin r) E) = A.mulMat j t := rfl

def descFn {r : ℕ} (M : GlobalTheory.JR.Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E))
    (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ) (f : Hn r F E → ℂ) (y : A.L) : ℂ :=
  letI := M.mU
  ∫ g, f (actU g (Ax, j y, lam)) * (α g : ℂ) ∂M.μU

end GlobalTheory.JR.Et
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_norms_trace_uniformizer_facts : ∀ (K : UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u → ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧ (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧ (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧ ∀ x : K.E, val K.O (K.c x) = val K.O x := by
  first | exact @GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | exact GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts | (intros; apply GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts <;> assumption)
end

