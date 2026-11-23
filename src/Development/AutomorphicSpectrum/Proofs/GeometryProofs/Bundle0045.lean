module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateChartDualAction
section
namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li))
    (hspan : Submodule.span K (D.om : Set (Module.Dual K Li)) = ⊤)
    {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [hspan] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  let : Module A Li := Module.compHom Li (algebraMap A K)
  have : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  have hvW : ∀ g, vec g ∈ latOn D (_root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (_root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add (f := _), mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hF0 : ∀ (e : Wsub) (z : D.omHT (σ.comp c.toRingHom)), ∃ a : A,
      algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
    rintro ⟨e, he⟩ z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
    change algebraMap A K d * (z : Module.Dual K Li) e ∈ (algebraMap A K).range
    rw [← hz', hE e he.1 w]
    exact he.2 w hw
  choose F hF using hF0
  let eval : Wsub →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)) :=
    { toFun := fun e =>
        { toFun := F e
          map_add' := fun x y => hinj <| by
            rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
          map_smul' := fun a x => hinj <| by
            rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul,
              LinearMap.smul_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun x y => by
        ext z
        apply hinj
        change algebraMap A K (F (x + y) z) = algebraMap A K (F x z + F y z)
        rw [map_add, hF, hF, hF, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun a x => by
        ext z
        apply hinj
        change algebraMap A K (F (a • x) z) = algebraMap A K (a * F x z)
        rw [map_mul, hF, hF, Submodule.coe_smul, hsmul, map_smul, smul_eq_mul, mul_left_comm] }
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ eval)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRrS (y : Fin N → K) : Rr y ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ := by
    simp only [Rr, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hvecS _)
  have hRr (y : Fin N → A) (z : D.omHT (σ.comp c.toRingHom)) :
      algebraMap A K d * (z : Module.Dual K Li) (Rr (fun l => algebraMap A K (y l))) =
        algebraMap A K (r y z) := by
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [Rr, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hvec]
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · exact ⟨eval ⟨e, he⟩, hF _, fun l => congrFun (hG ⟨e, he⟩) l⟩
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · let f := eval ⟨e, he⟩
    obtain ⟨w', hw'⟩ := hr f
    have hGe : G e = fun l => algebraMap A K (i f l) := hG ⟨e, he⟩
    let q := (p : K) ^ m
    have hq : q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let e' := q⁻¹ • (Rr (G e) - e)
    have he'S : e' ∈ _root_.GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hRrS _) he.1)
    refine ⟨e', ⟨he'S, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨z, hz⟩ := hmem w hw
      have hzEval : algebraMap A K d * (z : Module.Dual K Li) (Rr (G e) - e) =
          q * algebraMap A K (w' z) := by
        have hf : algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := hF _ _
        rw [map_sub, mul_sub, hGe, hRr, hw', LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, map_add, map_mul, map_pow, map_natCast, ← hf, add_sub_cancel_left]
      refine ⟨w' z, ?_⟩
      rw [← hE e' he'S w, ← hz]
      change algebraMap A K (w' z) = algebraMap A K d * (z : Module.Dual K Li) (q⁻¹ • (Rr (G e) - e))
      rw [map_smul, smul_eq_mul, mul_left_comm, hzEval, inv_mul_cancel_left₀ hq]
    · change Rr (G e) = e + q • (q⁻¹ • (Rr (G e) - e))
      rw [smul_inv_smul₀ hq]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsChartIntegral
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem mem_of_isIntegral_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {v : Ω} (hv : IsIntegral R v)
    (hv0 : v ≠ 0) (hu : v⁻¹ ∈ R) : v ∈ R := by
  obtain ⟨p, hp, hpv⟩ := hv
  have huv : v * v⁻¹ = 1 := mul_inv_cancel₀ hv0
  have key : ∀ i m : ℕ, i ≤ m → v ^ i * v⁻¹ ^ m = v⁻¹ ^ (m - i) := by
    intro i m him
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, Nat.add_sub_cancel_left]
  rw [hp.as_sum] at hpv
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow] at hpv
  generalize p.natDegree = n at hpv
  cases n with
  | zero => simp at hpv
  | succ m =>
    have h2 := congrArg (· * v⁻¹ ^ m) hpv
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [pow_succ, mul_comm (v ^ m) v, mul_assoc, key m m le_rfl, Nat.sub_self, pow_zero, mul_one] at h2
    have e : v = -∑ i ∈ Finset.range (m + 1), algebraMap R Ω (p.coeff i) * v⁻¹ ^ (m - i) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mul_assoc, key i m (by simp at hi; omega)]
    rw [e]
    refine neg_mem (sum_mem fun i _ => mul_mem ?_ (pow_mem hu _))
    exact (p.coeff i).2

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem chRing_join_iff {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    {d n : ℕ} (z : κ ⊕ Fin n → Ω) (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (hc : x c ≠ 0) (a : Ω) :
    a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔
      a ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hrat : ∀ q : κ × (κ ⊕ Fin n), joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) =
      x q.1 / x c * (z q.2 / x c ^ d) := by
    intro q
    simp only [joinCo, RingHom.id_apply, hz c]
    exact mul_div_mul_comm _ _ _ _
  have hT : chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) =
      Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨q, rfl⟩
      dsimp only
      rw [hrat]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨q.1, rfl⟩)) (Algebra.subset_adjoin (Or.inr ⟨q.2, rfl⟩))
    · apply Algebra.adjoin_le
      rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
      · have h1 : joinCo (RingHom.id Ω) x z (j, Sum.inl c) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (j, Sum.inl c))
        rw [hrat, hz c, div_self hd, mul_one] at h1
        exact h1
      · have h1 : joinCo (RingHom.id Ω) x z (c, k) / joinCo (RingHom.id Ω) x z (c, Sum.inl c) ∈
            chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) :=
          Algebra.subset_adjoin (Set.mem_range_self (c, k))
        rw [hrat, div_self hc, one_mul] at h1
        exact h1
  rw [hT]

end GlobalTheory.CompanionTheory.Ar.ChNorm

namespace GlobalTheory.CompanionTheory.Ar.ChNorm

theorem joinCo_div {Ω : Type} [Field Ω] {κ : Type} (x : κ → Ω) {d n : ℕ} (z : κ ⊕ Fin n → Ω)
    (hz : ∀ c, z (Sum.inl c) = x c ^ d) (c : κ) (q : κ × (κ ⊕ Fin n)) :
    joinCo (RingHom.id Ω) x z q / joinCo (RingHom.id Ω) x z (c, Sum.inl c) = x q.1 / x c * (z q.2 / x c ^ d) := by
  simp only [joinCo, RingHom.id_apply, hz c]
  exact mul_div_mul_comm _ _ _ _

theorem join_chart_normalisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (d n : ℕ) (z : κ ⊕ Fin n → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x z)), (∀ c, z (Sum.inl c) = x c ^ d) → (∀ c, x c ≠ 0 → ∀ a : Ω, IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d)) → ∀ c, x c ≠ 0 → (∀ a : Ω, a ∈ chRing o (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) ↔ IsIntegral (chRing o x c) a) ∧ ∀ p' : Cpt M'.ξ, (∀ j, x j / x c ∈ regAt M'.ξ p') → InChart M'.ξ (joinCo (RingHom.id Ω) x z) (c, Sum.inl c) p' := by
  intro o _ Ω _ _ κ _ x d n z M' hz hspan c hc
  have hd : x c ^ d ≠ 0 := pow_ne_zero _ hc
  have hyS : ∀ k, IsIntegral (chRing o x c) (z k / x c ^ d) := fun k =>
    (hspan c hc _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have hxS : ∀ j, x j / x c ∈ chRing o x c := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  refine ⟨fun a => ?_, fun p' hp' => ?_⟩
  · rw [chRing_join_iff x z hz c hc a]
    constructor
    · intro ha
      have hle : Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) ≤
          (integralClosure (chRing o x c) Ω).restrictScalars o := by
        apply Algebra.adjoin_le
        rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2
            (isIntegral_algebraMap (x := (⟨_, hxS j⟩ : chRing o x c))))
        · exact (Subalgebra.mem_restrictScalars o).2 ((mem_integralClosure_iff _ _).2 (hyS k))
      exact (mem_integralClosure_iff _ _).1 ((Subalgebra.mem_restrictScalars o).1 (hle ha))
    · intro ha
      have hSle : chRing o x c ≤
          Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)) :=
        Algebra.adjoin_mono Set.subset_union_left
      refine Submodule.span_induction
        (p := fun b _ => b ∈ Algebra.adjoin o (Set.range (fun j => x j / x c) ∪ Set.range (fun k => z k / x c ^ d)))
        ?_ ?_ ?_ ?_ ((hspan c hc a).1 ha)
      · rintro _ ⟨k, rfl⟩
        exact Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩)
      · exact zero_mem _
      · intro a b _ _ ha hb
        exact add_mem ha hb
      · intro s b _ hb
        rw [Subalgebra.smul_def]
        exact mul_mem (hSle s.2) hb
  · obtain ⟨hctr, l, hl⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.join_points_charts o Ω κ (κ ⊕ Fin n) x Ω (RingHom.id Ω) z M' (fun _ => rfl) p'
    obtain ⟨c', -, hc'⟩ := hctr
    have ho : ∀ r : o, algebraMap o Ω r ∈ regAt M'.ξ p' := fun r =>
      hc' _ (Subalgebra.algebraMap_mem _ r)
    have hSle : ∀ a ∈ chRing o x c, a ∈ regAt M'.ξ p' := by
      intro a ha
      have h1 : a ∈ (chRing o x c).toSubring := ha
      rw [chRing, Algebra.adjoin_eq_ring_closure] at h1
      exact (Subring.closure_le.2 (Set.union_subset (by rintro _ ⟨r, rfl⟩; exact ho r)
        (by rintro _ ⟨j, rfl⟩; exact hp' j))) h1
    let φ : chRing o x c →+* regAt M'.ξ p' :=
      { toFun := fun s => ⟨s, hSle s s.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hvint : IsIntegral (regAt M'.ξ p') (z l / x c ^ d) :=
      IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hyS l)
    obtain ⟨hzl, hzr⟩ := hl
    have hv : z l / x c ^ d ∈ regAt M'.ξ p' :=
      mem_of_isIntegral_of_inv_mem _ hvint (div_ne_zero hzl hd) (by rw [inv_div, ← hz c]; exact hzr _)
    have hy : ∀ k, z k / x c ^ d ∈ regAt M'.ξ p' := fun k => by
      have e : z k / x c ^ d = z k / z l * (z l / x c ^ d) := by field_simp
      rw [e]
      exact mul_mem (hzr k) hv
    refine ⟨?_, fun q => ?_⟩
    · simp only [joinCo, RingHom.id_apply, hz c]
      exact mul_ne_zero hc hd
    · rw [joinCo_div x z hz c q]
      exact mul_mem (hp' q.1) (hy q.2)

end GlobalTheory.CompanionTheory.Ar.ChNorm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmooth
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem smooth_of_away_mvPolynomial {R L ι : Type} [CommRing R] [CommRing L] [Finite ι]
    (g : R →+* L) (ψ : MvPolynomial ι R →+* L) (hg : ψ.comp MvPolynomial.C = g) (f : MvPolynomial ι R)
    (hl : @IsLocalization.Away _ _ f L _ ψ.toAlgebra) : g.Smooth := by
  letI := ψ.toAlgebra
  haveI := hl
  have h1 : ψ.Smooth := (Algebra.Smooth.of_isLocalization_Away f : Algebra.Smooth (MvPolynomial ι R) L)
  have h2 : (algebraMap R (MvPolynomial ι R)).Smooth :=
    RingHom.smooth_algebraMap.2 ⟨inferInstance, inferInstance⟩
  rw [MvPolynomial.algebraMap_eq] at h2
  rw [← hg]
  exact RingHom.Smooth.comp h2 h1

def evalSub {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω) (v : ι → K) :
    MvPolynomial ι R →+* K :=
  MvPolynomial.eval₂Hom ((algebraMap Ω K).comp R.subtype) v

theorem evalSub_injective {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) (hv : AlgebraicIndependent Ω v) : Function.Injective (evalSub R v) := by
  have e : evalSub R v =
      (MvPolynomial.aeval v : MvPolynomial ι Ω →ₐ[Ω] K).toRingHom.comp (MvPolynomial.map R.subtype) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [evalSub]
    · intro i
      simp [evalSub]
  rw [e]
  exact fun p q hpq => MvPolynomial.map_injective _ R.subtype_injective
    (algebraicIndependent_iff_injective_aeval.1 hv hpq)

theorem evalSub_range {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} (R : Subring Ω)
    (v : ι → K) : (evalSub R v).range =
      Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    induction a using MvPolynomial.induction_on with
    | C a =>
      refine Subring.subset_closure (Or.inl ⟨a, a.2, ?_⟩)
      simp [evalSub]
    | add p q hp hq =>
      rw [map_add (f := _)]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subring.subset_closure (Or.inr ⟨i, ?_⟩))
      simp [evalSub]
  · refine Subring.closure_le.2 ?_
    rintro x (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [evalSub]⟩
    · exact ⟨MvPolynomial.X i, by simp [evalSub]⟩

theorem smooth_locSub_closure : ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (R : Subring Ω) (v : ι → K), AlgebraicIndependent Ω v → ∀ ℓ : K, ℓ ∈ Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) → ℓ ≠ 0 → ∀ h : (∀ a ∈ R, algebraMap Ω K a ∈ locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ), (((algebraMap Ω K).comp R.subtype).codRestrict (locSub (Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v)) ℓ) (fun a => h a a.2)).Smooth := by
  intro Ω K _ _ _ ι _ R v hv ℓ hℓ h0 h
  have hr := evalSub_range R v
  generalize Subring.closure (((R.map (algebraMap Ω K) : Subring K) : Set K) ∪ Set.range v) = B at *
  subst hr
  have hinj := evalSub_injective R v hv
  have hmem : ∀ a, evalSub R v a ∈ locSub (evalSub R v).range ℓ :=
    fun a => le_locSub _ _ ⟨a, rfl⟩
  obtain ⟨f, hf⟩ := hℓ
  refine smooth_of_away_mvPolynomial _ ((evalSub R v).codRestrict _ hmem) ?_ f ?_
  · ext a
    change evalSub R v (MvPolynomial.C a) = algebraMap Ω K a
    simp [evalSub]
  · letI := ((evalSub R v).codRestrict _ hmem).toAlgebra
    have hval : ∀ a : MvPolynomial ι R,
        ((algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) a : locSub (evalSub R v).range ℓ) : K)
          = evalSub R v a := fun a => rfl
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨_, n, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial ι R) (locSub (evalSub R v).range ℓ) f) := by
        refine IsUnit.of_mul_eq_one ⟨ℓ⁻¹, inv_mem_locSub _ _⟩ (Subtype.ext ?_)
        simp [hval, hf, h0]
      simpa using hu.pow n
    · rintro ⟨z, hz⟩
      obtain ⟨k, hk⟩ := (mem_locSub_iff (RingHom.mem_range.2 ⟨f, hf⟩) h0 z).1 hz
      obtain ⟨a, ha⟩ := RingHom.mem_range.1 hk
      refine ⟨⟨a, ⟨f ^ k, k, rfl⟩⟩, Subtype.ext ?_⟩
      simp [hval, hf, ha, mul_comm]
    · intro x y hxy
      exact ⟨1, by rw [hinj (congrArg Subtype.val hxy)]⟩

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCodimOneStalkDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem stalk_isDiscreteValuationRing_of_dim_one : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ p : X, ringKrullDim (X.presheaf.stalk p) = 1 → ∃ _ : IsDomain (X.presheaf.stalk p), IsDiscreteValuationRing (X.presheaf.stalk p) :=
  @PositivityTheory.UnitarySelfGeneration.normal_scheme_height_one_stalk_dvr

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElementStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_localization_at_element : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (R : Subring Ω) (a : Ω), IsCptGen ξ → IsPiece ξ U R → a ∈ R → a ≠ 0 → ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_basicOpen_piece <;> assumption)
end

