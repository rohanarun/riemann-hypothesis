module

public import Mathlib

@[expose] public section
set_option maxHeartbeats 8000000

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.CofinalCompl
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.cofinalCompl :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (I J : Ideal R) (n : ℕ), J ^ n ≤ I → I ≤ J → IsAdicComplete I M → IsAdicComplete J M := by
  intro R M _ _ _ I J n hn hIJ hI
  have hle : ∀ k, J ^ ((n + 1) * k) • (⊤ : Submodule R M) ≤ I ^ k • ⊤ := fun k => by
    apply Submodule.smul_mono_left
    calc J ^ ((n + 1) * k) ≤ J ^ (n * k) :=
          Ideal.pow_le_pow_right (Nat.mul_le_mul_right k (Nat.le_succ n))
      _ = (J ^ n) ^ k := pow_mul J n k
      _ ≤ I ^ k := Ideal.pow_right_mono hn k
  have hge : ∀ k, I ^ k • (⊤ : Submodule R M) ≤ J ^ k • ⊤ := fun k =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ k)
  refine
    { haus' := fun x hx => hI.toIsHausdorff.haus' x fun k => (hx ((n + 1) * k)).mono (hle k)
      prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' (fun k => f ((n + 1) * k))
    (fun {a b} hab => (hf (Nat.mul_le_mul_left (n + 1) hab)).mono (hle a))
  refine ⟨L, fun m => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left m (Nat.succ_pos n))).trans ((hL m).mono (hge m))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
section
open IsLocalRing

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec (I := I) inferInstance (f := fun n => f n i) (fun {m n} hmn => ?_)
    have := (mem_smul_top_pi (I ^ m) _).1 (SModEq.sub_mem.1 (hf hmn)) i
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have := SModEq.sub_mem.1 (hL i n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa using this

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  have hmap : ∀ n, Submodule.map π (I ^ n • ⊤) = I ^ n • (⊤ : Submodule R M) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hπ]
  refine ⟨fun f hf => ?_⟩
  have hd : ∀ n, ∃ y ∈ (I ^ n • ⊤ : Submodule R (Fin r → R)), π y = f (n + 1) - f n := by
    intro n
    have : f (n + 1) - f n ∈ Submodule.map π (I ^ n • ⊤) := by
      rw [hmap]
      exact SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm
    exact Submodule.mem_map.1 this
  choose d hdI hdπ using hd
  obtain ⟨g0, hg0⟩ := hπ (f 0)
  have hgπ : ∀ n, π (g0 + ∑ k ∈ Finset.range n, d k) = f n := by
    intro n
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, map_add (f := _), ih, hdπ]
      abel
  have hcau : ∀ {m n : ℕ}, m ≤ n → (g0 + ∑ k ∈ Finset.range m, d k) ≡
      (g0 + ∑ k ∈ Finset.range n, d k) [SMOD (I ^ m • ⊤ : Submodule R (Fin r → R))] := by
    intro m n hmn
    rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
    have e : g0 + ∑ k ∈ Finset.range m, d k
        - (g0 + (∑ k ∈ Finset.range m, d k + ∑ k ∈ Finset.Ico m n, d k))
        = -∑ k ∈ Finset.Ico m n, d k := by abel
    rw [e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.1 hk).1) (hdI k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
    (f := fun n => g0 + ∑ k ∈ Finset.range n, d k) hcau
  refine ⟨π L, fun n => ?_⟩
  rw [← hgπ n, SModEq.sub_mem, ← map_sub, ← hmap n]
  exact Submodule.mem_map_of_mem (SModEq.sub_mem.1 (hL n))

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl :
    ∀ (Λ M : Type) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M], IsAdicComplete I M := by
  intro Λ M _ _ I _ _ _ _
  exact
    { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
      toIsPrecomplete := isPrecomplete_finite I }
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinMax
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finMax :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T], Finite (MaximalSpectrum T) ∧ (∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ ∧ (Finite (ResidueField Λ) → Finite (T ⧸ m))) ∧ ∃ n : ℕ, (⊥ : Ideal T).jacobson ^ n ≤ (maximalIdeal Λ).map (algebraMap Λ T) ∧ (maximalIdeal Λ).map (algebraMap Λ T) ≤ (⊥ : Ideal T).jacobson := by
  intro Λ T _ _ _ _ _
  let I : Ideal T := (maximalIdeal Λ).map (algebraMap Λ T)
  have h1 : Module.Finite Λ (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ Λ I).toLinearMap Ideal.Quotient.mk_surjective
  have h2 : Module.Finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  have h0 : IsArtinianRing (Λ ⧸ maximalIdeal Λ) := by
    letI := Ideal.Quotient.field (maximalIdeal Λ)
    infer_instance
  have h3 : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (Λ ⧸ maximalIdeal Λ) (T ⧸ I)
  have hcomap : ∀ m : Ideal T, m.IsMaximal → m.comap (algebraMap Λ T) = maximalIdeal Λ := by
    intro m hm
    haveI := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Λ) m
    exact IsLocalRing.eq_maximalIdeal this
  have hIm : ∀ m : Ideal T, m.IsMaximal → I ≤ m := fun m hm =>
    Ideal.map_le_iff_le_comap.2 (hcomap m hm).ge
  have hker : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  refine ⟨?_, ?_, ?_⟩
  · let f : MaximalSpectrum (T ⧸ I) → MaximalSpectrum T := fun p =>
      ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
    apply Finite.of_surjective f
    intro m
    have hcm : (m.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = m.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        hker]
      exact sup_eq_left.2 (hIm _ m.isMaximal)
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective m.isMaximal with h | h
    · exfalso
      apply m.isMaximal.ne_top
      rw [← hcm, h, Ideal.comap_top]
    · exact ⟨⟨_, h⟩, MaximalSpectrum.ext hcm⟩
  · intro m hm
    refine ⟨hcomap m hm, fun hk => ?_⟩
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := hk
    haveI : Finite (T ⧸ I) := Module.finite_of_finite (Λ ⧸ maximalIdeal Λ)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective (hIm m hm))
  · obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T ⧸ I)
    refine ⟨n, ?_, ?_⟩
    · have hJ : (⊥ : Ideal T).jacobson.map (Ideal.Quotient.mk I) ≤ (⊥ : Ideal (T ⧸ I)).jacobson := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_jacobson_bot]
        intro y
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add (f := _)]
        exact (Ideal.mem_jacobson_bot.1 hx y).map _
      intro x hx
      have hx' : Ideal.Quotient.mk I x ∈ ((⊥ : Ideal (T ⧸ I)).jacobson) ^ n := by
        apply Ideal.pow_right_mono hJ n
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hx
      rw [hn] at hx'
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hx'
    · rw [Ideal.jacobson]
      refine le_sInf ?_
      rintro m ⟨-, hm⟩
      exact hIm m hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.InvMem
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.invMem :
    ∀ (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (S : Subalgebra Λ (Module.End Λ M)) (u : (Module.End Λ M)ˣ), (u : Module.End Λ M) ∈ S → ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ∈ S := by
  intro Λ M _ _ _ _ S u hu
  obtain ⟨p, hp, hpv⟩ :=
    LinearMap.exists_monic_and_aeval_eq_zero Λ ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M)
  have key : ∀ n i, i ≤ n → (u : Module.End Λ M) ^ n *
      ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = (u : Module.End Λ M) ^ (n - i) := by
    intro n i hi
    have h1 : (u : Module.End Λ M) ^ i * ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv]
    rw [← pow_sub_mul_pow (u : Module.End Λ M) hi, mul_assoc, h1, mul_one]
  rw [Polynomial.aeval_eq_sum_range] at hpv
  cases h : p.natDegree with
  | zero =>
    have hc : p.coeff 0 = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_one, hc, one_smul, pow_zero] at hpv
    have hz : ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) = 0 := by
      rw [← mul_one ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M), hpv, mul_zero]
    rw [hz]
    exact S.zero_mem
  | succ n =>
    have hc : p.coeff (n + 1) = 1 := by rw [← h]; exact hp.coeff_natDegree
    rw [h, Finset.sum_range_succ, hc, one_smul] at hpv
    have hmul := congrArg (fun w => (u : Module.End Λ M) ^ n * w) hpv
    rw [mul_add, Finset.mul_sum, mul_zero] at hmul
    have hlast : (u : Module.End Λ M) ^ n *
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ (n + 1) =
        ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) := by
      rw [pow_succ, ← mul_assoc, key n n le_rfl, Nat.sub_self, pow_zero, one_mul]
    rw [hlast] at hmul
    have hterm : ∀ i ∈ Finset.range (n + 1), (u : Module.End Λ M) ^ n *
        (p.coeff i • ((u⁻¹ : (Module.End Λ M)ˣ) : Module.End Λ M) ^ i) =
        p.coeff i • (u : Module.End Λ M) ^ (n - i) := by
      intro i hi
      rw [mul_smul_comm, key n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
    rw [Finset.sum_congr rfl hterm] at hmul
    rw [eq_neg_of_add_eq_zero_right hmul]
    exact S.neg_mem (S.sum_mem fun i _ => S.smul_mem (S.pow_mem hu _) _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.IsOrdProjZeroOfIsNilpotent
section
namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

section Ord

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

def ordPart (U : Module.End R M) : Submodule R M := ⨅ n : ℕ, LinearMap.range (U ^ n)

theorem mem_ordPart {U : Module.End R M} {x : M} : x ∈ ordPart U ↔ ∀ n : ℕ, ∃ y, (U ^ n) y = x := by
  simp [ordPart, Submodule.mem_iInf]

theorem map_mem_smul_top {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (J : Ideal R)
    {x : M} (hx : x ∈ (J • ⊤ : Submodule R M)) : f x ∈ (J • ⊤ : Submodule R N) := by
  have h1 := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

def nilPart (I : Ideal R) (U : Module.End R M) : Submodule R M where
  carrier := {x | ∀ k : ℕ, ∃ n : ℕ, (U ^ n) x ∈ (I ^ k • ⊤ : Submodule R M)}
  zero_mem' := fun k => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy k
    obtain ⟨n, hn⟩ := hx k
    obtain ⟨m, hm⟩ := hy k
    refine ⟨n + m, ?_⟩
    rw [map_add (f := _)]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hn
    · rw [pow_add, Module.End.mul_apply]; exact map_mem_smul_top _ _ hm
  smul_mem' := by
    intro c x hx k
    obtain ⟨n, hn⟩ := hx k
    exact ⟨n, by rw [map_smul]; exact Submodule.smul_mem _ _ hn⟩

structure IsOrdProj (I : Ideal R) (U e : Module.End R M) : Prop where
  idem : IsIdempotentElem e
  comm : Commute U e
  bij : Set.BijOn U (LinearMap.range e) (LinearMap.range e)
  nil : ∀ k : ℕ, ∃ n : ℕ, ∀ x, (U ^ n) (x - e x) ∈ (I ^ k • ⊤ : Submodule R M)

def IsFactLim (I : Ideal R) (U e : Module.End R M) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ x, (U ^ j.factorial) x - e x ∈ (I ^ k • ⊤ : Submodule R M)


open Classical in
noncomputable def ordProj (I : Ideal R) (U : Module.End R M) : Module.End R M :=
  by
    classical
    exact if h : ∃ e, IsOrdProj I U e then h.choose else 0

theorem isOrdProj_ordProj {I : Ideal R} {U : Module.End R M} (h : ∃ e, IsOrdProj I U e) :
    IsOrdProj I U (ordProj I U) := by
  unfold ordProj
  rw [dite_eq_left h]
  exact h.choose_spec


variable (M) in
structure OrdAdm (I : Ideal R) : Prop where
  complete : IsAdicComplete I M
  finLen : ∀ k : ℕ, IsFiniteLength R (M ⧸ (I ^ k • ⊤ : Submodule R M))

end Ord

section Map

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
  {M : Type*} [AddCommGroup M] [Module A M]
  {M' : Type*} [AddCommGroup M'] [Module A M'] [Module A' M'] [IsScalarTower A A' M']

theorem pow_intertwine {U : Module.End A M} {U' : Module.End A' M'} {f : M →ₗ[A] M'}
    (h : ∀ x, f (U x) = U' (f x)) (n : ℕ) (x : M) : f ((U ^ n) x) = (U' ^ n) (f x) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

end Map

section Lim

variable {R : Type*} [CommRing R] {P : ℕ → Type*} [∀ b, AddCommGroup (P b)] [∀ b, Module R (P b)]
  {Q : ℕ → Type*} [∀ b, AddCommGroup (Q b)] [∀ b, Module R (Q b)]

end Lim

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocChar
section
open IsLocalRing

private theorem map_mem_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) {x : N} (hx : x ∈ J • (⊤ : Submodule R N)) :
    f x ∈ J • (⊤ : Submodule R N) := by
  have h1 : f x ∈ (J • (⊤ : Submodule R N)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

private theorem pow_mem_pow_smul_top {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (J : Ideal R) (f : Module.End R N) (hf : ∀ x, f x ∈ J • (⊤ : Submodule R N)) (k : ℕ) :
    ∀ x, (f ^ k) x ∈ J ^ k • (⊤ : Submodule R N) := by
  induction k with
  | zero =>
    intro x
    simp
  | succ k ih =>
    intro x
    rw [pow_succ' f k, Module.End.mul_apply, pow_succ J k, Submodule.mul_smul]
    have h1 : f ((f ^ k) x) ∈ (J ^ k • (⊤ : Submodule R N)).map f :=
      Submodule.mem_map_of_mem (ih x)
    rw [Submodule.map_smul''] at h1
    refine Submodule.smul_mono le_rfl ?_ h1
    rintro _ ⟨z, _, rfl⟩
    exact hf z

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar :
    ∀ (R N T ι : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup N] [Module R N] [Module.Finite R N] [CommRing T] (ρ : T →+* Module.End R N) (I : Ideal T) (u : ι → T) (e : T), (∀ μ ∈ I, ∀ x, ρ μ x ∈ maximalIdeal R • (⊤ : Submodule R N)) → IsIdempotentElem e → (∀ i, ∃ n : ℕ, u i ^ n * e ∈ I) → 1 - e ∈ I ⊔ Ideal.span (Set.range u) → ∀ x, ρ e x = x ↔ ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (ρ (u i) ^ n) x ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
  intro R N T ι _ _ _ _ _ _ _ ρ I u e hI he hu hspan x
  have hP : ∀ (k : ℕ) (t : T) {z : N}, z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) →
      ρ t z ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) :=
    fun k t z hz => _root_.map_mem_smul_top _ (ρ t) hz
  constructor
  · intro hx i k
    obtain ⟨n, hn⟩ := hu i
    have hek : ∀ j : ℕ, ρ (e ^ j) x = x := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, map_mul, Module.End.mul_apply, hx, ih]
    refine ⟨n * k, ?_⟩
    have hmem := pow_mem_pow_smul_top (maximalIdeal R) (ρ (u i ^ n * e)) (hI _ hn) k x
    have heq : (ρ (u i) ^ (n * k)) x = (ρ (u i ^ n * e) ^ k) x := by
      rw [← map_pow, ← map_pow, mul_pow, ← pow_mul, map_mul, Module.End.mul_apply, hek k]
    rw [heq]
    exact hmem
  · intro h
    obtain ⟨y, hy⟩ : ∃ y, y = ρ (1 - e) x := ⟨_, rfl⟩
    have hyk : ∀ k : ℕ, y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := by
      intro k
      let S : Ideal T :=
        { carrier := {t | ρ t y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)}
          add_mem' := fun {a b} ha hb => by
            show ρ (a + b) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_add (f := _), LinearMap.add_apply]
            exact add_mem ha hb
          zero_mem' := by
            show ρ 0 y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_zero, LinearMap.zero_apply]
            exact zero_mem _
          smul_mem' := fun c t ht => by
            show ρ (c * t) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
            rw [map_mul, Module.End.mul_apply]
            exact hP k c ht }
      have hrad : I ⊔ Ideal.span (Set.range u) ≤ S.radical := by
        refine sup_le (fun μ hμ => Ideal.mem_radical_iff.mpr ⟨k, ?_⟩) (Ideal.span_le.mpr ?_)
        · show ρ (μ ^ k) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          rw [map_pow]
          exact pow_mem_pow_smul_top _ (ρ μ) (hI μ hμ) k y
        · rintro _ ⟨i, rfl⟩
          obtain ⟨n, hn⟩ := h i k
          refine Ideal.mem_radical_iff.mpr ⟨n, ?_⟩
          show ρ (u i ^ n) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N)
          have hc : ρ (u i ^ n) y = ρ (1 - e) ((ρ (u i) ^ n) x) := by
            rw [hy, ← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
              ← map_mul, mul_comm]
          rw [hc]
          exact hP k _ hn
      obtain ⟨K, hK⟩ := Ideal.mem_radical_iff.mp (hrad hspan)
      have hKy : ρ ((1 - e) ^ K) y = y := by
        rw [hy, ← Module.End.mul_apply, ← map_mul, ← pow_succ, he.one_sub.pow_succ_eq]
      have hK' : ρ ((1 - e) ^ K) y ∈ maximalIdeal R ^ k • (⊤ : Submodule R N) := hK
      rwa [hKy] at hK'
    have hy0 : y = 0 := IsHausdorff.haus inferInstance y (fun k => SModEq.zero.mpr (hyk k))
    rw [hy, map_sub, map_one, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy0
    exact hy0.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.SepIffInjective
section
namespace UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

variable {O R K : Type*} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K]

def Sep (Y : Set (R →ₐ[O] K)) : Prop := ∀ f : R, (∀ y ∈ Y, y f = 0) → f = 0

end UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
end

