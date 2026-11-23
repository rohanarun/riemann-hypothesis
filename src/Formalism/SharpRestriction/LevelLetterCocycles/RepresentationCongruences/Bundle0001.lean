module

public import Mathlib
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CoeffRelation
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries

theorem coeff_relation {O : Type*} [CommRing O] [IsDomain O] {d₁ d : ℕ} (p : O) (hp : p ≠ 0)
    (F : Fin d₁ → O⟦X⟧) (μ : Fin d₁ → Fin d → O) (k₀ : Fin d) (K s S h k : ℕ) (Q : O⟦X⟧)
    (hk : k < h) (hkS : S ≤ k)
    (heq : ∀ j : Fin d, ∃ R : O⟦X⟧,
      C p ^ K * (∑ m, F m * C (μ m j) - (if j = k₀ then C p ^ s * X ^ S * Q else 0)) = X ^ h * R) :
    ∀ j, ∑ m, coeff k (F m) * μ m j = if j = k₀ then p ^ s * coeff (k - S) Q else 0 := by
  intro j
  obtain ⟨R, hR⟩ := heq j
  have h1 : coeff k (C p ^ K * (∑ m, F m * C (μ m j) -
      (if j = k₀ then C p ^ s * X ^ S * Q else 0))) = 0 := by
    rw [hR, coeff_X_pow_mul', if_neg (by omega)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_pow, coeff_C_mul, map_sub, map_sum, coeff_mul_C] at h1
  have h2 := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hp))
  rw [h2]
  split_ifs with hj
  · simp [← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', hkS]
  · exact map_zero _

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.EqZeroOfForallMemCoeffFiltration
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

open PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

def T (O : Type*) [CommRing O] [IsLocalRing O] (N : ℕ) : Ideal O⟦X⟧ where
  carrier := {x | ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m)}
  add_mem' {a b} ha hb m := by
    simpa only [map_add (f := _)] using Ideal.add_mem _ (ha m) (hb m)
  zero_mem' m := by simp
  smul_mem' c x hx m := by
    rw [smul_eq_mul, coeff_mul]
    refine Submodule.sum_mem _ fun p hp => Ideal.mul_mem_left _ _ ?_
    have h2 : p.2 ≤ m := by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega
    exact Ideal.pow_le_pow_right (by omega) (hx p.2)

theorem mem_T {N : ℕ} {x : O⟦X⟧} :
    x ∈ T O N ↔ ∀ m, coeff m x ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := Iff.rfl

theorem T_anti {N N' : ℕ} (h : N ≤ N') : T O N' ≤ T O N := by
  intro x hx
  rw [mem_T] at hx ⊢
  exact fun m => Ideal.pow_le_pow_right (by omega) (hx m)

theorem T_mul {a b : ℕ} {x y : O⟦X⟧} (hx : x ∈ T O a) (hy : y ∈ T O b) : x * y ∈ T O (a + b) := by
  rw [mem_T] at hx hy ⊢
  intro m
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h2 := Ideal.mul_mem_mul (hx p.1) (hy p.2)
  rw [← pow_add] at h2
  exact Ideal.pow_le_pow_right (by omega) h2

private theorem maximalIdeal_pow_smul_whole_ring_eq_self (n : ℕ) :
    ((IsLocalRing.maximalIdeal O) ^ n • ⊤ : Submodule O O) = (IsLocalRing.maximalIdeal O) ^ n := by
  first
    | rw [Ideal.smul_eq_mul, Ideal.mul_top]
    | simp [Ideal.smul_eq_mul]
    | simp

theorem eq_zero_of_forall_mem_coeffFiltration {x : O⟦X⟧} (hx : ∀ N, x ∈ T O N) : x = 0 := by
  have H : IsHausdorff (IsLocalRing.maximalIdeal O) O := inferInstance
  ext m
  rw [map_zero]
  refine H.haus _ fun n => ?_
  rw [SModEq.zero, maximalIdeal_pow_smul_whole_ring_eq_self]
  have h := (mem_T.mp (hx (n + m))) m
  rwa [Nat.add_sub_cancel] at h

variable {g : O⟦X⟧}

theorem mem_T_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : g ∈ T O 1 := by
  rw [mem_T]
  intro m
  rcases m with _ | m
  · rw [Nat.sub_zero, pow_one, coeff_zero_eq_constantCoeff_apply]
    exact hg
  · rw [show 1 - (m + 1) = 0 by omega, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem pow_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (N : ℕ) : g ^ N ∈ T O N := by
  induction N with
  | zero =>
    rw [pow_zero, mem_T]
    intro m
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    rw [pow_succ]
    exact T_mul ih (mem_T_one hg)

theorem aeval_mem_coeffFiltration (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) {N : ℕ} {p : Polynomial O}
    (hp : ∀ d < N, p.coeff d = 0) : Polynomial.aeval g p ∈ T O N := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun d _ => ?_
  by_cases hd : d < N
  · rw [hp d hd, zero_smul]
    exact Submodule.zero_mem _
  · rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _
      (T_anti (not_lt.mp hd) (pow_mem_coeffFiltration hg d))

noncomputable def S (g : O⟦X⟧) (N : ℕ) (f : O⟦X⟧) : O⟦X⟧ := Polynomial.aeval g (trunc N f)

theorem S_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) {N N' : ℕ}
    (h : N ≤ N') : S g N' f - S g N f ∈ T O N := by
  unfold S
  rw [← map_sub (Polynomial.aeval (R := O) g)]
  refine aeval_mem_coeffFiltration hg fun d hd => ?_
  have hd' : d < N' := lt_of_lt_of_le hd h
  simp [coeff_trunc, hd, hd']

theorem exists_lim (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (m : ℕ) :
    ∃ L : O, ∀ N, coeff m (S g N f) - L ∈ (IsLocalRing.maximalIdeal O) ^ (N - m) := by
  have hC : IsPrecomplete (IsLocalRing.maximalIdeal O) O := inferInstance
  obtain ⟨L, hL⟩ := hC.prec (f := fun k => coeff m (S g (k + m) f)) (fun {a b} hab => by
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self]
    have h1 := S_sub_mem hg f (show a + m ≤ b + m by omega) m
    rw [map_sub, Nat.add_sub_cancel] at h1
    have h2 := neg_mem h1
    rw [neg_sub] at h2
    exact h2)
  refine ⟨L, fun N => ?_⟩
  rcases le_or_gt m N with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    have h3 := hL k
    rw [SModEq.sub_mem, maximalIdeal_pow_smul_whole_ring_eq_self] at h3
    rw [Nat.add_sub_cancel]
    exact h3
  · rw [Nat.sub_eq_zero_of_le h.le, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

noncomputable def subst (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) : O⟦X⟧ :=
  PowerSeries.mk fun m => Classical.choose (exists_lim hg f m)

theorem subst_sub_mem (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f : O⟦X⟧) (N : ℕ) :
    subst hg f - S g N f ∈ T O N := by
  rw [mem_T]
  intro m
  rw [map_sub]
  simp only [subst, coeff_mk]
  have h1 := Classical.choose_spec (exists_lim hg f m) N
  have h2 := neg_mem h1
  rwa [neg_sub] at h2

theorem subst_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f y : O⟦X⟧) (N0 : ℕ)
    (hy : ∀ N, N0 ≤ N → y - S g N f ∈ T O N) : y = subst hg f := by
  have key : ∀ N, y - subst hg f ∈ T O N := fun N => by
    have h1 := hy (N + N0) (by omega)
    have h2 := subst_sub_mem hg f (N + N0)
    have h3 := sub_mem h1 h2
    rw [sub_sub_sub_cancel_right] at h3
    exact T_anti (by omega) h3
  exact sub_eq_zero.mp (eq_zero_of_forall_mem_coeffFiltration key)

private theorem truncEval_add (N : ℕ) (f f' : O⟦X⟧) :
    S g N (f + f') = S g N f + S g N f' := by
  have h : trunc N (f + f') = trunc N f + trunc N f' := map_add (trunc N) f f'
  simp only [S, h, map_add (f := _)]

theorem subst_add (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f + f') = subst hg f + subst hg f' := by
  refine (subst_eq hg (f + f') _ 0 fun N _ => ?_).symm
  rw [truncEval_add, add_sub_add_comm]
  exact add_mem (subst_sub_mem hg f N) (subst_sub_mem hg f' N)

private theorem truncEval_smul (N : ℕ) (r : O) (f : O⟦X⟧) :
    S g N (r • f) = r • S g N f := by
  have h : trunc N (r • f) = r • trunc N f := by
    first
      | exact map_smul (trunc N) r f
      | (ext d; simp only [coeff_trunc, Polynomial.coeff_smul, coeff_smul]; split_ifs <;> simp)
  simp only [S, h, map_smul]

theorem subst_smul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (r : O) (f : O⟦X⟧) :
    subst hg (r • f) = r • subst hg f := by
  refine (subst_eq hg (r • f) _ 0 fun N _ => ?_).symm
  rw [truncEval_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ r (subst_sub_mem hg f N)

private theorem coeff_trunc_mul_trunc_of_lt {N d : ℕ} (hd : d < N) (f f' : O⟦X⟧) :
    (trunc N f * trunc N f').coeff d = coeff d (f * f') := by
  rw [Polynomial.coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have h1 : x.1 < N := by omega
  have h2 : x.2 < N := by omega
  simp [coeff_trunc, h1, h2]

theorem subst_mul (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) (f f' : O⟦X⟧) :
    subst hg (f * f') = subst hg f * subst hg f' := by
  refine (subst_eq hg (f * f') _ 0 fun N _ => ?_).symm
  have hA := subst_sub_mem hg f N
  have hB := subst_sub_mem hg f' N
  have hT : S g N f * S g N f' - S g N (f * f') ∈ T O N := by
    unfold S
    rw [← map_mul (Polynomial.aeval (R := O) g), ← map_sub (Polynomial.aeval (R := O) g)]
    refine aeval_mem_coeffFiltration hg fun d hd => ?_
    rw [Polynomial.coeff_sub, coeff_trunc_mul_trunc_of_lt hd]
    simp [coeff_trunc, hd]
  have key : subst hg f * subst hg f' - S g N (f * f') =
      (subst hg f - S g N f) * subst hg f' +
        S g N f * (subst hg f' - S g N f') +
        (S g N f * S g N f' - S g N (f * f')) := by ring
  rw [key]
  exact add_mem (add_mem (Ideal.mul_mem_right _ _ hA) (Ideal.mul_mem_left _ _ hB)) hT

theorem subst_one (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (1 : O⟦X⟧) = 1 := by
  refine (subst_eq hg 1 1 1 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_one, map_one, sub_self]
  exact Submodule.zero_mem _

theorem subst_X (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : subst hg (X : O⟦X⟧) = g := by
  refine (subst_eq hg X g 2 fun N hN => ?_).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [S, trunc_X, Polynomial.aeval_X, sub_self]
  exact Submodule.zero_mem _

noncomputable def substAlgHom (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) : O⟦X⟧ →ₐ[O] O⟦X⟧ :=
  AlgHom.ofLinearMap
    { toFun := subst hg
      map_add' := subst_add hg
      map_smul' := subst_smul hg }
    (subst_one hg) (subst_mul hg)

theorem exists_algHom_X_eq (hg : constantCoeff g ∈ IsLocalRing.maximalIdeal O) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g := ⟨substAlgHom hg, subst_X hg⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsGLLatBasisOfIsSplitEquiv
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTA

open PowerSeries

variable {O : Type*} [CommRing O]

theorem alg_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  have e : (C a : O⟦X⟧) = algebraMap O O⟦X⟧ a := by
    first
    | rfl
    | simp
    | (rw [PowerSeries.algebraMap_apply']; rfl)
  rw [e, AlgHom.commutes]

private theorem exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one (l : ℕ) (x y : O⟦X⟧)
    (hx : constantCoeff x = 1) (hy : constantCoeff y = 1) :
    ∃ S : O⟦X⟧, constantCoeff S = l ∧ x ^ l - y ^ l = S * (x - y) := by
  refine ⟨∑ i ∈ Finset.range l, x ^ i * y ^ (l - 1 - i), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp [map_sum, hx, hy]
  · first
    | exact (geom_sum₂_mul x y l).symm
    | exact ((Commute.all x y).geom_sum₂_mul l).symm

theorem exists_GL_latBasis_of_isSplitEquiv (l : ℕ) :
    ∃ Q0 : O⟦X⟧, constantCoeff Q0 = l ∧ (1 + X : O⟦X⟧) ^ l - 1 = X * Q0 := by
  obtain ⟨S, hS, e⟩ := exists_pow_sub_pow_eq_mul_sub_of_constantCoeff_eq_one l (1 + X : O⟦X⟧) 1 (by simp) (by simp)
  exact ⟨S, hS, by linear_combination e⟩

variable [IsDomain O] [CharZero O]

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTA
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsSumPadicValIntWindowEq
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Finset

theorem padicValNat_factorial_add_sum (l : ℕ) [Fact l.Prime] (m S : ℕ) :
    padicValNat l m.factorial + ∑ j ∈ range S, padicValNat l (m + 1 + j) =
      padicValNat l (m + S).factorial := by
  induction S with
  | zero => simp
  | succ n ih =>
    have h1 : (m + (n + 1)).factorial = (m + n + 1) * (m + n).factorial := by
      rw [show m + (n + 1) = m + n + 1 by omega, Nat.factorial_succ]
    have h2 : padicValNat l ((m + n + 1) * (m + n).factorial) =
        padicValNat l (m + n + 1) + padicValNat l (m + n).factorial :=
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (by omega) (Nat.factorial_ne_zero _)
    rw [Finset.sum_range_succ, h1, h2, show m + 1 + n = m + n + 1 by omega]
    omega

theorem padicValNat_factorial_le_div_sub_one' (l : ℕ) [hp : Fact l.Prime] (n : ℕ) :
    (padicValNat l n.factorial : ℝ) ≤ n / ((l : ℝ) - 1) := by
  have hl : 2 ≤ l := hp.out.two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have key := Nat.Prime.sub_one_mul_multiplicity_factorial (n := n) hp.out
  have hle : (l - 1) * padicValNat l n.factorial ≤ n := by
    rw [Nat.padicValNat_def, key]; exact Nat.sub_le _ _
  have hcast : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h' : ((l : ℝ) - 1) * (padicValNat l n.factorial : ℝ) ≤ n := by
    rw [← hcast]; exact_mod_cast hle
  rw [le_div_iff₀ hlR]
  linarith [mul_comm ((l : ℝ) - 1) (padicValNat l n.factorial : ℝ)]

private theorem sum_Ico_int_eq_sum_range_add (a : ℤ) (S : ℕ) (f : ℤ → ℕ) :
    ∑ i ∈ Finset.Ico a (a + S), f i = ∑ j ∈ range S, f (a + j) := by
  induction S with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Ico a (a + ((n + 1 : ℕ) : ℤ)) = insert (a + n) (Finset.Ico a (a + n)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Ico]
      push_cast
      constructor <;> intro h <;> omega
    rw [hI, Finset.sum_insert (by simp), ih, Finset.sum_range_succ, add_comm]

theorem exists_sum_padicValInt_window_eq (l : ℕ) (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ∃ m : ℕ, m + S ≤ N ∧ ∑ i ∈ Finset.Ico a (a + S), padicValInt l i =
      ∑ j ∈ range S, padicValNat l (m + 1 + j) := by
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · exact ⟨0, by simp, by simp⟩
  have hfirst := ha a (by simp only [Finset.mem_Ico]; omega)
  have hlast := ha (a + S - 1) (by simp only [Finset.mem_Ico]; omega)
  rw [sum_Ico_int_eq_sum_range_add]
  rcases lt_or_gt_of_ne hfirst.1 with hneg | hpos
  · have hend : a + S ≤ 0 := by
      by_contra hc
      have h0 := ha 0 (by simp only [Finset.mem_Ico]; omega)
      exact h0.1 rfl
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ -a - S by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hfirst.2).1
      omega
    · rw [← Finset.sum_range_reflect (fun j => padicValNat l (m + 1 + j)) S]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have he : a + (j : ℤ) = -(((m + 1 + (S - 1 - j) : ℕ)) : ℤ) := by omega
      rw [padicValInt, he, Int.natAbs_neg]
      rw [Int.natAbs_natCast, ← Nat.padicValNat_def]
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ a - 1 by omega)
    refine ⟨m, ?_, ?_⟩
    · have := (abs_le.mp hlast.2).2
      omega
    · apply Finset.sum_congr rfl
      intro j _
      have he : a + (j : ℤ) = ((m + 1 + j : ℕ) : ℤ) := by push_cast; omega
      rw [padicValInt, he]
      rw [Int.natAbs_natCast, ← Nat.padicValNat_def]

theorem sum_padicValInt_window_le (l : ℕ) [Fact l.Prime] (a : ℤ) (S N : ℕ)
    (ha : ∀ i ∈ Finset.Ico a (a + S), i ≠ 0 ∧ |i| ≤ (N : ℤ)) :
    ((∑ i ∈ Finset.Ico a (a + S), padicValInt l i : ℕ) : ℝ) ≤ N / ((l : ℝ) - 1) := by
  obtain ⟨m, hmN, heq⟩ := exists_sum_padicValInt_window_eq l a S N ha
  rw [heq]
  have h1 := padicValNat_factorial_add_sum l m S
  have h2 := padicValNat_factorial_le_div_sub_one' l (m + S)
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlR : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have h3n : ∑ j ∈ range S, padicValNat l (m + 1 + j) ≤ padicValNat l (m + S).factorial := by
    omega
  have h3 : ((∑ j ∈ range S, padicValNat l (m + 1 + j) : ℕ) : ℝ) ≤
      (padicValNat l (m + S).factorial : ℝ) := by exact_mod_cast h3n
  have h4 : ((m + S : ℕ) : ℝ) / ((l : ℝ) - 1) ≤ N / ((l : ℝ) - 1) := by
    rw [le_div_iff₀ hlR, div_mul_cancel₀ _ hlR.ne']
    exact_mod_cast hmN
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Imports
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb

open Finset

theorem split {R : Type*} [CommRing R] (π q l : R) (hq : q = π + l) (e B r : ℕ) :
    π ^ (r + 1) * q ^ (e * (r + 1)) =
      (∑ k ∈ (range (r + 1)).filter (fun k => k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1))) +
      π * q ^ B * ∑ k ∈ (range (r + 1)).filter (fun k => ¬ k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B) := by
  have hπ : π = q + (-l) := by rw [hq]; ring
  have h1 : π ^ (r + 1) * q ^ (e * (r + 1)) = π * q ^ (e * (r + 1)) * (q + (-l)) ^ r := by
    rw [← hπ]; ring
  rw [h1, add_pow, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (range (r + 1))
    (fun k => k + e * (r + 1) < B), Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : B ≤ k + e * (r + 1) := by
      simp only [Finset.mem_filter] at hk
      omega
    have hq' : q ^ (k + e * (r + 1)) = q ^ B * q ^ (k + e * (r + 1) - B) := by
      rw [← pow_add]; congr 1; omega
    rw [neg_pow]
    calc π * q ^ (e * (r + 1)) * (q ^ k * ((-1) ^ (r - k) * l ^ (r - k)) * (r.choose k : R))
        = (-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1)) := by ring
      _ = π * q ^ B * ((-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B)) := by
        rw [hq']; ring

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InvSubOneSqLeInv
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities

variable {x : ℝ}

lemma p_le (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 1 / 10 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 10 - (x - 1)⁻¹ = (x - 11) / (10 * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 10 - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h1.le)
  linarith

lemma q_le (hx : 11 ≤ x) : x / (x - 1) ^ 2 ≤ 121 / 100 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by norm_num) h0.le) (sq_nonneg _))
  linarith

lemma p_le_u (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 11 / 10 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 10 * x⁻¹ - (x - 1)⁻¹ = (x - 11) / (10 * x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 10 * x⁻¹ - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h1.le)
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities
end

