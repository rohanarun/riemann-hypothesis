module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ConstantCoeffAlgHom
section
noncomputable section

open PowerSeries

namespace Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation

variable {O : Type*} [CommRing O]

theorem coeff_X_pow_mul_lt {n d : ℕ} (h : d < n) (p : PowerSeries O) :
    coeff d (X ^ n * p) = 0 := by
  first
  | rw [PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr h)]
  | (rw [mul_comm, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr h)])
  | simp [PowerSeries.coeff_X_pow_mul', not_le.mpr h]

theorem coeff_pow_mul_lt {Y : PowerSeries O} (hY : constantCoeff Y = 0) {n d : ℕ} (h : d < n)
    (p : PowerSeries O) : coeff d (Y ^ n * p) = 0 := by
  obtain ⟨Z, rfl⟩ := PowerSeries.X_dvd_iff.mpr hY
  rw [mul_pow, mul_assoc]
  exact coeff_X_pow_mul_lt h _

theorem trunc_decomp (a : PowerSeries O) (k : ℕ) :
    ∃ b, a = (trunc k a : PowerSeries O) + X ^ k * b := by
  have hd : (X : PowerSeries O) ^ k ∣ a - (trunc k a : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := hd
  exact ⟨b, by rw [← hb]; ring⟩

theorem algHom_coe (ψ : PowerSeries O →ₐ[O] PowerSeries O) (p : Polynomial O) :
    ψ (p : PowerSeries O) = Polynomial.aeval (ψ X) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.coe_add, map_add (f := _), hp, hq, map_add (f := _)]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    congr 1
    first
    | exact ψ.commutes c
    | (rw [← ψ.commutes c]; rfl)
    | simp [PowerSeries.algebraMap_eq]

private theorem natDegree_trunc_lt_of_pos (a : PowerSeries O) {N : ℕ} (hN : 0 < N) :
    (trunc N a).natDegree < N := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  first
  | exact PowerSeries.natDegree_trunc_lt a N'
  | exact Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
      rw [PowerSeries.coeff_trunc, if_neg (by omega)])

private theorem coeff_algHom_eq_sum_range_of_lt (σ : PowerSeries O →ₐ[O] PowerSeries O)
    (hσ : constantCoeff (σ X) = 0) (a : PowerSeries O) {m N : ℕ} (hN : m < N) :
    coeff m (σ a) = ∑ n ∈ Finset.range N, coeff n a * coeff m (σ X ^ n) := by
  obtain ⟨b, hb⟩ := trunc_decomp a N
  have hdeg := natDegree_trunc_lt_of_pos a (lt_of_le_of_lt (Nat.zero_le m) hN)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show σ a = σ ((trunc N a : PowerSeries O) + X ^ N * b) from congrArg σ hb, map_add (f := _), map_mul,
    map_pow, algHom_coe, map_add,
    coeff_pow_mul_lt hσ hN, add_zero,
    Polynomial.aeval_eq_sum_range' hdeg, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  first
  | rw [map_smul, smul_eq_mul, PowerSeries.coeff_trunc, if_pos hi]
  | rw [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_trunc, if_pos hi]
  | simp [PowerSeries.coeff_trunc, hi]

private theorem hasSubst_of_constantCoeff_eq_zero_level_letter_cocycles {Y : PowerSeries O}
    (hY : constantCoeff Y = 0) : PowerSeries.HasSubst Y := by
  first
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' hY
  | exact PowerSeries.HasSubst.of_constantCoeff_zero hY
  | exact ⟨1, by rw [pow_one]; exact hY⟩

private theorem coeff_subst_eq_sum_range_of_lt {Y : PowerSeries O} (hY : constantCoeff Y = 0)
    (a : PowerSeries O) {m N : ℕ} (hN : m < N) :
    coeff m (a.subst Y) = ∑ n ∈ Finset.range N, coeff n a * coeff m (Y ^ n) := by
  have hs := hasSubst_of_constantCoeff_eq_zero_level_letter_cocycles hY
  let σ : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom hs
  have h1 : ∀ f : PowerSeries O, σ f = f.subst Y := fun f => by
    first
    | rfl
    | simp [σ, PowerSeries.coe_substAlgHom]
  have h2 : σ X = Y := by
    rw [h1]
    first
    | exact PowerSeries.subst_X hs
    | simp [hs]
  have h3 := coeff_algHom_eq_sum_range_of_lt σ (by rw [h2]; exact hY) a hN
  rw [h2, h1] at h3
  exact h3

theorem algHom_eq_subst (ψ : PowerSeries O →ₐ[O] PowerSeries O)
    (hψ : constantCoeff (ψ X) = 0) (a : PowerSeries O) : ψ a = a.subst (ψ X) := by
  ext m
  rw [coeff_algHom_eq_sum_range_of_lt ψ hψ a (Nat.lt_succ_self m),
    coeff_subst_eq_sum_range_of_lt hψ a (Nat.lt_succ_self m)]

def qn (Y Z : PowerSeries O) (n : ℕ) : PowerSeries O :=
  ∑ i ∈ Finset.range n, Y ^ i * Z ^ (n - 1 - i)

theorem coeff_qn {Y Z : PowerSeries O} (hY : constantCoeff Y = 0) (hZ : constantCoeff Z = 0)
    {n j : ℕ} (h : j + 1 < n) : coeff j (qn Y Z n) = 0 := by
  obtain ⟨Y', rfl⟩ := PowerSeries.X_dvd_iff.mpr hY
  obtain ⟨Z', rfl⟩ := PowerSeries.X_dvd_iff.mpr hZ
  unfold qn
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e : n - 1 = i + (n - 1 - i) := by omega
  have hprod : (X * Y') ^ i * (X * Z') ^ (n - 1 - i) = X ^ (n - 1) * (Y' ^ i * Z' ^ (n - 1 - i)) := by
    generalize n - 1 - i = k at e ⊢
    rw [e]
    ring
  rw [hprod]
  exact coeff_X_pow_mul_lt (by omega) _

theorem subst_sub_subst_dvd {Y Z : PowerSeries O} (hY : constantCoeff Y = 0)
    (hZ : constantCoeff Z = 0) (a : PowerSeries O) : (Y - Z) ∣ a.subst Y - a.subst Z := by
  classical
  have hYZ : ∀ n, (Y - Z) * qn Y Z n = Y ^ n - Z ^ n := fun n => by
    unfold qn
    rw [mul_comm]
    first
    | exact geom_sum₂_mul Y Z n
    | exact (Commute.all Y Z).geom_sum₂_mul n
  have stab : ∀ q M, q + 2 ≤ M →
      ∑ n ∈ Finset.range M, coeff n a * coeff q (qn Y Z n) =
        ∑ n ∈ Finset.range (q + 2), coeff n a * coeff q (qn Y Z n) := by
    intro q M hM
    symm
    refine Finset.sum_subset (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega) fun n _ hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [coeff_qn hY hZ (by omega), mul_zero]
  refine ⟨PowerSeries.mk fun q =>
    ∑ n ∈ Finset.range (q + 2), coeff n a * coeff q (qn Y Z n), ?_⟩
  ext m
  symm
  have hm : m < m + 2 := by omega
  rw [map_sub, PowerSeries.coeff_mul, coeff_subst_eq_sum_range_of_lt hY a hm,
    coeff_subst_eq_sum_range_of_lt hZ a hm, ← Finset.sum_sub_distrib]
  have h1 : ∀ n, coeff n a * coeff m (Y ^ n) - coeff n a * coeff m (Z ^ n) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, coeff p.1 (Y - Z) * (coeff n a * coeff p.2 (qn Y Z n)) := by
    intro n
    have e := congrArg (coeff m) (hYZ n)
    rw [map_sub, PowerSeries.coeff_mul] at e
    rw [← mul_sub, ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [Finset.sum_congr rfl fun n _ => h1 n]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [PowerSeries.coeff_mk, ← Finset.mul_sum,
    stab p.2 (m + 2) (by rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp; omega)]

end Formalism.MainNotions.N.WachTwistedLattices.PowerSeriesTruncation
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ConvEqSum
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def conv (g : PowerSeries L) (f : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem conv_vanish (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : (PowerSeries.X : PowerSeries L) ^ e ∣ g) (k : ℤ) (hk : k < m + e) : conv g f k = 0 := by
  unfold conv
  rw [PowerSeries.X_pow_dvd_iff] at hg
  have hz : ∀ j : ℕ, PowerSeries.coeff j g • f (k - j) = 0 := by
    intro j
    by_cases hj : j < e
    · rw [hg j hj, zero_smul]
    · rw [hf _ (by omega), smul_zero]
  exact (finsum_congr hz).trans finsum_zero

theorem conv_lead (g : PowerSeries L) (f : ℤ → M) (m : ℤ) (hf : ∀ k < m, f k = 0) (e : ℕ)
    (hg : ∀ j < e, PowerSeries.coeff j g = 0) :
    conv g f (m + e) = PowerSeries.coeff e g • f m := by
  unfold conv
  rw [finsum_eq_single _ e]
  · rw [add_sub_cancel_right]
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hg j h, zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem triangular {ι : Type} [Fintype ι] (D : ι → ℤ → M) (m : ℤ) (hD : ∀ a, ∀ k < m, D a k = 0)
    (hind : LinearIndependent L (fun a => D a m)) (g : ι → PowerSeries L) (b : ℕ)
    (hsum : ∀ k < m + b, ∑ a, conv (g a) (D a) k = 0) :
    ∀ a, (PowerSeries.X : PowerSeries L) ^ b ∣ g a := by
  have key : ∀ n : ℕ, n < b → ∀ a, PowerSeries.coeff n (g a) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h1 : ∑ a, PowerSeries.coeff n (g a) • D a m = 0 := by
        have hs := hsum (m + n) (by omega)
        calc ∑ a, PowerSeries.coeff n (g a) • D a m
            = ∑ a, conv (g a) (D a) (m + n) :=
              Finset.sum_congr rfl fun a _ =>
                (conv_lead (g a) (D a) m (hD a) n
                  (fun j hj => ih j hj (by omega) a)).symm
          _ = 0 := hs
      exact Fintype.linearIndependent_iff.mp hind (fun a => PowerSeries.coeff n (g a)) h1
  intro a
  rw [PowerSeries.X_pow_dvd_iff]
  intro n hn
  exact key n hn a

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Conv
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.EqZeroOfPowDvd
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring

open Polynomial

variable {K : Type} [Field K]

theorem eq_X_mul_unit (s : PowerSeries K) (h0 : PowerSeries.constantCoeff s = 0)
    (h1 : PowerSeries.coeff 1 s ≠ 0) : ∃ u : PowerSeries K, IsUnit u ∧ s = PowerSeries.X * u := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr h0
  refine ⟨u, ?_, hu⟩
  have hc : PowerSeries.coeff 1 s = PowerSeries.constantCoeff u := by
    rw [hu]
    first
    | simp [PowerSeries.coeff_succ_X_mul]
    | exact PowerSeries.coeff_succ_X_mul 0 u
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [hc] at h1
  exact isUnit_iff_ne_zero.mpr h1

private theorem algebraMap_powerSeries_self_eq_C {R : Type} [CommRing R] (a : R) :
    algebraMap R (PowerSeries R) a = PowerSeries.C a := by
  first
  | rfl
  | (rw [Algebra.algebraMap_eq_smul_one, PowerSeries.smul_eq_C_mul, mul_one])
  | simp [PowerSeries.algebraMap_apply']

private theorem constantCoeff_aeval_eq_eval_constantCoeff (y : PowerSeries K) (r : K[X]) :
    PowerSeries.constantCoeff (Polynomial.aeval y r) = r.eval (PowerSeries.constantCoeff y) := by
  refine Polynomial.induction_on' r (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), hp, hq, Polynomial.eval_add]
  · rw [Polynomial.aeval_monomial, map_mul, map_pow, algebraMap_powerSeries_self_eq_C, PowerSeries.constantCoeff_C,
      Polynomial.eval_monomial]

theorem pow_dvd_of_order (r : K[X]) (c : K) (s : PowerSeries K)
    (h0 : PowerSeries.constantCoeff s = 0) (h1 : PowerSeries.coeff 1 s ≠ 0) (b : ℕ)
    (hb : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) r) :
    (Polynomial.X - Polynomial.C c) ^ b ∣ r := by
  obtain ⟨u, hu, hsu⟩ := eq_X_mul_unit s h0 h1
  have hsub : Polynomial.aeval (PowerSeries.C c + s) (Polynomial.X - Polynomial.C c) = s := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_powerSeries_self_eq_C, add_sub_cancel_left]
  induction b generalizing r with
  | zero => simp
  | succ b ih =>
    have hX : (PowerSeries.X : PowerSeries K) ∣ Polynomial.aeval (PowerSeries.C c + s) r :=
      (dvd_pow_self _ (Nat.succ_ne_zero b)).trans hb
    have hroot : r.IsRoot c := by
      rw [PowerSeries.X_dvd_iff, constantCoeff_aeval_eq_eval_constantCoeff, map_add (f := _), PowerSeries.constantCoeff_C, h0,
        add_zero] at hX
      exact hX
    obtain ⟨q, rfl⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    rw [map_mul, hsub] at hb
    have hb' : (PowerSeries.X : PowerSeries K) * PowerSeries.X ^ b ∣
        PowerSeries.X * (u * Polynomial.aeval (PowerSeries.C c + s) q) := by
      rw [← mul_assoc, ← hsu, ← pow_succ']
      exact hb
    have hq : (PowerSeries.X : PowerSeries K) ^ b ∣ Polynomial.aeval (PowerSeries.C c + s) q :=
      hu.dvd_mul_left.mp ((mul_dvd_mul_iff_left PowerSeries.X_ne_zero).mp hb')
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih q hq)

theorem eq_zero_of_pow_dvd (r : K[X]) (cs : Finset K) (b : ℕ)
    (h : ∀ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b ∣ r) (hdeg : r.natDegree < cs.card * b) : r = 0 := by
  by_contra hr
  have hprod : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b) ∣ r := by
    refine Finset.prod_dvd_of_coprime ?_ h
    intro x _ y _ hxy
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
  have hdeg' : (∏ c ∈ cs, (Polynomial.X - Polynomial.C c) ^ b).natDegree = cs.card * b := by
    rw [Polynomial.natDegree_prod _ _ (fun c _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))]
    simp [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_comm]
  have := Polynomial.natDegree_le_of_dvd hprod hr
  omega

theorem algHom_coe {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (φ : PowerSeries O →ₐ[O] A) (r : O[X]) :
    φ (r : PowerSeries O) = Polynomial.aeval (φ PowerSeries.X) r := by
  refine Polynomial.induction_on r (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.coe_C, Polynomial.aeval_C, ← algebraMap_powerSeries_self_eq_C, φ.commutes]
  · rw [Polynomial.coe_add, map_add (f := _), map_add (f := _), hp, hq]
  · rw [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X, map_mul, map_pow,
      ← algebraMap_powerSeries_self_eq_C, φ.commutes, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]

private theorem aeval_map_algebraMap_eq_aeval {O : Type} [CommRing O] [Algebra O K] (y : PowerSeries K)
    (r : O[X]) : Polynomial.aeval y (r.map (algebraMap O K)) = Polynomial.aeval y r := by
  first
  | exact Polynomial.aeval_map_algebraMap K y r
  | (refine Polynomial.induction_on r (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
     · simp [algebraMap_powerSeries_self_eq_C, PowerSeries.algebraMap_apply']
     · simp only [Polynomial.map_add (f := _), map_add (f := _), hp, hq]
     · simp [algebraMap_powerSeries_self_eq_C, PowerSeries.algebraMap_apply'])

theorem dvd_of_vanish {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) f (N : ℕ)
    (hres : PowerSeries.map (IsLocalRing.residue O) f = PowerSeries.X ^ N)
    (Z : Finset K) (hZ : Z.card = N) (φ : K → (PowerSeries O →ₐ[O] PowerSeries K))
    (s : K → PowerSeries K) (hφX : ∀ c ∈ Z, φ c PowerSeries.X = PowerSeries.C c + s c)
    (hs0 : ∀ c ∈ Z, PowerSeries.constantCoeff (s c) = 0)
    (hs1 : ∀ c ∈ Z, PowerSeries.coeff 1 (s c) ≠ 0)
    (hf : ∀ c ∈ Z, PowerSeries.X ∣ φ c f) (b : ℕ) (g : PowerSeries O)
    (hg : ∀ c ∈ Z, PowerSeries.X ^ b ∣ φ c g) :
    ∃ h : PowerSeries O, g = f ^ b * h := by
  have hmap : PowerSeries.map (IsLocalRing.residue O) (f ^ b) = PowerSeries.X ^ (N * b) := by
    rw [map_pow, hres, ← pow_mul]
  have hne : PowerSeries.map (IsLocalRing.residue O) (f ^ b) ≠ 0 := by
    rw [hmap]; exact pow_ne_zero _ PowerSeries.X_ne_zero
  obtain ⟨q, r, hqr⟩ := PowerSeries.exists_isWeierstrassDivision g hne
  have hord : (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)).order.toNat
      = N * b := by
    have hm : PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (f ^ b)
        = PowerSeries.X ^ (N * b) := hmap
    rw [hm, PowerSeries.order_X_pow]
    rfl
  have hdeg : r.degree < (N * b : ℕ) := by
    have := hqr.degree_lt
    rwa [hord] at this
  have hg_eq : g = f ^ b * q + (r : PowerSeries O) := hqr.eq_mul_add
  have hr : r = 0 := by
    by_contra hr0
    have hnat : r.natDegree < N * b := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hdeg
    have hdvd : ∀ c ∈ Z, (Polynomial.X - Polynomial.C c) ^ b ∣ r.map (algebraMap O K) := by
      intro c hc
      apply pow_dvd_of_order _ c (s c) (hs0 c hc) (hs1 c hc) b
      have h1 : φ c g = (φ c f) ^ b * φ c q + Polynomial.aeval (PowerSeries.C c + s c) r := by
        rw [hg_eq, map_add (f := _), map_mul, map_pow, algHom_coe, hφX c hc]
      have h2 : (PowerSeries.X : PowerSeries K) ^ b ∣ (φ c f) ^ b * φ c q :=
        dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (hf c hc) b) _
      have h4 := hg c hc
      rw [h1] at h4
      rw [aeval_map_algebraMap_eq_aeval]
      exact (dvd_add_right h2).mp h4
    have hK : r.map (algebraMap O K) = 0 := by
      refine eq_zero_of_pow_dvd _ Z b hdvd ?_
      rw [hZ]
      exact lt_of_le_of_lt Polynomial.natDegree_map_le hnat
    exact hr0 (Polynomial.map_injective _ hinj (by rw [hK, Polynomial.map_zero]))
  exact ⟨q, by rw [hg_eq, hr, Polynomial.coe_zero, add_zero]⟩

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Ring
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExistsMemMapEqSmul
section
namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds

open Polynomial

variable {O M₁ M₂ : Type*} [CommRing O] [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂]
  [Module O M₂]

private theorem linearMap_mul_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g * h) x = g (h x) := rfl

theorem linearMap_pow_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (k : ℕ) (y : M₁) : f ((d₁ ^ k) y) = (d₂ ^ k) (f y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, linearMap_mul_apply, linearMap_mul_apply, ih, hf]

private theorem linearMap_add_apply {M : Type*} [AddCommGroup M] [Module O M] (g h : M →ₗ[O] M)
    (x : M) : (g + h) x = g x + h x := rfl

private theorem aeval_end_monomial_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (n : ℕ) (a : O) (x : M) :
    aeval d (monomial n a) x = a • (d ^ n) x := by
  rw [aeval_monomial, linearMap_mul_apply]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

theorem linearMap_aeval_apply_comm_of_intertwine (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (P : O[X]) (y : M₁) :
    f (aeval d₁ P y) = aeval d₂ P (f y) := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), linearMap_add_apply, linearMap_add_apply, map_add (f := _), hp, hq]
  · rw [aeval_end_monomial_apply, aeval_end_monomial_apply, map_smul, linearMap_pow_apply_comm_of_intertwine f d₁ d₂ hf]

private theorem pow_apply_mem_of_invariant' (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (k : ℕ) {y : M₁} (hy : y ∈ N) : (d ^ k) y ∈ N := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    rw [pow_succ, linearMap_mul_apply]
    exact ih (hN y hy)

theorem aeval_apply_mem_of_invariant (N : Submodule O M₁) (d : M₁ →ₗ[O] M₁) (hN : ∀ y ∈ N, d y ∈ N)
    (P : O[X]) {y : M₁} (hy : y ∈ N) : aeval d P y ∈ N := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), linearMap_add_apply]
    exact N.add_mem hp hq
  · rw [aeval_end_monomial_apply]
    exact N.smul_mem a (pow_apply_mem_of_invariant' N d hN n hy)

private theorem aeval_end_C_apply {M : Type*} [AddCommGroup M] [Module O M]
    (d : M →ₗ[O] M) (a : O) (x : M) : aeval d (C a) x = a • x := by
  rw [aeval_C]
  first
    | rw [Module.algebraMap_end_apply]
    | simp

theorem exists_mem_map_eq_smul (f : M₁ →ₗ[O] M₂) (d₁ : M₁ →ₗ[O] M₁) (d₂ : M₂ →ₗ[O] M₂)
    (hf : ∀ y, f (d₁ y) = d₂ (f y)) (N₁ : Submodule O M₁) (hN : ∀ y ∈ N₁, d₁ y ∈ N₁)
    (P₁ P₂ : O[X]) (e : O) (he : C e ∈ Ideal.span ({P₁, P₂} : Set O[X])) (x : M₂)
    (h₁ : ∃ y ∈ N₁, f y = aeval d₂ P₁ x) (h₂ : ∃ y ∈ N₁, f y = aeval d₂ P₂ x) :
    ∃ y ∈ N₁, f y = e • x := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : O[X], A * P₁ + B * P₂ = C e := by
    first
      | exact Ideal.mem_span_pair.1 he
      | simpa [smul_eq_mul] using Submodule.mem_span_pair.1 he
  obtain ⟨y₁, hy₁, hfy₁⟩ := h₁
  obtain ⟨y₂, hy₂, hfy₂⟩ := h₂
  refine ⟨aeval d₁ A y₁ + aeval d₁ B y₂,
    N₁.add_mem (aeval_apply_mem_of_invariant N₁ d₁ hN A hy₁) (aeval_apply_mem_of_invariant N₁ d₁ hN B hy₂), ?_⟩
  rw [← aeval_end_C_apply d₂ e x, ← hAB, map_add (aeval d₂), map_mul (aeval d₂), map_mul (aeval d₂),
    linearMap_add_apply, linearMap_mul_apply, linearMap_mul_apply, ← hfy₁, ← hfy₂, map_add f,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf,
    linearMap_aeval_apply_comm_of_intertwine f d₁ d₂ hf]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.FactorialSumBounds
end

