module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0017
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.AbsNormSpanNatCast
section
open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Arith

variable {F : Type} [Field F] [NumberField F]

def nfT (F : Type) [Field F] [NumberField F] (T : ℕ) : Multiset (Ideal (𝓞 F)) :=
  UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((T : ℕ) : 𝓞 F)})

def supT (F : Type) [Field F] [NumberField F] (T : ℕ) : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
  (nfT F T).toFinset.subtype (fun 𝔭 => 𝔭.IsMaximal)

theorem span_natCast_ne_bot {T : ℕ} (hT : 0 < T) : Ideal.span {((T : ℕ) : 𝓞 F)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hT.ne'

theorem mem_nfT_iff {T : ℕ} (hT : 0 < T) (P : Ideal (𝓞 F)) :
    P ∈ nfT F T ↔ P.IsPrime ∧ ((T : ℕ) : 𝓞 F) ∈ P := by
  unfold nfT
  rw [Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hT), Ideal.span_singleton_le_iff_mem]

theorem isMaximal_of_mem_nfT {T : ℕ} (hT : 0 < T) {P : Ideal (𝓞 F)} (h : P ∈ nfT F T) :
    P.IsMaximal := by
  obtain ⟨hP, hm⟩ := (mem_nfT_iff hT P).1 h
  refine hP.isMaximal ?_
  rintro rfl
  rw [Ideal.mem_bot] at hm
  exact (Nat.cast_ne_zero.2 hT.ne') hm

theorem mem_supT {T : ℕ} (hT : 0 < T) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    𝔭 ∈ supT F T ↔ ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 := by
  unfold supT
  rw [Finset.mem_subtype, Multiset.mem_toFinset, mem_nfT_iff hT]
  exact ⟨fun h => h.2, fun h => ⟨𝔭.2.isPrime, h⟩⟩

theorem tprod_supT {T : ℕ} (hT : 0 < T) (g : Ideal (𝓞 F) → ℝ) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then g 𝔭.1 else 1)) =
      ∏ P ∈ (nfT F T).toFinset, g P := by
  rw [tprod_eq_prod (s := supT F T)]
  · unfold supT
    rw [Finset.prod_subtype_eq_prod_filter (f := fun P => if ((T : ℕ) : 𝓞 F) ∈ P then g P else 1)]
    rw [Finset.filter_true_of_mem (fun P hP => isMaximal_of_mem_nfT hT (Multiset.mem_toFinset.1 hP))]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos ((mem_nfT_iff hT P).1 (Multiset.mem_toFinset.1 hP)).2]
  · intro 𝔭 h𝔭
    rw [if_neg (fun h => h𝔭 ((mem_supT hT 𝔭).2 h))]

theorem absNorm_span_natCast (T : ℕ) :
    Ideal.absNorm (Ideal.span {((T : ℕ) : 𝓞 F)}) = T ^ finrank ℚ F := by
  rw [Ideal.absNorm_span_singleton]
  have e : ((T : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (T : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem prod_absNorm_pow {T : ℕ} (hT : 0 < T) :
    ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P : ℝ) ^ (vT F T P) = (T : ℝ) ^ finrank ℚ F := by
  have h1 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (Multiset.count P (nfT F T)) =
      ((nfT F T).map Ideal.absNorm).prod := (Finset.prod_multiset_map_count _ _).symm
  have h2 : ((nfT F T).map Ideal.absNorm).prod = Ideal.absNorm (nfT F T).prod :=
    (map_multiset_prod Ideal.absNorm _).symm
  have h3 : (nfT F T).prod = Ideal.span {((T : ℕ) : 𝓞 F)} :=
    Ideal.prod_normalizedFactors_eq_self (span_natCast_ne_bot hT)
  have h4 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (vT F T P) = T ^ finrank ℚ F := by
    have : ∀ P, vT F T P = Multiset.count P (nfT F T) := fun P => rfl
    simp only [this]
    rw [h1, h2, h3, absNorm_span_natCast]
  exact_mod_cast h4

end Arith

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowersNeZero
section
open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

def SStable {K : Type} [Field K] [NumberField K] [StarRing K]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Prop :=
  ∀ a ∈ (I : Submodule (𝓞 K) K), star a ∈ (I : Submodule (𝓞 K) K)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem sStable_one : SStable (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  intro a ha
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ha ⊢
  obtain ⟨x, rfl⟩ := ha
  exact ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd K) x, rfl⟩

theorem sStable_mul {I J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (hJ : SStable J) :
    SStable (I * J) := by
  intro a ha
  rw [FractionalIdeal.coe_mul] at ha ⊢
  refine Submodule.mul_induction_on (C := fun a => star a ∈ (I : Submodule (𝓞 K) K) * J) ha ?_ ?_
  · intro x hx y hy
    rw [star_mul, mul_comm (star y)]
    exact Submodule.mul_mem_mul (hI x hx) (hJ y hy)
  · intro x y hx hy
    rw [star_add]
    exact add_mem hx hy

theorem sStable_pow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℕ) :
    SStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact sStable_one
  | succ n ih => rw [pow_succ]; exact sStable_mul ih hI

theorem sStable_inv {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) : SStable I⁻¹ := by
  by_cases h0 : I = 0
  · subst h0
    intro a ha
    rw [FractionalIdeal.inv_zero', FractionalIdeal.coe_zero, Submodule.mem_bot] at ha ⊢
    rw [ha, star_zero]
  · intro a ha
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff h0] at ha ⊢
    intro y hy
    have h1 : a * star y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
      ha _ (FractionalIdeal.mem_coe.mp (hI y (FractionalIdeal.mem_coe.mpr hy)))
    have h2 := sStable_one (K := K) _ (FractionalIdeal.mem_coe.mpr h1)
    rw [star_mul, star_star, mul_comm] at h2
    exact FractionalIdeal.mem_coe.mp h2

theorem sStable_zpow {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : SStable I) (n : ℤ) :
    SStable (I ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact sStable_pow hI n
  | negSucc n => rw [zpow_negSucc]; exact sStable_inv (sStable_pow hI _)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sStable_ddS (D : Formalism.BasicNotions.D7) : SStable (ddS D) := by
  intro a ha
  rw [FractionalIdeal.mem_coe] at ha ⊢
  unfold ddS at ha ⊢
  rw [FractionalIdeal.mem_coeIdeal] at ha ⊢
  obtain ⟨y, hy, rfl⟩ := ha

  have hc : (NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E)).comp
      (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) := by
    ext x
    exact (D.sp.cm.fixed _).2 ⟨(x : D.host.F), rfl⟩
  refine ⟨NumberField.RingOfIntegers.mapRingHom (starRingEnd D.host.E) y, ?_, rfl⟩
  rw [← hc, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem _ hy

theorem ddS_ne_zero' (D : Formalism.BasicNotions.D7) : ddS D ≠ 0 :=
  PI.ScalarPairDr.W.ddS_ne_zero D

theorem stable_differentIdealPowers (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : SStable (differentIdealPowers D i) := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact sStable_one
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact sStable_zpow (sStable_ddS D) _

theorem differentIdealPowers_ne_zero (D : Formalism.BasicNotions.D7) (i : Fin (D.R.rS + 1)) : differentIdealPowers D i ≠ 0 := by
  induction i using Fin.lastCases with
  | last => unfold differentIdealPowers; rw [Fin.snoc_last]; exact one_ne_zero
  | cast a => unfold differentIdealPowers; rw [Fin.snoc_castSucc]; exact zpow_ne_zero _ (ddS_ne_zero' D)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FinrankOFOE
section
open NumberField Module Formalism.MainNotions.S

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_OF_OE (D : Formalism.BasicNotions.D7) : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.host.der.finrank_E, D.host.der.finrank_F] at h1
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [D.host.der.finrank_E] at hpos

  have key : ∀ o x : ℕ, 2 * o * x = 4 * o → 0 < 4 * o → x = 2 := by
    intro o x h hp
    have ho : 0 < 2 * o := by omega
    exact Nat.eq_of_mul_eq_mul_left ho (by rw [h]; ring)
  exact key _ _ h1 hpos

theorem absNorm_ddS (D : Formalism.BasicNotions.D7) :
    FractionalIdeal.absNorm (ddS D) = (((NumberField.discr D.host.F).natAbs : ℚ)) ^ 2 := by
  have h := FractionalIdeal.absNorm_eq' (K := D.host.E) (I := ddS D) 1
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)))
    (by
      first
        | (open scoped Pointwise in rw [one_smul]; rfl)
        | (exact (one_smul _ _).trans rfl)
        | (open scoped Pointwise in simp; rfl))
  rw [h, Ideal.absNorm_algebraMap, finrank_OF_OE,
    NumberField.absNorm_differentIdeal (K := D.host.F)]
  simp

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramDeterminantFormula
section
open Matrix Polynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Generic

variable {K : Type*} [Field K]

theorem adjugate_last (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    M.adjugate (Fin.last r) (Fin.last r) = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp only [Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem det_sub_single (r : ℕ) (W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (W - single (Fin.last r) (Fin.last r) c).det =
      W.det - c * W.adjugate (Fin.last r) (Fin.last r) := by
  have hrow : W - single (Fin.last r) (Fin.last r) c =
      W.updateRow (Fin.last r) (W (Fin.last r) + (-c) • Pi.single (Fin.last r) 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.updateRow_apply, Matrix.single_apply, Pi.add_apply,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp_all [sub_eq_add_neg]
  rw [hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← Matrix.adjugate_apply]
  ring

theorem det_blocks_of_ne (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) (hZ : Z.det ≠ 0) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det = Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  haveI := Z.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hZ)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, Matrix.single_mul_mul_single,
    det_sub_single, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  field_simp

theorem single_map {L M : Type*} [Ring L] [Ring M] (f : L →+* M) (r : ℕ) (c : L) :
    (single (Fin.last r) (Fin.last r) c).map f = single (Fin.last r) (Fin.last r) (f c) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

private theorem blocks_map_lemma {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)
    (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (a b : R) :
    f ((fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det -
      (Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r))) =
    (fromBlocks (Z.map f) (single (Fin.last r) (Fin.last r) (f a))
        (single (Fin.last r) (Fin.last r) (f b)) (W.map f)).det -
      ((Z.map f).det * (W.map f).det - f a * f b * (Z.map f).adjugate (Fin.last r) (Fin.last r) *
        (W.map f).adjugate (Fin.last r) (Fin.last r)) := by
  have hdet : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R, f M.det = (M.map f).det := fun M =>
    RingHom.map_det f M
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R,
      f (M.adjugate (Fin.last r) (Fin.last r)) = (M.map f).adjugate (Fin.last r) (Fin.last r) := by
    intro M
    rw [show M.map f = f.mapMatrix M from rfl, ← RingHom.map_adjugate]
    rfl
  simp only [map_sub, map_mul, hdet, hadj]
  rw [RingHom.map_det f, RingHom.mapMatrix_apply, Matrix.fromBlocks_map, single_map, single_map]

theorem det_blocks (r : ℕ) (Z W : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (a b : K) :
    (fromBlocks Z (single (Fin.last r) (Fin.last r) a) (single (Fin.last r) (Fin.last r) b) W).det =
      Z.det * W.det - a * b * Z.adjugate (Fin.last r) (Fin.last r) * W.adjugate (Fin.last r) (Fin.last r) := by
  classical
  let φ := algebraMap K[X] (FractionRing K[X])
  have hφ : Function.Injective φ := IsFractionRing.injective K[X] (FractionRing K[X])
  have hdet : ((charmatrix (-Z)).map φ).det ≠ 0 := by
    have h1 : φ (charmatrix (-Z)).det ≠ 0 := fun h =>
      (Matrix.charpoly_monic (-Z)).ne_zero (hφ (h.trans (map_zero φ).symm))
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h1
  have key := det_blocks_of_ne r ((charmatrix (-Z)).map φ) ((W.map Polynomial.C).map φ)
    (φ (Polynomial.C a)) (φ (Polynomial.C b)) hdet
  have hX : (fromBlocks (charmatrix (-Z)) (single (Fin.last r) (Fin.last r) (Polynomial.C a))
      (single (Fin.last r) (Fin.last r) (Polynomial.C b)) (W.map Polynomial.C)).det -
      ((charmatrix (-Z)).det * (W.map Polynomial.C).det - Polynomial.C a * Polynomial.C b *
        (charmatrix (-Z)).adjugate (Fin.last r) (Fin.last r) *
        (W.map Polynomial.C).adjugate (Fin.last r) (Fin.last r)) = 0 := by
    apply hφ
    rw [blocks_map_lemma, map_zero, key, sub_self]
  have h0 := congrArg (Polynomial.evalRingHom (0 : K)) hX
  rw [blocks_map_lemma, map_zero] at h0
  have hZ0 : (charmatrix (-Z)).map (Polynomial.evalRingHom (0 : K)) = Z := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.charmatrix_apply_eq]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h]
  have hW0 : (W.map Polynomial.C).map (Polynomial.evalRingHom (0 : K)) = W := by
    ext i j; simp
  rw [hZ0, hW0] at h0
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at h0
  exact sub_eq_zero.mp h0

end Generic

theorem det_swap {K : Type*} [Field K] (n : ℕ) :
    (fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)
      (0 : Matrix (Fin n) (Fin n) K)).det = (-1) ^ n := by
  have hN : (fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    simp [Matrix.det_fromBlocks_zero₁₂]
  have hMN : fromBlocks (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) * fromBlocks (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (1 : Matrix (Fin n) (Fin n) K) (0 : Matrix (Fin n) (Fin n) K) := by
    simp [Matrix.fromBlocks_multiply]
  have h := congrArg Matrix.det hMN
  rw [Matrix.det_mul, hN, mul_one, Matrix.det_fromBlocks_one₁₁] at h
  rw [h]
  simp [Matrix.det_neg]

open Formalism.L2.SG.CntLocal Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem leadMinorE_r (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = Z.adjugate (Fin.last D.R.rS) (Fin.last D.R.rS) := by
  rw [adjugate_last]
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ _)]
  rfl

theorem gram_determinant_formula_alt : DetGa := by
  intro D T T' _ _ Z
  have hA : ∀ c : D.host.E, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then c else 0) =
      single (Fin.last D.R.rS) (Fin.last D.R.rS) c := by
    intro c
    ext a b
    by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;>
      simp_all [Matrix.single_apply, eq_comm]
  have hprod : Ga T T' Z * fromBlocks (0 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) 1 1 0 =
      fromBlocks Z (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T))
        (single (Fin.last D.R.rS) (Fin.last D.R.rS) (-T')) Zᴴ := by
    unfold Ga
    rw [hA, hA, Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_mul, det_swap, det_blocks, Matrix.det_conjTranspose, ← Matrix.adjugate_conjTranspose,
    Matrix.conjTranspose_apply] at h
  unfold GZ
  rw [leadMinorE_full, leadMinorE_r]
  have hsq : ((-1 : D.host.E) ^ (D.R.rS + 1)) * (-1) ^ (D.R.rS + 1) = 1 := by
    rw [← mul_pow]; simp
  calc (Ga T T' Z).det = (Ga T T' Z).det * ((-1) ^ (D.R.rS + 1) * (-1) ^ (D.R.rS + 1)) := by
        rw [hsq, mul_one]
    _ = (-1) ^ (D.R.rS + 1) * ((Ga T T' Z).det * (-1) ^ (D.R.rS + 1)) := by ring
    _ = _ := by rw [h]; ring

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanExists
section
open NumberField Module IsDedekindDomain Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

open Formalism.HermitianLattices.Ext.L3

def JordanExists : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → Module.finrank F K = 2 → h.IsSymm →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    Formalism.HermitianLatticesTheory.IsIntegralLat h (pbLat x 𝔞) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X (pbLat x 𝔞) 𝔭 b a

def DetLocal : Prop :=
  ∀ (K F V ι : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x : ι → V)
    (𝔞 : ι → FractionalIdeal (nonZeroDivisors (𝓞 K)) K), IsFixF K F →
    (∀ i, ∀ a ∈ (𝔞 i : Submodule (𝓞 K) K), star a ∈ (𝔞 i : Submodule (𝓞 K) K)) → (∀ i, 𝔞 i ≠ 0) →
    LinearIndependent K x → Submodule.span K (Set.range x) = X → (gram h x).det ≠ 0 →
    ∀ (𝔭 : Ideal (𝓞 F)) (b : Fin (finrank K X) → V) (a : Fin (finrank K X) → 𝓞 F), 𝔭.IsMaximal →
      IsJordanIn h X (pbLat x 𝔞) 𝔭 b a →
      ∀ P : HeightOneSpectrum (𝓞 K), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P ((∏ i, 𝔞 i ^ 2) *
            FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (gram h x).det) =
          FractionalIdeal.count K P
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((a j : 𝓞 F) : F))))

def CountExt : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K] (n : ℕ)
    (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)) (α : Fin n → 𝓞 F), 𝔭.IsMaximal →
    P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 → (∀ j, α j ≠ 0) →
    FractionalIdeal.count K P
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (algebraMap F K (∏ j, ((α j : 𝓞 F) : F)))) =
      ((P.asIdeal.ramificationIdx (𝓞 F) * ∑ j, vF 𝔭 (α j) : ℕ) : ℤ)

def NormAssembly : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K],
    Module.finrank F K = 2 →
    ∀ (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (w : Ideal (𝓞 F) → ℕ), J ≠ 0 →
    (∀ (𝔭 : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 K)), 𝔭.IsMaximal →
      P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 →
        FractionalIdeal.count K P J = ((P.asIdeal.ramificationIdx (𝓞 F) * w 𝔭 : ℕ) : ℤ)) →
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ w 𝔭.1) ^ 2 =
      (FractionalIdeal.absNorm J : ℝ)

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

