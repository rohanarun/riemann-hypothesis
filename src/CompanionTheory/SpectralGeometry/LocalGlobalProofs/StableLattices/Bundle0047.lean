module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0038

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionIsGlRepresentation
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos Cn ann cre lift)
open CompanionTheory.RgExh.U
open GlobalTheory.CompanionTheory.FarReg.BdProd (adL_cre)

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem lift_mul_cre (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * cre g : Module.End ℂ (Cn n V)) = cre g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_cre φ g x

theorem lift_mul_ann (φ : Module.End ℂ V) (g : Pos n) :
    (lift n φ * ann g : Module.End ℂ (Cn n V)) = ann g * lift n φ :=
  LinearMap.ext fun x => CompanionTheory.D.LK.lift_ann φ g x

theorem lift_mul_adL (φ : Module.End ℂ V) (p q : Fin n) :
    (lift n φ * adL p q : Module.End ℂ (Cn n V)) = adL p q * lift n φ := by
  simp only [adL, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, lift_mul_cre, mul_assoc, lift_mul_ann, mul_assoc]

theorem term_ann (k i g : Pos n) :
    (ann g * (cre k * ann i) - cre k * ann i * ann g : Module.End ℂ (Cn n V)) = if k = g then ann i else 0 := by
  have h1 := CompanionTheory.D.LK.Car.ann_cre (V := V) g k
  have h2 := CompanionTheory.D.LK.Car.ann_ann (V := V) g i
  rw [← mul_assoc, eq_sub_of_add_eq h1, sub_mul, mul_assoc (cre k) (ann g), eq_neg_of_add_eq_zero_left h2]
  by_cases e : k = g
  · subst e
    simp [mul_assoc]
  · have e' : ¬g = k := fun h => e h.symm
    simp [e, e', mul_assoc]

theorem adL_ann (p q : Fin n) (g : Pos n) :
    (∑ i : Pos n, adC p q i g • ann i : Module.End ℂ (Cn n V)) = ann g * adL p q - adL p q * ann g := by
  have h : (ann g * adL p q - adL p q * ann g : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (ann g * (cre k * ann i) - cre k * ann i * ann g) := by
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [term_ann]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single g]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem adL_comm (p q r v : Fin n) :
    (adL p q * adL r v - adL r v * adL p q : Module.End ℂ (Cn n V)) =
      ∑ i : Pos n, ∑ l : Pos n,
        (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • (cre l * ann i) := by
  have gen : ∀ A : Module.End ℂ (Cn n V), A * adL r v - adL r v * A =
      ∑ i : Pos n, ∑ k : Pos n, adC r v i k • (A * (cre k * ann i) - cre k * ann i * A) := by
    intro A
    simp only [adL, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
      ← Finset.sum_sub_distrib]
  have h1 : ∀ k i : Pos n, (adL p q * (cre k * ann i) - cre k * ann i * adL p q : Module.End ℂ (Cn n V)) =
      (∑ l : Pos n, adC p q k l • cre l) * ann i - cre k * ∑ m : Pos n, adC p q m i • ann m := by
    intro k i
    rw [← adL_cre, adL_ann]
    noncomm_ring
  rw [gen]
  simp only [h1, smul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  · refine (Finset.sum_congr rfl fun k _ => Finset.sum_comm).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm.trans ?_
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]

def dl (a b : Fin n) : ℂ := if a = b then 1 else 0

def cc (p q : Fin n) (s t : Fin n × Fin n) : ℂ :=
  dl q s.1 * dl t.1 p * dl t.2 s.2 - dl s.2 p * dl t.1 s.1 * dl t.2 q

theorem ite3 (A B C : Prop) [Decidable A] [Decidable B] [Decidable C] :
    (if A ∧ B ∧ C then 1 else 0 : ℂ) = (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases a : A <;> by_cases b : B <;> by_cases c : C <;> simp [a, b, c]

theorem adC_eq (p q : Fin n) (i k : Pos n) : adC p q i k = cc p q i.1 k.1 := by
  have e1 : ∀ a b : Fin n × Fin n, a = b ↔ a.1 = b.1 ∧ a.2 = b.2 := fun a b => Prod.ext_iff
  simp only [adC, cc, dl, e1 k.1, ite3]

theorem ite_dl (a b : Fin n) (x : ℂ) : (if a = b then x else 0) = dl a b * x := by
  by_cases h : a = b <;> simp [dl, h]

theorem sum_at (f : Fin n × Fin n → ℂ) (s : Fin n × Fin n) (hs : (s.1 : ℕ) < s.2) :
    ∑ k : Pos n, (if k.1 = s then f k.1 else 0) = f s := by
  have e : ∀ k : Pos n, k.1 = s ↔ k = ⟨s, hs⟩ := fun k => (Subtype.ext_iff (a1 := k) (a2 := ⟨s, hs⟩)).symm
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]

theorem sum_adC {lev : Fin n → ℕ} (hm : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) {i : Pos n}
    (hi : inU lev i) (f : Fin n × Fin n → ℂ) :
    ∑ k : Pos n, adC p q i k * f k.1 =
      dl q i.1.1 * f (p, i.1.2) - dl i.1.2 p * f (i.1.1, q) := by
  have a1 : ∑ k : Pos n, (if q = i.1.1 ∧ k.1 = (p, i.1.2) then 1 else 0) * f k.1 = dl q i.1.1 * f (p, i.1.2) := by
    by_cases h : q = i.1.1
    · have hs : (p : ℕ) < i.1.2 := by
        have : lev p < lev i.1.2 := by rw [hpq, h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (p, i.1.2) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  have a2 : ∑ k : Pos n, (if i.1.2 = p ∧ k.1 = (i.1.1, q) then 1 else 0) * f k.1 = dl i.1.2 p * f (i.1.1, q) := by
    by_cases h : i.1.2 = p
    · have hs : (i.1.1 : ℕ) < q := by
        have : lev i.1.1 < lev q := by rw [← hpq, ← h]; exact hi
        exact hm.reflect_lt this
      have := sum_at f (i.1.1, q) hs
      simp only [h, true_and, dl, if_true, one_mul, ite_mul, zero_mul] at this ⊢
      exact this
    · simp [h, dl]
  simp only [adC, sub_mul, Finset.sum_sub_distrib, a1, a2]

theorem mat_id {lev : Fin n → ℕ} (hm : Monotone lev) {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v)
    {i : Pos n} (hi : inU lev i) (l : Pos n) :
    ∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l) =
      (if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0) := by
  have h1 := sum_adC hm hrv hi (fun s => cc p q s l.1)
  have h2 := sum_adC hm hpq hi (fun s => cc r v s l.1)
  simp only [← adC_eq] at h1 h2
  rw [Finset.sum_sub_distrib, h1, h2, ite_dl, ite_dl]
  simp only [adC_eq, cc]
  ring

theorem ann_eq_zero {lev : Fin n → ℕ} {x : Cn n V} (hx : SuppIn (inU lev) x) {i : Pos n} (hi : ¬inU lev i) :
    ann i x = 0 := by
  funext A
  by_contra h
  exact hi (hx _ (CompanionTheory.D.LK.ann_ne h).2 i (mem_insert_self _ _))

theorem adL_comm_apply {lev : Fin n → ℕ} (hm : Monotone lev) {x : Cn n V} (hx : SuppIn (inU lev) x)
    {p q r v : Fin n} (hpq : lev p = lev q) (hrv : lev r = lev v) :
    adL p q (adL r v x) - adL r v (adL p q x) =
      (if q = r then adL p v x else 0) - (if v = p then adL r q x else 0) := by
  have h := LinearMap.congr_fun (adL_comm (V := V) p q r v) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [h]
  have e : ∀ a b : Fin n, (adL a b x : Cn n V) = ∑ i : Pos n, ∑ l : Pos n, adC a b i l • cre l (ann i x) := by
    intro a b
    simp [adL, LinearMap.sum_apply, Module.End.mul_apply]
  have t : ∀ i l : Pos n,
      (∑ k : Pos n, (adC r v i k * adC p q k l - adC p q i k * adC r v k l)) • cre l (ann i x) =
      ((if q = r then adC p v i l else 0) - (if v = p then adC r q i l else 0)) • cre l (ann i x) := by
    intro i l
    by_cases hi : inU lev i
    · rw [mat_id hm hpq hrv hi]
    · rw [ann_eq_zero hx hi, map_zero, smul_zero, smul_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  simp only [t]
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  · split_ifs
    · rw [e]
    · simp
  · split_ifs
    · rw [e]
    · simp

end GlobalTheory.CompanionTheory.RgCOBlock.LetterGl

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem lF_glRel : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E → ∀ (x : Cn n V), SuppIn (inU lev) x → ∀ p q r v, lev p = lev q → lev r = lev v → lF E p q (lF E r v x) - lF E r v (lF E p q x) = (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  intro n lev V _ _ E hm hE x hx p q r v hpq hrv
  have hA := LetterGl.adL_comm_apply hm hx hpq hrv
  have h1 : ∀ y : Cn n V, lift n (E p q) (adL r v y) = adL r v (lift n (E p q) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E p q) r v) y
  have h2 : ∀ y : Cn n V, lift n (E r v) (adL p q y) = adL p q (lift n (E r v) y) := fun y =>
    LinearMap.congr_fun (LetterGl.lift_mul_adL (E r v) p q) y
  have hL : lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x) =
      (if q = r then lift n (E p v) x else 0) - (if v = p then lift n (E r q) x else 0) := by
    funext A
    have := LinearMap.congr_fun (hE p q r v) (x A)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    simp only [Pi.sub_apply, CompanionTheory.D.LK.lift_apply]
    rw [this]
    split_ifs <;> simp
  simp only [lF, LinearMap.add_apply, map_add (f := _), h1, h2]
  calc _ = (lift n (E p q) (lift n (E r v) x) - lift n (E r v) (lift n (E p q) x)) +
        (adL p q (adL r v x) - adL r v (adL p q x)) := by abel
    _ = _ := by
      rw [hL, hA]
      split_ifs <;> abel

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantCoefficientsExpansion
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GroundTheory.BlockD.FourierDecayAlt.GaugeExists (qdetPoly tmPoly evU evU_apply evU_qdetPoly natDegree_qdetPoly_le
  coeff_qdetPoly_top prod_linear sum_fin_cast)

section Poly

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem poly_eq_zero_of_evU (Q : A[X]) (h : ∀ u : ℂ, evU u Q = 0) : Q = 0 := by
  ext j
  rw [coeff_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  let R : ℂ[X] := ∑ k ∈ range (Q.natDegree + 1), monomial k (φ (Q.coeff k))
  have hR : R = 0 := by
    refine Polynomial.funext fun u => ?_
    have h1 := congrArg φ (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [evU_apply, eval₂_eq_sum_range, map_sum, map_zero] at h1
    rw [eval_zero, ← h1]
    simp only [R, eval_finsetSum, eval_monomial, RingHom.id_apply, ← map_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have h2 := congrArg (fun p => p.coeff j) hR
  simp only [R, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, coeff_zero, Finset.sum_ite_eq', mem_range] at h2
  split_ifs at h2 with hj
  · exact h2
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem commute_coeff_of_evU (P : A[X]) (a : A) (h : ∀ u : ℂ, Commute (evU u P) a) (j : ℕ) :
    Commute (P.coeff j) a := by
  have hC : ∀ u : ℂ, evU u (C a) = a := fun u => by simp [evU_apply]
  have hQ : P * C a - C a * P = 0 := poly_eq_zero_of_evU _ fun u => by
    rw [map_sub, map_mul, map_mul, hC, sub_eq_zero]
    exact h u
  have h2 := congrArg (fun p => p.coeff j) hQ
  simp only [coeff_sub, coeff_mul_C, coeff_C_mul, coeff_zero] at h2
  exact sub_eq_zero.1 h2

theorem coeff_qdetPoly_mem {n : ℕ} (E : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (hS : ∀ p q, E p q ∈ S) (j : ℕ) : (qdetPoly E).coeff j ∈ S := by
  let f : S →+* A := S.val.toRingHom
  have hC : ∀ a ∈ S, C a ∈ liftsRing f := fun a ha => by
    rw [← lifts_iff_liftsRing]
    exact C_mem_lifts f ⟨a, ha⟩
  have hX : (X : A[X]) ∈ liftsRing f := by
    rw [← lifts_iff_liftsRing]
    exact X_mem_lifts f
  have hT : ∀ (k : ℕ) (a b : Fin n), tmPoly E k a b ∈ liftsRing f := fun k a b => by
    unfold tmPoly
    refine add_mem ?_ (hC _ (hS a b))
    split_ifs
    · exact sub_mem hX (hC _ (S.algebraMap_mem _))
    · exact zero_mem _
  have hP : qdetPoly E ∈ liftsRing f := by
    unfold qdetPoly
    refine sum_mem fun σ _ => mul_mem (hC _ (intCast_mem S _)) ?_
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hT _ _ _
  rw [← lifts_iff_liftsRing, lifts_iff_coeff_lifts] at hP
  obtain ⟨y, hy⟩ := hP j
  rw [← hy]
  exact y.2

end Poly

theorem capelli_coef_commute : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (M : ℕ) (d : Fin M → ℕ) (X : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W), (∀ i, GlRel (X i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (X i p q) (X j r v)) → ∃ c : Fin M → ℕ → Module.End ℂ W, (∀ i, c i (d i) = 1) ∧ (∀ i (u : ℂ), qdet (X i) u = ∑ j ∈ Finset.range (d i + 1), u ^ j • c i j) ∧ (∀ i, 1 ≤ d i → c i (d i - 1) = ∑ p, X i p p - (((d i : ℂ) * ((d i : ℂ) - 1) / 2)) • (1 : Module.End ℂ W)) ∧ ∀ i j a b, Commute (c i a) (c j b) := by
  intro W _ _ M d X hgl hcomm
  have hL : ∀ i a p q, Commute ((qdetPoly (X i)).coeff a) (X i p q) := fun i a p q =>
    commute_coeff_of_evU _ _ (fun u => by
      rw [evU_qdetPoly]
      exact Formalism.REAL.qDetCentral _ _ (X i) (hgl i) u p q) a
  have hL2 : ∀ i j a r v, Commute ((qdetPoly (X i)).coeff a) (X j r v) := by
    intro i j a r v
    by_cases hij : i = j
    · subst hij
      exact hL i a r v
    · have hm := coeff_qdetPoly_mem (X i) (Subalgebra.centralizer ℂ {X j r v}) (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hcomm i j hij p q r v).symm.eq) a
      rw [Subalgebra.mem_centralizer_iff] at hm
      exact (hm _ rfl).symm
  refine ⟨fun i j => (qdetPoly (X i)).coeff j, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, htop, -⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i) = 1
    rw [coeff_qdetPoly_top _ _ (by omega), htop]
  · intro i u
    rw [← evU_qdetPoly (X i) u, evU_apply,
      eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le (X i)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  · intro i hi
    obtain ⟨-, -, hsub⟩ := prod_linear (d i) fun k => X i k k - algebraMap ℂ (Module.End ℂ W) ((k : ℕ) : ℂ)
    show (qdetPoly (X i)).coeff (d i - 1) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_qdetPoly_top _ _ (by omega), hsub (d i - 1) (by omega), Finset.sum_sub_distrib,
      ← map_sum, sum_fin_cast, Algebra.algebraMap_eq_smul_one]
  · intro i j a b
    have hm := coeff_qdetPoly_mem (X j) (Subalgebra.centralizer ℂ {(qdetPoly (X i)).coeff a})
      (fun p q => by
        rw [Subalgebra.mem_centralizer_iff]
        rintro g rfl
        exact (hL2 i j a p q).eq) b
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm _ rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem card_lev_lt_succ {n : ℕ} (lev : Fin n → ℕ) (k : ℕ) :
    (univ.filter fun a => lev a < k + 1).card =
      (univ.filter fun a => lev a < k).card + (univ.filter fun a => lev a = k).card := by
  have hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_union]
  omega

theorem sum_sz_castLE {n M : ℕ} (lev : Fin n → ℕ) : ∀ (k : ℕ) (hk : k ≤ M),
    ∑ b : Fin k, sz lev M (Fin.castLE hk b) = (univ.filter fun a => lev a < k).card := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]
    rfl

theorem lt_card_iff {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (k : ℕ) (a : Fin n) :
    (a : ℕ) < (univ.filter fun b => lev b < k).card ↔ lev a < k := by
  constructor
  · intro h
    by_contra hn
    have hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact Finset.mem_Iio.2 (hm.reflect_lt (by omega))
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k) := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega

theorem lev_stdBlocks {n M : ℕ} (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (i : Fin M) (p : Fin (sz lev M i)) : lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ) := by
  have hv := stdBlocks_val (sz lev M) h i p
  rw [sum_sz_castLE lev (i : ℕ) i.2.le] at hv
  have hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card := p.2
  have h1 := lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)
  have h2 := lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)
  rw [card_lev_lt_succ] at h2
  have h3 := h2.1 (by omega)
  have h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ) := fun hl => by
    have := h1.2 hl
    omega
  omega

theorem stdBlocks_clusters : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  intro n M lev h hm _
  refine ⟨lev_stdBlocks lev h hm, fun f i => ?_⟩
  refine Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact lev_stdBlocks lev h hm i p
  · intro p _ q _ hpq
    have := (stdBlocks (sz lev M) h).injective hpq
    simpa using this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨⟨j, q⟩, rfl⟩ := (stdBlocks (sz lev M) h).surjective a
    have hj : j = i := Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)
    subst hj
    exact ⟨q, mem_univ _, rfl⟩
  · intro p _
    rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end

