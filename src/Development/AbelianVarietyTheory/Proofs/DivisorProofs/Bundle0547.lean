module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionPowAnalyticVectorNormLe
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockAnalytic

theorem totalDegree_pderiv_le_self {σ : Type} (i : σ) (Q : MvPolynomial σ ℂ) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff Q (m + Finsupp.single i 1) ≠ 0 := by
    rw [mem_support_iff, coeff_pderiv] at hm
    intro h
    rw [h, zero_mul] at hm
    exact hm rfl
  have h1 := le_totalDegree (mem_support_iff.2 hc)
  have h2 : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  rw [h2] at h1
  show (m.sum fun _ e => e) ≤ Q.totalDegree
  omega

def OneStep {σ : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : MvPolynomial σ ℂ →ₗ[ℂ] H) (A : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d →
    (A P).totalDegree ≤ d + 1 ∧ ‖ι (A P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2

section
variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem oneStep_mul (h : IsFockIP ι) (i : σ) : OneStep ι (LinearMap.mulLeft ℂ (X i)) := by
  intro d P hP
  refine ⟨?_, (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).1⟩
  rw [LinearMap.mulLeft_apply]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_X]; omega

theorem oneStep_pderiv (h : IsFockIP ι) (i : σ) : OneStep ι (pderiv i).toLinearMap := by
  intro d P hP
  refine ⟨((totalDegree_pderiv_le_self i P).trans hP).trans (Nat.le_succ _), ?_⟩
  have := (GlobalTheory.T.fock_norm_bounds_mul_X_pderiv σ H ι h i d P hP).2
  have h2 := sq_nonneg ‖ι P‖
  change ‖ι (pderiv i P)‖ ^ 2 ≤ _
  nlinarith

omit [DecidableEq σ] in
theorem OneStep.neg {A : Module.End ℂ (MvPolynomial σ ℂ)} (h : OneStep ι A) : OneStep ι (-A) := by
  intro d P hP
  simpa using h d P hP

omit [DecidableEq σ] in
theorem OneStep.comp {A B : Module.End ℂ (MvPolynomial σ ℂ)} (hA : OneStep ι A) (hB : OneStep ι B)
    (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.totalDegree ≤ d) :
    ((A * B) P).totalDegree ≤ d + 2 ∧ ‖ι ((A * B) P)‖ ≤ ((d : ℝ) + 3 / 2) * ‖ι P‖ := by
  obtain ⟨h1, h2⟩ := hB d P hP
  obtain ⟨h3, h4⟩ := hA (d + 1) _ h1
  refine ⟨h3, ?_⟩
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  push_cast at h4
  have h5 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (d : ℝ) + 1 + 1 by positivity)
  have h6 := sq_nonneg ‖ι P‖
  change ‖ι (A (B P))‖ ^ 2 ≤ _
  nlinarith
end

section
variable {p q r s : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Pol p q r s →ₗ[ℂ] H}

theorem omE_bound (h : IsFockIP ι) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s)
    (hP : P.totalDegree ≤ d) :
    (omE l l' P).totalDegree ≤ d + 2 ∧ ‖ι (omE l l' P)‖ ≤ ((d : ℝ) + 2) * ‖ι P‖ := by
  have hA : OneStep ι (raiB l) := by
    unfold raiB; split_ifs
    exacts [oneStep_mul h l, (oneStep_pderiv h l).neg]
  have hB : OneStep ι (lowB l') := by
    unfold lowB; split_ifs
    exacts [oneStep_pderiv h l', oneStep_mul h l']
  obtain ⟨h1, h2⟩ := hA.comp hB d P hP
  have hn := norm_nonneg (ι P)
  unfold omE
  split_ifs
  · rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    refine ⟨(totalDegree_add _ _).trans (max_le h1 ((totalDegree_smul_le _ _).trans (by omega))), ?_⟩
    rw [map_add (f := _), map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    linarith
  · rw [add_zero]
    exact ⟨h1, by linarith⟩

theorem omAct_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ)
    (P : Pol p q r s) (hP : P.totalDegree ≤ d) :
    (omAct p q r s Y P).totalDegree ≤ d + 2 ∧
      ‖ι (omAct p q r s Y P)‖ ≤ (∑ l, ∑ l', ‖Y l l'‖) * (((d : ℝ) + 2) * ‖ι P‖) := by
  have e : omAct p q r s Y P = ∑ l, ∑ l', Y l l' • omE l l' P := by
    simp [omAct, LinearMap.sum_apply]
  rw [e]
  constructor
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
    exact (totalDegree_smul_le _ _).trans (omE_bound h l l' d P hP).1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun l' _ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (omE_bound h l l' d P hP).2 (norm_nonneg _)

theorem omAct_pow_bound (h : IsFockIP ι) (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d m : ℕ)
    (hm : d ≤ 2 * m) (P : Pol p q r s) (hP : P.totalDegree ≤ d) (k : ℕ) :
    ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧
      ‖ι ((omAct p q r s Y ^ k) P)‖ ≤
        (2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖ := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    obtain ⟨h1, h2⟩ := omAct_bound h Y _ _ ih.1
    refine ⟨by omega, h2.trans ?_⟩
    have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
    have hm' : (d : ℝ) ≤ 2 * m := by exact_mod_cast hm
    rw [Nat.ascFactorial_succ]
    push_cast
    calc _ ≤ (∑ l, ∑ l', ‖Y l l'‖) * ((2 * ((m : ℝ) + 1 + k)) *
            ((2 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * ((m + 1).ascFactorial k : ℝ) * ‖ι P‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hS
          exact mul_le_mul (by linarith) ih.2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
end

theorem omAct_pow_norm_le : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Y : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d k : ℕ) (P : Pol p q r s), P.totalDegree ≤ d → ((omAct p q r s Y ^ k) P).totalDegree ≤ d + 2 * k ∧ ‖ι ((omAct p q r s Y ^ k) P)‖ ≤ (4 * ∑ l, ∑ l', ‖Y l l'‖) ^ k * (k.factorial : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2 + 1) * ‖ι P‖ := by
  intro p q r s H _ _ ι h Y d k P hP
  obtain ⟨h1, h2⟩ := omAct_pow_bound h Y d ((d + 1) / 2) (by omega) P hP k
  refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))⟩
  set m := (d + 1) / 2 with hm
  have hS : (0 : ℝ) ≤ ∑ l, ∑ l', ‖Y l l'‖ := by positivity
  generalize (∑ l, ∑ l', ‖Y l l'‖) = S at hS
  have hm1 : (m : ℝ) ≤ (d : ℝ) / 2 + 1 := by
    have : 2 * m ≤ d + 2 := by omega
    have : (2 * m : ℝ) ≤ d + 2 := by exact_mod_cast this
    linarith
  have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ ((d : ℝ) / 2 + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hm1
  have h4 : (((m + k).choose k : ℕ) : ℝ) ≤ 2 ^ (m + k) := by
    exact_mod_cast Nat.choose_le_two_pow (m + k) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  calc (2 * S) ^ k * ((k.factorial : ℝ) * ((m + k).choose k : ℝ))
      ≤ (2 * S) ^ k * ((k.factorial : ℝ) * 2 ^ (m + k)) := by gcongr
    _ = (4 * S) ^ k * (k.factorial : ℝ) * 2 ^ m := by
        rw [show (4 : ℝ) * S = 2 * (2 * S) by ring, mul_pow 2 (2 * S), pow_add]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.FockAnalytic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjoint
section
noncomputable section

open MvPolynomial Matrix Formalism.L2.DIV

namespace GlobalTheory.MinorFrame

variable {σ σ' : Type} [Fintype σ] [Fintype σ']

theorem constantCoeff_rsub (M : Matrix σ' σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (rsub M g) = constantCoeff g := by
  have : (constantCoeff : MvPolynomial σ' ℂ →+* ℂ).comp (rsub M).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [rsub_X]
  exact congrArg (fun φ : MvPolynomial σ ℂ →+* ℂ => φ g) this

theorem pderiv_rsub [DecidableEq σ] [DecidableEq σ'] (M : Matrix σ' σ ℂ) (s : σ') (g : MvPolynomial σ ℂ) :
    pderiv s (rsub M g) = ∑ w, C (M s w) * rsub M (pderiv w g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv s (rsub M (X k)) = C (M s k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [rsub_X, map_sum, Finset.sum_eq_single s]
      · simp [pderiv_X]
      · intro b _ hb
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne hb]
        simp
      · simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self, map_one]; ring
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]
        simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem fockL_rsub_adj (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ) :
    fockL (rsub M F) F' = fockL F (rsub Mᴴ F') := by
  classical
  induction F using MvPolynomial.induction_on generalizing F' with
  | C a => rw [algHom_C, algebraMap_eq, fockL_C_left, fockL_C_left, constantCoeff_rsub]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq]
  | mul_X p v hp =>
    have e1 : rsub M (p * X v) = ∑ w, M w v • (X w * rsub M p) := by
      rw [map_mul, rsub_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]; ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, LinearMap.sum_apply]
    simp_rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, fockL_X_pderiv, hp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm p, fockL_X_pderiv, pderiv_rsub, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, map_smul, Matrix.conjTranspose_apply, starRingEnd_apply]

theorem fockS_rsub_adj : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ)
    (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' =
      Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  intro σ σ' _ _ M F F'
  exact fockL_rsub_adj M F F'

end GlobalTheory.MinorFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.AxesPull

variable {R : Type} [CommRing R]

theorem isAffine_unit : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Sp R))

theorem pO1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pO1 g (pO1 f a) = pO1 (g ≫ f) a :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).1 a)

theorem pF_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : pF g (pF f a) = pF (g ≫ f) a :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.1 a)

theorem pH1_comp {X Y Z : Over (Sp R)} (g : X ⟶ Y) (f : Y ⟶ Z) (a) : deRhamH1Pullback g (deRhamH1Pullback f a) = deRhamH1Pullback (g ≫ f) a :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) f.left (ovw f) R X.left X.hom (RingHom.id R) g.left
    (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) fun _ ↦ rfl).2.2.2.1 a)

theorem pO1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pO1 (u ≫ f) a = 0 := by
  rw [← pO1_comp]
  haveI := ((GlobalTheory.AbCoh.Vanish.main.1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom isAffine_unit).1)
  rw [Subsingleton.elim (pO1 f a) 0, map_zero]

theorem pF_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    pF (u ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem pH1_unit {X Y : Over (Sp R)} (u : X ⟶ 𝟙_ (Over (Sp R))) (f : 𝟙_ (Over (Sp R)) ⟶ Y) (a) :
    deRhamH1Pullback (u ≫ f) a = 0 := by
  rw [← pH1_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).2
  rw [Subsingleton.elim (deRhamH1Pullback f a) 0, map_zero]

theorem main : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], (∀ a, pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (fst A A) a) = a ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 (snd A A) a) = 0 ∧ pO1 (lift (𝟙 A) (toUnit A ≫ η[A])) (pO1 μ[A] a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (fst A A) a) = 0 ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 (snd A A) a) = a ∧ pO1 (lift (toUnit A ≫ η[A]) (𝟙 A)) (pO1 μ[A] a) = a) ∧ (∀ a, pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) a) = a ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (snd A A) a) = 0 ∧ pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF μ[A] a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) a) = 0 ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (snd A A) a) = a ∧ pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF μ[A] a) = a) ∧ (∀ a, deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (fst A A) a) = a ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback (snd A A) a) = 0 ∧ deRhamH1Pullback (lift (𝟙 A) (toUnit A ≫ η[A])) (deRhamH1Pullback μ[A] a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (fst A A) a) = 0 ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback (snd A A) a) = a ∧ deRhamH1Pullback (lift (toUnit A ≫ η[A]) (𝟙 A)) (deRhamH1Pullback μ[A] a) = a) := by
  intro R _ A _
  have hid := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.2.2 R A)
  refine ⟨fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · simp only [pO1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pO1_unit, hid.1, and_self]
  · simp only [pF_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pF_unit, hid.2.2.1, and_self]
  · simp only [pH1_comp, lift_fst, lift_snd, lift_comp_one_right, lift_comp_one_left, pH1_unit, hid.2.2.2.1, and_self]

end GlobalTheory.AbCoh.AxesPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbCoh

theorem prod_pullback_sq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  intro R R' _ _ σ A _ A' _ φ h
  have pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom := IsPullback.of_hasPullback _ _
  obtain ⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left,
      Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ :=
    ⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),
      pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩
  have hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) := by
    have q := pA'.paste_horiz h.1
    rw [← h₁, ← h.1.w] at q
    have r := (IsPullback.of_right q h₂ pA).paste_vert h.1
    rwa [Over.w, Over.w] at r
  have one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left := by
    intro T
    let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have e : x₀ = 1 := mul_eq_left.1 hx
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    show (toUnit _ ≫ η[A]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  let Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A := Over.homMk Φ hP.w
  have hm := h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂
  rw [← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp,
    Over.comp_left] at hm
  refine ⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExp
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [DecidableEq ι]

theorem hasDerivAt_exp_ofReal_smul_entry {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  simp only [Complex.coe_smul]
  exact h2

theorem colDer_mul_X {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (v : Var ι d a) :
    colDer τ S (R * X v) = colDer τ S R * X v + R * colDer τ S (X v) := by
  simp only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_mul]
  simp only [smul_eq_C_mul]
  ring

theorem hasDerivAt_coeff_mul_X {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => AddMonoidAlgebra.coeff (A h) m) (AddMonoidAlgebra.coeff B m) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => AddMonoidAlgebra.coeff (A h * X w) m) (AddMonoidAlgebra.coeff (B * X w) m) 0 := by
  classical
  simp only [coeff_mul_X']
  split_ifs
  · exact hA _
  · exact hasDerivAt_const _ _

theorem hasDerivAt_coeff_colSub_of_curve [Fintype ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ)
    (g : ℝ → ι → Matrix (Fin a) (Fin a) ℂ) (h0 : g 0 = 1)
    (hg : ∀ σ i j, HasDerivAt (fun h => g h σ i j) (if σ = τ then S i j else 0) 0)
    (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (colSub (g h) R) m) (AddMonoidAlgebra.coeff (colDer τ S R) m) 0 := by
  have hone : ∀ P : Pol ι d a, colSub (g 0) P = P := by
    have : (colSub (g 0) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro y
      rw [h0]
      simp only [colSub, aeval_X, Pi.one_apply, AlgHom.id_apply]
      rw [Finset.sum_eq_single y.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    intro P
    rw [this, AlgHom.id_apply]
  induction R using MvPolynomial.induction_on generalizing m with
  | C c =>
    have h1 : colDer τ S (C c : Pol ι d a) = 0 := by simp [colDer_apply]
    simp only [h1, algHom_C, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact hasDerivAt_const _ _
  | add P Q hP hQ =>
    simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hP m).add (hQ m)
  | mul_X P v hP =>
    have e1 : ∀ h, AddMonoidAlgebra.coeff (colSub (g h) (P * X v)) m =
        ∑ k, g h v.1 k v.2.2 * AddMonoidAlgebra.coeff (colSub (g h) P * X (v.1, v.2.1, k)) m := by
      intro h
      rw [map_mul]
      conv_lhs => rw [show colSub (g h) (X v : Pol ι d a) = ∑ k, C (g h v.1 k v.2.2) * X (v.1, v.2.1, k) by
        simp [colSub]]
      rw [Finset.mul_sum, coeff_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, coeff_C_mul]
    simp only [e1]
    have hd := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hg v.1 k v.2.2).fun_mul (hasDerivAt_coeff_mul_X hP (v.1, v.2.1, k) m)
    refine hd.congr_deriv ?_
    rw [colDer_mul_X, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Finset.sum_add_distrib, add_comm]
    congr 1
    · rw [h0, Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj
        simp [Matrix.one_apply_ne hj]
      · simp
    · rw [colDer_X, hone]
      by_cases hv : v.1 = τ
      · subst hv
        simp only [if_true, Finset.mul_sum, coeff_sum, mul_smul_comm, coeff_smul, smul_eq_mul]
      · simp [hv]

theorem hasDerivAt_coeff_colSub_exp {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι)
    (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    HasDerivAt (fun h : ℝ => AddMonoidAlgebra.coeff (colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) R) m)
      (AddMonoidAlgebra.coeff (colDer τ S R) m) 0 := by
  refine hasDerivAt_coeff_colSub_of_curve τ S (fun h => atPl τ (NormedSpace.exp ((h : ℂ) • S))) ?_ ?_ R m
  · simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, atPl]
    exact Function.update_eq_self τ 1
  · intro σ i j
    by_cases h : σ = τ
    · subst h
      simp only [atPl, Function.update_self, if_true]
      exact hasDerivAt_exp_ofReal_smul_entry S i j
    · simp only [atPl, Function.update_of_ne h, if_neg h]
      exact hasDerivAt_const _ _

end GlobalTheory.ColLie

end
end

