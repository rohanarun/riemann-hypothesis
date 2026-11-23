module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitary
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.ZonalBound

theorem trivialBound_iff {q n : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n) (β : Fin (n / 2) → ℂˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β ↔
      ∀ i, ‖(β i : ℂ)‖ ≤ (q : ℝ) ^ (n - 1) ∧ ‖(β i : ℂ)‖⁻¹ ≤ (q : ℝ) ^ (n - 1) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have e : ((q : ℝ) ^ 2) ^ (((n : ℝ) - 1) / 2) = (q : ℝ) ^ (n - 1) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast, Nat.cast_sub hn, Nat.cast_one]
  have e' : ((q : ℝ) ^ 2) ^ (-(((n : ℝ) - 1) / 2)) = ((q : ℝ) ^ (n - 1))⁻¹ := by
    rw [Real.rpow_neg (by positivity), e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound
  rw [e, e']
  refine forall_congr' fun i => and_congr ?_ Iff.rfl |>.trans and_comm
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  exact ⟨fun h => inv_le_of_inv_le₀ (by positivity) h, fun h => inv_le_of_inv_le₀ hp h⟩

theorem trivialBound_of_ne_zero {q n : ℕ} (hq : 1 ≤ q) (β : Fin (n / 2) → ℂˣ)
    (h : ∀ i, ∀ X : ℂ, ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ →
      1 - (q : ℂ) ^ (n - 1) * X * (β i : ℂ) ≠ 0 ∧ 1 - (q : ℂ) ^ (n - 1) * X / (β i : ℂ) ≠ 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n β := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  rw [trivialBound_iff hq (by omega)]
  intro i
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set c : ℝ := (q : ℝ) ^ (n - 1) with hc
  have hc0 : 0 < c := by positivity
  have hcc : (q : ℝ) ^ (2 * (n - 1)) = c * c := by rw [hc, ← pow_add]; ring_nf
  have hcC : ‖((q : ℂ) ^ (n - 1))‖ = c := by rw [norm_pow, Complex.norm_natCast]
  have hcC0 : ((q : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hp : 0 < ‖(β i : ℂ)‖ := norm_pos_iff.2 (β i).ne_zero
  have hb0 : (β i : ℂ) ≠ 0 := (β i).ne_zero
  constructor
  · by_contra hlt
    push_neg at hlt
    have hX : ‖((q : ℂ) ^ (n - 1) * (β i : ℂ))⁻¹‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_inv, norm_mul, hcC, hcc]
      exact inv_strictAnti₀ (by positivity) (mul_lt_mul_of_pos_left hlt hc0)
    apply (h i _ hX).1
    field_simp
    ring
  · by_contra hlt
    push_neg at hlt
    have hX : ‖(β i : ℂ) / (q : ℂ) ^ (n - 1)‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := by
      rw [norm_div, hcC, hcc, div_lt_iff₀ hc0, mul_inv, mul_assoc, inv_mul_cancel₀ hc0.ne', mul_one]
      exact (lt_inv_comm₀ hp hc0).2 hlt
    apply (h i _ hX).2
    field_simp
    ring


open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
def denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) (X : ℂ) : ℂ :=
  (∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ))) * (if Odd n then 1 - c * X else 1)

theorem differentiable_denom (n : ℕ) (c : ℂ) (α : Fin (n / 2) → ℂˣ) : Differentiable ℂ (denom n c α) := by
  unfold denom
  by_cases h : Odd n
  · simp only [if_pos h]; fun_prop
  · simp only [if_neg h]; fun_prop

theorem one_sub_ne_zero {z : ℂ} (h : ‖z‖ < 1) : 1 - z ≠ 0 := fun e => by
  rw [← sub_eq_zero.1 e, norm_one] at h
  exact lt_irrefl _ h

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_mul_denom (q n : ℕ) (c X : ℂ) (α : Fin (n / 2) → ℂˣ) (h : Domain (c * X) α) :
    closedForm q n X (c * X) α * denom n c α X = ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) := by
  have h1 : (∏ i, (1 - c * X * (α i : ℂ))⁻¹ * (1 - c * X / (α i : ℂ))⁻¹) *
      ∏ i, (1 - c * X * (α i : ℂ)) * (1 - c * X / (α i : ℂ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    have a : 1 - c * X * (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_mul]; exact (h.2 i).1)
    have b : 1 - c * X / (α i : ℂ) ≠ 0 := one_sub_ne_zero (by rw [norm_div, div_eq_mul_inv]; exact (h.2 i).2)
    rw [mul_mul_mul_comm, inv_mul_cancel₀ a, inv_mul_cancel₀ b, one_mul]
  have h2 : (if Odd n then (1 - c * X)⁻¹ else 1) * (if Odd n then 1 - c * X else 1) = 1 := by
    split_ifs
    · exact inv_mul_cancel₀ (one_sub_ne_zero h.1)
    · exact one_mul _
  rw [closedForm, denom, mul_assoc (∏ j ∈ Finset.range n, _), mul_assoc (∏ j ∈ Finset.range n, _),
    mul_mul_mul_comm, h1, h2, one_mul, mul_one]

theorem numer_ne_zero {q n : ℕ} (hq : 1 ≤ q) {X : ℂ} (hX : ‖X‖ < ((q : ℝ) ^ (2 * (n - 1)))⁻¹) :
    ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X) ≠ 0 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine Finset.prod_ne_zero_iff.2 fun j hj => one_sub_ne_zero ?_
  have hj' := Finset.mem_range.1 hj
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_natCast]
  calc (q : ℝ) ^ j * ‖X‖ ≤ (q : ℝ) ^ (2 * (n - 1)) * ‖X‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega)) (norm_nonneg _)
    _ < (q : ℝ) ^ (2 * (n - 1)) * ((q : ℝ) ^ (2 * (n - 1)))⁻¹ := mul_lt_mul_of_pos_left hX (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)


open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem domain_of_bound {r : ℕ} {y : ℂ} {α : Fin r → ℂˣ} {M : ℝ} (hM : 1 ≤ M)
    (hα : ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M) (hy : ‖y‖ * M < 1) : Domain y α := by
  have key : ∀ a : ℝ, a ≤ M → ‖y‖ * a < 1 := fun a ha =>
    (mul_le_mul_of_nonneg_left ha (norm_nonneg _)).trans_lt hy
  exact ⟨by simpa using key 1 hM, fun i => ⟨key _ (hα i).1, key _ (hα i).2⟩⟩

theorem exists_bound {r : ℕ} (α : Fin r → ℂˣ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i, ‖(α i : ℂ)‖ ≤ M ∧ ‖(α i : ℂ)‖⁻¹ ≤ M := by
  have h0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), 0 ≤ ‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹ := fun i _ => by positivity
  refine ⟨1 + ∑ i, (‖(α i : ℂ)‖ + ‖(α i : ℂ)‖⁻¹), le_add_of_nonneg_right (Finset.sum_nonneg h0), fun i => ?_⟩
  have h1 := Finset.single_le_sum h0 (Finset.mem_univ i)
  have h2 : 0 ≤ ‖(α i : ℂ)‖ := norm_nonneg _
  have h3 : 0 ≤ ‖(α i : ℂ)‖⁻¹ := by positivity
  constructor <;> linarith


open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem exists_deg {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ)
    {σ : L →+* L} {q n : ℕ} (hU : IsUnramInv (ϖ : L) σ q) (hn : 1 ≤ n) :
    ∃ deg : GU σ n ⧸ KU σ n → ℕ, ∀ X : ℂ, X ≠ 0 → ∃ (χ : Lˣ →* ℂˣ) (s : ℂ) (Φ : GD σ n → ℂ), IsUnr χ ∧
      IsSphSec σ q n χ s Φ ∧ varX q n (χ ϖ) s = X ∧ varY q (χ ϖ) s = (q : ℂ) ^ (n - 1) * X ∧
      (∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = Φ (io1 σ n g)) ∧
      ∀ a : GU σ n ⧸ KU σ n, Φ (io1 σ n a.out) = X ^ deg a := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hc := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU
  choose D t ht k₁ hk₁ k₂ hk₂ e using hc
  refine ⟨fun a => (∑ i, max (D a.out i) 0).toNat, fun X hX => ?_⟩
  obtain ⟨χ, hχ, hχϖ⟩ := GlobalTheory.ZetaSumU.exists_unr_char ϖ hU
    (Units.mk0 (X * (q : ℂ) ^ n) (mul_ne_zero hX (pow_ne_zero _ hqC)))
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq n hχ (((0 : ℕ) : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := GlobalTheory.ZetaSumU.varXY_eq q n 0 hq2 (X * (q : ℂ) ^ n)
  have hz : ((χ ϖ : ℂˣ) : ℂ) = X * (q : ℂ) ^ n := by rw [hχϖ]; rfl
  have hvX : varX q n (χ ϖ) (((0 : ℕ) : ℂ) / 2) = X := by
    rw [hz, hXe, add_zero, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hqC), mul_one]
  have hval : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) = X ^ (∑ i, max (D g i) 0) := fun g k hk => by
    have h := _root_.GlobalTheory.UGraph.sphSec_io_diag L ϖ σ q n hU χ hχ _ Φ hΦ (D g) (t g) (ht g) (k₁ g) (hk₁ g) (k₂ g * k)
      (mul_mem (hk₂ g) hk)
    rw [hvX, ← mul_assoc, ← e g] at h
    exact h
  have hval1 : ∀ g, Φ (io1 σ n g) = X ^ (∑ i, max (D g i) 0) := fun g => by
    simpa only [mul_one] using hval g 1 (one_mem _)
  refine ⟨χ, _, Φ, hχ, hΦ, hvX, ?_, fun g k hk => (hval g k hk).trans (hval1 g).symm, fun a => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [hz, hYe, Nat.add_sub_cancel, zero_add, pow_one, pow_succ]
    field_simp
  · rw [hval1, ← zpow_natCast, Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => le_max_right _ _)]


open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem trivialBound_of_bounded : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ (α : Fin (n / 2) → ℂˣ) (w : GU σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal (ϖ : L) q α w → (∃ C : ℝ, ∀ g, ‖w g‖ ≤ C) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q n α := by
  intro H L _ _ _ ϖ σ q n hU α w hw hb
  obtain ⟨C, hC⟩ := hb
  rcases Nat.lt_or_ge n 2 with hn | hn
  · intro i; exact absurd i.2 (by omega)
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  obtain ⟨deg, hdeg⟩ := exists_deg ϖ hU (by omega : 1 ≤ n)
  letI : MeasurableSpace (GU σ n) := borel _
  haveI : BorelSpace (GU σ n) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L (ϖ : L) σ q n hU).1
  have hc1 : (1 : ℝ) ≤ (q : ℝ) ^ (n - 1) := one_le_pow₀ hq1
  have hc0 : (0 : ℝ) < (q : ℝ) ^ (n - 1) := by positivity
  have hny : ∀ x : ℝ, 0 < x → ‖(q : ℂ) ^ (n - 1) * (x : ℂ)‖ = (q : ℝ) ^ (n - 1) * x := fun x hx => by
    rw [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hx.le]

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU n
  have hb0 := (trivialBound_iff (by omega) (by omega) α0).1 (GlobalTheory.ZetaSumU.tb_triv q n hq2 α0 hα0)
  have hsum : ∀ r : ℝ, 0 < r → r < ((q : ℝ) ^ (2 * (n - 1)))⁻¹ → Summable fun a => r ^ deg a := fun r hr hρ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, -, hY, hinv, hval⟩ := hdeg (r : ℂ) (by exact_mod_cast hr.ne')
    have hdom : Domain (varY q (χ ϖ) s) α0 := by
      rw [hY]
      refine domain_of_bound hc1 hb0 ?_
      rw [hny r hr, mul_right_comm, ← pow_add, ← two_mul]
      exact (mul_lt_mul_of_pos_left hρ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    have hint := ((H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α0 _ hw0).1 hdom).1
    have hs := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ (fun g k hk => by simp only [hinv g k hk]) hint
    refine hs.congr fun a => ?_
    simp only [hval, mul_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr.le]

  obtain ⟨M, hM, hαM⟩ := exists_bound α
  have heq : ∀ x : ℝ, 0 < x → x < ((q : ℝ) ^ (n - 1) * M)⁻¹ →
      (∑' a : GU σ n ⧸ KU σ n, w a.out * (x : ℂ) ^ deg a) * denom n ((q : ℂ) ^ (n - 1)) α x =
        ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * (x : ℂ)) := fun x hx hδ => by
    obtain ⟨χ, s, Φ, hχ, hΦ, hX, hY, hinv, hval⟩ := hdeg (x : ℂ) (by exact_mod_cast hx.ne')
    have hdom : Domain ((q : ℂ) ^ (n - 1) * (x : ℂ)) α := by
      refine domain_of_bound hM hαM ?_
      rw [hny x hx, mul_right_comm]
      exact (mul_lt_mul_of_pos_left hδ (by positivity)).trans_eq (mul_inv_cancel₀ (by positivity))
    obtain ⟨hint, hI, -⟩ := (H L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α w hw).1 (by rw [hY]; exact hdom)
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (io1 σ n (g * k)) * w (g * k) = Φ (io1 σ n g) * w g := fun g k hk => by
      have h1 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h1
      rw [hinv g k hk, h1]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (_root_.GlobalTheory.InertZeta.cosetIntegral_holds _ μ (KU σ n) hKo hμK (fun g => Φ (io1 σ n g) * w g) _ hF hs.hasSum).2
    rw [hI, hX, hY] at hci
    rw [← closedForm_mul_denom q n _ _ α hdom, hci]
    congr 1
    exact tsum_congr fun a => by rw [hval, mul_comm]
  refine trivialBound_of_ne_zero (by omega) α fun i X hX => ?_
  have hP := GlobalTheory.gradedSeries_mul_ne_zero (GU σ n ⧸ KU σ n) deg (fun a => w a.out) ((q : ℝ) ^ (2 * (n - 1)))⁻¹
    ((q : ℝ) ^ (n - 1) * M)⁻¹ (denom n ((q : ℂ) ^ (n - 1)) α)
    (fun X => ∏ j ∈ Finset.range n, (1 - (-(q : ℂ)) ^ j * X)) (by positivity) (differentiable_denom _ _ _)
    (by fun_prop)
    (fun r hr hρ => Summable.of_nonneg_of_le (fun a => by positivity)
      (fun a => mul_le_mul_of_nonneg_right (hC _) (by positivity)) ((hsum r hr hρ).mul_left C))
    heq X hX (numer_ne_zero (by omega) hX)
  exact mul_ne_zero_iff.1 (Finset.prod_ne_zero_iff.1 (mul_ne_zero_iff.1 hP).1 i (Finset.mem_univ i))

end GlobalTheory.ZonalBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalHeckeOperatorEqSmulOfLocalParameter
section
noncomputable section

namespace GlobalTheory.LFun.EigLoc

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section General

variable {G H : Type} [Group G] [Group H]

theorem comp_symm_mem_hecke (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) : φ ∘ e.symm ∈ Hecke ℂ K' := by
  classical
  have hφ' : IsBiInv K φ ∧ FinDosetSupp K φ := hφ
  obtain ⟨hb, S, hS⟩ := hφ'
  have hsymm : ∀ y : H, y ∈ K' → e.symm y ∈ K := fun y hy => by
    rw [hK, MulEquiv.apply_symm_apply]; exact hy
  show IsBiInv K' (φ ∘ e.symm) ∧ FinDosetSupp K' (φ ∘ e.symm)
  refine ⟨fun a b g => ?_, ⟨S.image e, fun g hg => ?_⟩⟩
  · have := hb ⟨_, hsymm a a.2⟩ ⟨_, hsymm b b.2⟩ (e.symm g)
    simpa only [Function.comp_apply, map_mul] using this
  · obtain ⟨s, hs, a, b, hab⟩ := hS (e.symm g) hg
    refine ⟨e s, ?_, ⟨e a, (hK _).1 a.2⟩, ⟨e b, (hK _).1 b.2⟩, ?_⟩
    · exact Finset.mem_image_of_mem _ hs
    · have := congrArg e hab
      simpa only [MulEquiv.apply_symm_apply, map_mul] using this

theorem heckeVec_eq_comp_symm {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    {φ : G → ℂ} (hφ : φ ∈ Hecke ℂ K) {x : V} (hx : x ∈ fixed ρ K) :
    heckeVec ρ K φ x = heckeVec (ρ.comp e.symm.toMonoidHom) K' (φ ∘ e.symm) x := by
  classical
  have hfix : ∀ k, k ∈ K → ρ k x = x := fun k hk => by
    have hx' : ∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x := hx
    simpa using hx' ⟨k, hk⟩
  have hT : ∀ g k, k ∈ K → φ (g * k) • ρ (g * k) x = φ g • ρ g x := by
    intro g k hk
    have hb : IsBiInv K φ := hφ.1
    have h1 : φ (g * k) = φ g := by simpa using hb 1 ⟨k, hk⟩ g
    rw [h1, map_mul, mul_apply_eq_comp, hfix k hk]
  let Q : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, map_mul, map_inv])
  have hQ : ∀ g : G, Q (g : G ⧸ K) = ((e g : H) : H ⧸ K') := fun g => rfl
  unfold heckeVec
  rw [← finsum_comp_equiv Q]
  refine finsum_congr fun c => ?_
  have h1 : (((Q c).out : H) : H ⧸ K') = ((e c.out : H) : H ⧸ K') := by
    rw [QuotientGroup.out_eq', ← hQ, QuotientGroup.out_eq']
  have h2 : (e c.out)⁻¹ * (Q c).out ∈ K' := QuotientGroup.eq.1 h1.symm
  have h3 : c.out⁻¹ * e.symm (Q c).out ∈ K := by
    rw [hK]
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h2
  have h4 := hT c.out _ h3
  rw [mul_inv_cancel_left] at h4
  exact h4.symm

private theorem cell_unif_lemma {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (a : Fin m → ℤ) (y : GU c n)
    (H : ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :
    ∃ u : GU c n, IsUnipU u ∧ ∃ k ∈ KU c n,
      (((y : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        tMat ϖ' n m a * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((k : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  obtain ⟨u, hu, k, hk, hy⟩ := H
  have hne : ∀ t : L, IsUnramInv t c q → t ≠ 0 := fun t ht h0 => by
    have h := ht.2.2.2.1
    simp [h0] at h
  have hg0 : ∀ t : L, t ≠ 0 → ∀ i, tMat t n m a i i ≠ 0 := by
    intro t ht i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> first | exact zpow_ne_zero _ ht | exact one_ne_zero
  have hvv : Valued.v ϖ = Valued.v ϖ' := hU.2.2.2.1.trans hU'.2.2.2.1.symm
  have hgv : ∀ i, Valued.v (tMat ϖ n m a i i) = Valued.v (tMat ϖ' n m a i i) := by
    intro i
    simp only [tMat, Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [map_zpow₀, hvv]
  have htm : ∀ t : L, tMat t n m a = Matrix.diagonal (fun i => tMat t n m a i i) := by
    intro t
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      simp only [tMat, Matrix.diagonal_apply_ne _ hij]
  set e : Fin n → L := fun i => tMat ϖ n m a i i / tMat ϖ' n m a i i with he_def
  have he0 : ∀ i, e i ≠ 0 := fun i => div_ne_zero (hg0 ϖ (hne ϖ hU) i) (hg0 ϖ' (hne ϖ' hU') i)
  obtain ⟨t, ht⟩ := Formalism.UG.P.fSatake_tMat_exists hU hm a
  obtain ⟨t', ht'⟩ := Formalism.UG.P.fSatake_tMat_exists hU' hm a
  have hb : ∀ i, c (tMat ϖ n m a i i) * tMat ϖ n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht) i
    rwa [ht] at this
  have hb' : ∀ i, c (tMat ϖ' n m a i i) * tMat ϖ' n m a i.rev i.rev = 1 := fun i => by
    have := Formalism.UG.P.fSatake_unit_diag (Formalism.UG.P.fSatake_borel_tMat ht') i
    rwa [ht'] at this
  have hce : ∀ i, c (e i) * e i.rev = 1 := fun i => by
    simp only [he_def, map_div₀]
    rw [div_mul_div_comm, hb i, hb' i, div_one]
  obtain ⟨D, hD, hD'⟩ := Formalism.UG.P.fSatake_diag_exists e hce
  have hev : ∀ i, Valued.v (e i) = 1 := fun i => by
    simp only [he_def]
    rw [map_div₀, hgv i, div_self]
    exact (Valuation.ne_zero_iff _).2 (hg0 ϖ' (hne ϖ' hU') i)
  have hDK : D ∈ KU c n := Formalism.UG.P.fSatake_diag_mem_K hD hD' hev
  have hDD : (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have hsplit : tMat ϖ n m a = tMat ϖ' n m a * (((D : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hD, htm ϖ, htm ϖ', Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_div_cancel₀ _ (hg0 ϖ' (hne ϖ' hU') i)]
  obtain ⟨hub, hud⟩ := hu
  refine ⟨D * u * D⁻¹, ?_, D * k, Subgroup.mul_mem _ hDK hk, ?_⟩
  · have hmat : ∀ i j, (((D * u * D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
        e i * (((u : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j * (e j)⁻¹ := by
      intro i j
      simp only [Subgroup.coe_mul, Units.val_mul, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul]
    unfold IsUnipU IsBorelU
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmat, hub i j hij, mul_zero, zero_mul]
    · rw [hmat, hud i, mul_one, mul_inv_cancel₀ (he0 i)]
  · rw [hy, hsplit]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((D⁻¹ : GU c n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hDD, Matrix.one_mul]

private theorem satU_eq_of_isUnramInv {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}
    {n q m : ℕ} {ϖ ϖ' : L} (hU : IsUnramInv ϖ c q) (hU' : IsUnramInv ϖ' c q) (hm : 2 * m ≤ n)
    (f : GU c n → ℂ) (α : Fin m → ℂ) : SatU ϖ q f α = SatU ϖ' q f α := by
  unfold SatU
  refine finsum_congr fun a => ?_
  congr 1
  refine finsum_congr fun x => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (cell_unif_lemma hU hU' hm a _ h1) h2
  · exact absurd (cell_unif_lemma hU' hU hm a _ h2) h1
  · rfl

end General

theorem heckeVec_eq_smul_of_isParamVec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v) (B : Multiset ℂˣ), ∀ φ ∈ Hecke ℂ (stabLoc σ J L v), ∃ z : ℂ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLoc σ J v) V) (x : V), IsParamVec σ J L h ρ x B → heckeVec ρ (stabLoc σ J L v) φ x = z • x := by
  intro F E _ _ _ _ _ σ n J L v w h B φ hφ
  classical
  by_cases hsp : IsSplit (E := E) v ∧
      ∃ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e
  · obtain ⟨hv, e0, he0⟩ := hsp
    obtain ⟨z, hz⟩ := GlobalTheory.T.satake_determines_sphericalHeckeCharacter_GL E w n B (φ ∘ e0.symm) (comp_symm_mem_hecke e0 he0.2 hφ)
    refine ⟨z, fun V _ _ ρ x hx => ?_⟩
    rw [heckeVec_eq_comp_symm e0 he0.2 hφ hx.mem_fixed]
    exact hz V (ρ.comp e0.symm.toMonoidHom) x (hx.isSatVecGL hv he0)
  by_cases hin : ∃ (c : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E)
      (e : GLoc σ J v ≃* GU c n) (α : Fin (n / 2) → ℂˣ),
      IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ B = GlobalTheory.LGrp.bcParam n α
  · obtain ⟨c0, ϖ0, e0, α0, hU0, hC0, hB0⟩ := hin
    have hmem := comp_symm_mem_hecke e0 hC0.2.2 hφ
    refine ⟨SatU ϖ0 (qV F v) (φ ∘ e0.symm) (fun i => (α0 i : ℂ)), fun V _ _ ρ x hx => ?_⟩
    have hfx := hx.mem_fixed
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, hS, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · obtain rfl : c = c0 := IsConjAt.unique hC.1 hC0.1
      have hS0 := IsSatVecU.of_chart hC hC0 hS
      rw [heckeVec_eq_comp_symm e0 hC0.2.2 hφ hfx, hS0.2.2 _ hmem]
      congr 1
      rw [satU_eq_of_isUnramInv hU hU0 (Nat.mul_div_le n 2)]
      exact _root_.GlobalTheory.SatBc.satU_eq_of_bcParam_eq _ ϖ0 c (qV F v) n hU0 α α0 (hB.symm.trans hB0) _ hmem
  · refine ⟨0, fun V _ _ ρ x hx => ?_⟩
    rcases hx with ⟨hv, e, he, -⟩ | ⟨-, c, ϖ, e, α, hU, hC, -, hB⟩
    · exact (hsp ⟨hv, e, he⟩).elim
    · exact (hin ⟨c, ϖ, e, α, hU, hC, hB⟩).elim

end GlobalTheory.LFun.EigLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorsWittParabolicOriginToPoint
section
namespace I195MixedCoordinates_496aa803720ccf0c37cbff80

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_496aa803720ccf0c37cbff80

public noncomputable abbrev _root_.I195MixedCoordinates_3601ff04f10fcda6f28caf89.source :=
  @_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WMove

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → ∀ x : Mx D T.rank ρ, (∀ h, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (1, h) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (1, h) (heisO ψ S T (d.extX T (mt T h⁻¹ ⬝ x)) f)) 0) ∧ (∀ a g, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) (heisO ψ S T (d.extX T (x ⬝ a.1)) f)) 0) ∧ ∀ n : GA D S, (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (n, 1) f) x = (_root_.I195MixedCoordinates_496aa803720ccf0c37cbff80.source d) T ψ μ 𝓕 (om (n, 1) (heisO ψ S T (d.extX T x ⬝ mt S n) f)) 0 := by
  intro D ψ S S₀ T ρ d χS χT om hω μ 𝓕 hμ f hf x
  have hb := fun F y => ((_root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 F y)
  change ∀ (F : WO S T → ℂ) (y : Mx D T.rank ρ),
    I195MixedCoordinates_496aa803720ccf0c37cbff80.source d T ψ μ 𝓕 F y =
      I195MixedCoordinates_496aa803720ccf0c37cbff80.source d T ψ μ 𝓕 (heisO ψ S T (d.extX T y) F) 0 at hb
  refine ⟨fun h => ?_, fun a g => ?_, fun n => ?_⟩
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extX_apply, HypDec.extX_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, _root_.mul_inv_rev, ← map_inv d.levi, ← map_inv d.emb0, mt_mul,
      ← Matrix.mul_assoc, d.extX_apply T (x ⬝ a.1), Matrix.mul_assoc _ d.pX, d.wittDecomp_projX_anisotropicEmbedding, ← d.extX_apply T (x ⬝ a.1),
      d.extX_levi, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · rw [hb, hω.om_heis _ _ _ _ hf]
    congr 3
    rw [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

end GlobalTheory.WMove
end

