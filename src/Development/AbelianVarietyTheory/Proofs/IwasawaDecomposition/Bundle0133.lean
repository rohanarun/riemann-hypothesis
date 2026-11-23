module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.DiscRoot

open Polynomial _root_.WeierstrassCurve

theorem exists_vieta_two (p q : ℂ) : ∃ x y : ℂ, x + y = p ∧ x * y = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * q) (show 0 < 2 by norm_num)
  exact ⟨(p + s) / 2, (p - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

theorem exists_vieta_three (p q r : ℂ) :
    ∃ x y z : ℂ, x + y + z = p ∧ x * y + x * z + y * z = q ∧ x * y * z = r := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]) (by
    have : (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]).degree = 3 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, h1, h2⟩ := exists_vieta_two (p - x) (q - x * (p - x))
  exact ⟨x, y, z, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + hx⟩

theorem exists_vieta_four (p q r t : ℂ) :
    ∃ x y z w : ℂ, x + y + z + w = p ∧ x * y + x * z + x * w + y * z + y * w + z * w = q ∧
      x * y * z + x * y * w + x * z * w + y * z * w = r ∧ x * y * z * w = t := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]) (by
    have : (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]).degree = 4 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, w, h1, h2, h3⟩ := exists_vieta_three (p - x) (q - x * (p - x)) (r - x * (q - x * (p - x)))
  exact ⟨x, y, z, w, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + h3,
    by linear_combination x * h3 - hx⟩

variable {W : WeierstrassCurve ℂ}

theorem four_torsion (hΔ : W.Δ ≠ 0) {e s t : ℂ} (h2 : W.b₂ = -4 * (3 * e - s ^ 2 - t ^ 2))
    (h4 : W.b₄ = 2 * (e * (e - s ^ 2) + e * (e - t ^ 2) + (e - s ^ 2) * (e - t ^ 2)))
    (h6 : W.b₆ = -4 * (e * (e - s ^ 2) * (e - t ^ 2))) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    e + s * t ∈ torsionCoords W 4 ∧
      s * t * (s + t) - (W.a₁ * (e + s * t) + W.a₃) / 2 ∈ torsionCoords W 4 := by
  simp only [b₂, b₄, b₆] at h2 h4 h6
  set x := e + s * t with hx
  set y := s * t * (s + t) - (W.a₁ * x + W.a₃) / 2 with hy
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (-(e + s * t) ^ 2 / 4) * h2 - (e + s * t) / 2 * h4 - 1 / 4 * h6
  have hns : W.toAffine.Nonsingular x y := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 heq
  have hd : y - W.toAffine.negY x y = 2 * (s * t * (s + t)) := by
    simp only [Affine.negY, toAffine]
    rw [hy]; ring
  have hd0 : y - W.toAffine.negY x y ≠ 0 := by
    rw [hd]; exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hst)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 hd0
  have hl : W.toAffine.slope x x y y = s + t - W.a₁ / 2 := by
    rw [Affine.slope_of_Y_ne rfl hne, div_eq_iff hd0, hd]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (e + s * t) / 2 * h2 + 1 / 2 * h4
  have h0 : 4 • Affine.Point.some x y hns = 0 := by
    rw [show 4 = 2 * 2 from rfl, mul_smul, two_smul, two_smul, Affine.Point.add_self_of_Y_ne hne]
    apply Affine.Point.add_self_of_Y_eq
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hl, toAffine]
    rw [hy, hx]
    linear_combination (s + t) / 2 * h2
  exact ⟨⟨x, y, hns, h0, Or.inl rfl⟩, ⟨x, y, hns, h0, Or.inr rfl⟩⟩

theorem three_torsion (hΔ : W.Δ ≠ 0) {x : ℂ}
    (h : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0) : x ∈ torsionCoords W 3 := by
  simp only [b₂, b₄, b₆, b₈] at h
  obtain ⟨y, y', h1, h2⟩ := exists_vieta_two (-(W.a₁ * x + W.a₃)) (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    linear_combination y * h1 - h2
  have hns : W.toAffine.Nonsingular x y :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 ((Affine.equation_iff _ _).2 heq)
  have key : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2 +
      W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) =
      (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination -h - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * heq
  have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [Affine.negY, toAffine]; ring
  have hd0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    rw [h0] at key
    have h3 : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 := by
      apply pow_eq_zero_iff (n := 2) two_ne_zero |>.1
      linear_combination key
    rcases ((Affine.nonsingular_iff _ _).1 hns).2 with h4 | h4
    · exact h4 (by simp only [toAffine]; linear_combination -h3)
    · exact h4 (by simp only [toAffine]; linear_combination h0)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 (hd ▸ hd0)
  have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [Affine.slope_of_Y_ne rfl hne, hd, div_mul_cancel₀ _ hd0]
    rw [← hl] at key
    simp only [Affine.addX, toAffine] at key ⊢
    apply mul_right_cancel₀ (pow_ne_zero 2 hd0)
    linear_combination key
  refine ⟨x, y, hns, ?_, Or.inl rfl⟩
  rw [show 3 = 2 + 1 from rfl, add_smul, two_smul, one_smul, Affine.Point.add_self_of_Y_ne hne]
  apply Affine.Point.add_of_Y_eq hX
  simp only [Affine.addY, Affine.negAddY, hX, sub_self, mul_zero, zero_add]

variable {M : IntermediateField ℚ ℂ}

theorem sqrt_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {e₁ e₂ e₃ s : ℂ}
    (h2 : W.b₂ = -4 * (e₁ + e₂ + e₃)) (h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)) (h6 : W.b₆ = -4 * (e₁ * e₂ * e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (hs : s ^ 2 = e₁ - e₂) : s ∈ M := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  have key : ∀ t : ℂ, t ^ 2 = e₁ - e₃ → s * t ≠ 0 ∧ e₁ + s * t ∈ M ∧ s * t * (s + t) ∈ M := by
    intro t ht
    have hs0 : s ≠ 0 := fun h => h12 (by rw [h] at hs; linear_combination -hs)
    have ht0 : t ≠ 0 := fun h => h13 (by rw [h] at ht; linear_combination -ht)
    have hst : s + t ≠ 0 := fun h => h23 (by linear_combination hs - ht - (s - t) * h)
    obtain ⟨k1, k2⟩ := four_torsion (e := e₁) hΔ (by rw [hs, ht, h2]; ring) (by rw [hs, ht, h4]; ring)
      (by rw [hs, ht, h6]; ring) hs0 ht0 hst
    have k1 : e₁ + s * t ∈ M := hM k1
    have k2 : _ ∈ M := hM k2
    refine ⟨mul_ne_zero hs0 ht0, k1, ?_⟩
    have := add_mem k2 (div_mem (add_mem (mul_mem ha₁ k1) ha₃) (ofNat_mem M 2))
    rwa [sub_add_cancel] at this
  obtain ⟨h0, k1, k2⟩ := key t ht
  obtain ⟨-, k3, k4⟩ := key (-t) (by rw [neg_sq, ht])
  have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : t ≠ 0 := right_ne_zero_of_mul h0
  have : s = (s * t * (s + t) - s * -t * (s + -t)) / ((e₁ + s * t) - (e₁ + s * -t)) := by
    rw [eq_div_iff (by
      rw [show (e₁ + s * t) - (e₁ + s * -t) = 2 * (s * t) by ring]
      exact mul_ne_zero two_ne_zero h0)]
    ring
  rw [this]
  exact div_mem (sub_mem k2 k4) (sub_mem k1 k3)

theorem fourth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {c : ℂ}
    (hc : c ^ 4 = W.Δ) : c ∈ M := by
  obtain ⟨e₁, e₂, e₃, k2, k4, k6⟩ := exists_vieta_three (-W.b₂ / 4) (W.b₄ / 2) (-W.b₆ / 4)
  have h2 : W.b₂ = -4 * (e₁ + e₂ + e₃) := by linear_combination 4 * k2
  have h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by linear_combination -2 * k4
  have h6 : W.b₆ = -4 * (e₁ * e₂ * e₃) := by linear_combination 4 * k6
  have h8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by linear_combination W.b_relation / 4
  have hD : W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [Δ, h8, h2, h4, h6]; ring
  have h12 : e₁ ≠ e₂ := fun h => hΔ (by rw [hD, h]; ring)
  have h13 : e₁ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  have h23 : e₂ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₂) (show 0 < 2 by norm_num)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₃) (show 0 < 2 by norm_num)
  have ms : s ∈ M := sqrt_mem hΔ ha₁ ha₃ hM h2 h4 h6 h12 h13 h23 hs
  have mt : t ∈ M := sqrt_mem (e₁ := e₁) (e₂ := e₃) (e₃ := e₂) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h13 h12 h23.symm ht
  have mu : u ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₃) (e₃ := e₁) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h23 h12.symm h13.symm hu
  have mi : Complex.I * s ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) hΔ ha₁ ha₃ hM (by rw [h2]; ring)
    (by rw [h4]; ring) (by rw [h6]; ring) h12.symm h23 h13 (by rw [mul_pow, Complex.I_sq, hs]; ring)
  have mb : 2 * (s * t * u) ∈ M := mul_mem (ofNat_mem M 2) (mul_mem (mul_mem ms mt) mu)
  have mb' : Complex.I * (2 * (s * t * u)) ∈ M := by
    rw [show Complex.I * (2 * (s * t * u)) = 2 * (Complex.I * s * t * u) by ring]
    exact mul_mem (ofNat_mem M 2) (mul_mem (mul_mem mi mt) mu)
  have hb : (2 * (s * t * u)) ^ 4 = c ^ 4 := by
    rw [hc, hD, ← hs, ← ht, ← hu]; ring
  generalize 2 * (s * t * u) = b at mb mb' hb
  have hf : (c - b) * (c + b) * ((c - Complex.I * b) * (c + Complex.I * b)) = 0 := by
    linear_combination -hb - (c ^ 2 - b ^ 2) * b ^ 2 * Complex.I_sq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h | h <;> rw [h]
  exacts [mb, neg_mem mb, mb', neg_mem mb']

theorem cube_root_mem (hΔ : W.Δ ≠ 0) (hM : torsionCoords W 3 ⊆ M) {c : ℂ} (hc : c ^ 3 = W.Δ) : c ∈ M := by
  obtain ⟨x, y, z, w, k2, k4, k6, k8⟩ := exists_vieta_four (-W.b₂ / 3) W.b₄ (-W.b₆) (W.b₈ / 3)
  have h2 : W.b₂ = -3 * (x + y + z + w) := by linear_combination 3 * k2
  have h4 := k4.symm
  have h6 : W.b₆ = -(x * y * z + x * y * w + x * z * w + y * z * w) := by linear_combination k6
  have h8 : W.b₈ = 3 * (x * y * z * w) := by linear_combination -3 * k8
  have mx : x ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have my : y ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mz : z ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mw : w ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have m4 : W.b₄ ∈ M := by
    rw [h4]
    exact add_mem (add_mem (add_mem (add_mem (add_mem (mul_mem mx my) (mul_mem mx mz)) (mul_mem mx mw))
      (mul_mem my mz)) (mul_mem my mw)) (mul_mem mz mw)
  have hr := W.b_relation
  have res : ∀ u : ℂ, u ^ 3 - W.b₄ * u ^ 2 + (W.b₂ * W.b₆ - 4 * W.b₈) / 3 * u -
      (W.b₂ ^ 2 * W.b₈ / 27 + W.b₆ ^ 2 - 4 * W.b₄ * W.b₈ / 3) = 0 → (W.b₄ - 3 * u) ^ 3 = W.Δ := by
    intro u hu
    rw [Δ]
    linear_combination -27 * hu + (9 * W.b₄ - 9 * u) * hr
  have a1 := res (x * y + z * w) (by rw [h2, h4, h6, h8]; ring)
  have a2 := res (x * z + y * w) (by rw [h2, h4, h6, h8]; ring)
  have a3 := res (x * w + y * z) (by rw [h2, h4, h6, h8]; ring)
  have m1 : W.b₄ - 3 * (x * y + z * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx my) (mul_mem mz mw)))
  have m2 : W.b₄ - 3 * (x * z + y * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx mz) (mul_mem my mw)))
  rw [show W.b₄ - 3 * (x * w + y * z) = -((W.b₄ - 3 * (x * y + z * w)) + (W.b₄ - 3 * (x * z + y * w))) by
    linear_combination 3 * h4] at a3
  generalize W.b₄ - 3 * (x * y + z * w) = a at a1 a3 m1
  generalize W.b₄ - 3 * (x * z + y * w) = b at a2 a3 m2
  have hab : b - a ≠ 0 := fun h => hΔ (by
    rw [sub_eq_zero.1 h] at a3
    linear_combination (-8 / 9 : ℂ) * a1 - 1 / 9 * a3)
  have hq : b ^ 2 + b * a + a ^ 2 = 0 := mul_left_cancel₀ hab (by linear_combination a2 - a1)
  have hf : (c - a) * (c - b) * (c + (a + b)) = 0 := by
    linear_combination hc - a1 + (a - c) * hq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h <;> rw [h]
  exacts [m1, m2, neg_mem (add_mem m1 m2)]

theorem twelfth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 12 ⊆ M) {z : ℂ}
    (hz : z ^ 12 = W.Δ) : z ∈ M := by
  have h0 : z ≠ 0 := fun h => hΔ (by rw [← hz, h]; norm_num)
  have h3 : z ^ 3 ∈ M := fourth_root_mem hΔ ha₁ ha₃ ((torsionCoords_mono W (by norm_num)).trans hM)
    (by rw [← hz]; ring)
  have h4 : z ^ 4 ∈ M := cube_root_mem hΔ ((torsionCoords_mono W (by norm_num)).trans hM) (by rw [← hz]; ring)
  rw [show z = z ^ 4 / z ^ 3 by field_simp]
  exact div_mem h4 h3

theorem discField_eq_torsionField (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) [A.IsElliptic] :
    discField d A = torsionField d A := by
  refine le_antisymm (sup_le le_rfl ?_) (torsionField_le_discField d A)
  rw [IntermediateField.adjoin_le_iff]
  intro z (hz : z ^ 12 = _)
  have hF : F ≤ torsionField d A := le_sup_right.trans (hilbertField_le_torsionField d A)
  have hD : (A.baseChange ℂ).Δ = (A.Δ : ℂ) := by rw [baseChange, map_Δ]; rfl
  refine twelfth_root_mem (W := A.baseChange ℂ) ?_ (hF A.a₁.2) (hF A.a₃.2) ?_ (hD ▸ hz)
  · rw [hD]
    exact fun h => A.isUnit_Δ.ne_zero (Subtype.ext h)
  · exact fun w hw => (le_sup_right : _ ≤ torsionField d A) (IntermediateField.subset_adjoin ℚ _ hw)

end GlobalTheory.Mem.DiscRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonIndexIdealInfSupLattices
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BetaEx
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_index_ideal_inf_sup (E : Type) [Field E] [NumberField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E)) (hb : Bdd (M' ⊔ M))
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan (M ⊓ M') = 𝔞 • detSpan M ∧
      detSpan M' = 𝔞 • detSpan (M' ⊔ M) ∧
      Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have hsub : ∀ N : Submodule (𝓞 E) (Fin n → E), N ≤ M' ⊔ M → Bdd N := by
    intro N hN
    obtain ⟨k, hk, h⟩ := hb
    exact ⟨k, hk, fun v hv => h v (hN hv)⟩
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧
        detSpan (M ⊓ M') = 𝔞 • detSpan ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = (M ⊓ M').toAddSubgroup.relIndex
          ((M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h1', h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      have hsM : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ M :=
        Submodule.span_le.2 fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := (M ⊓ M') ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      set S := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hS
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have hmM : Submodule.span (𝓞 E) {m} ≤ M := (Submodule.span_singleton_le_iff_mem _ _).2 hm
      have e : (M ⊓ M') ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have e' : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          S ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hS, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNS : N = M ⊓ S := by
        rw [hN, hS, inf_sup_assoc_of_le _ hsM]
      have hb1 : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (le_sup_of_le_right (sup_le (sup_le inf_le_left hsM) hmM))
      have hb2 : Bdd (S ⊔ Submodule.span (𝓞 E) {m}) :=
        hsub _ (sup_le (sup_le_sup_left hsM _) (le_sup_of_le_right hmM))
      have hc : (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)) =
          S.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) := by
        ext a
        rw [hNS]
        exact ⟨fun h => h.2, fun h => ⟨M.smul_mem a hm, h⟩⟩
      rw [e, e']
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2
          ⟨a, (le_sup_left : M ⊓ M' ≤ N) ⟨M.smul_mem a hm, ham⟩, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb1]
      · rw [h1', hc, Submodule.mul_smul, ← detSpan_cyclic S m hb2]
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hsub M le_sup_right
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 inf_le_left] at this

end GlobalTheory.BetaEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactOpenCongr
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.GLCongrCptOpen

def congrSubgroup {R : Type} [CommRing R] (n : ℕ) (O : Subring R) (I : AddSubgroup R)
    (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I) : Subgroup (GL (Fin n) R) where
  carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  one_mem' := by
    have h : ∀ i j, (1 : Matrix (Fin n) (Fin n) R) i j ∈ O := fun i j => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [O.one_mem, O.zero_mem]
    refine ⟨h, by simpa using h, fun i j => by simp⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3⟩ ⟨h1, h2, h3⟩
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (g1 _ _) (h1 _ _)
    · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact O.sum_mem fun k _ => O.mul_mem (h2 _ _) (g2 _ _)
    · have e : ((g * h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
          (g : Matrix (Fin n) (Fin n) R) * ((h : Matrix (Fin n) (Fin n) R) - 1) +
            ((g : Matrix (Fin n) (Fin n) R) - 1) := by
        rw [Units.val_mul]; noncomm_ring
      rw [← Matrix.sub_apply, e, Matrix.add_apply, Matrix.mul_apply]
      exact I.add_mem (I.sum_mem fun k _ => hI _ (g1 _ _) _ (h3 _ _)) (g3 _ _)
  inv_mem' := by
    rintro g ⟨g1, g2, g3⟩
    refine ⟨g2, by simpa only [inv_inv] using g1, fun i j => ?_⟩
    have e : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - 1 =
        -(((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((g : Matrix (Fin n) (Fin n) R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [← Matrix.sub_apply, e, Matrix.neg_apply, Matrix.mul_apply]
    exact I.neg_mem (I.sum_mem fun k _ => hI _ (g2 _ _) _ (g3 _ _))

theorem isOpen_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ)
    (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) :
    IsOpen (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have c1 : ∀ i j, Continuous fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  change IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    (∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
    ∀ i j, (g : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c1 i j)).inter
    ((isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (c2 i j)).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hIo.preimage ((c1 i j).sub continuous_const)))

theorem isCompact_congrSubgroup {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (n : ℕ) (O : Subring R) (I : AddSubgroup R) (hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I)
    (hO : IsOpen (O : Set R)) (hIo : IsOpen (I : Set R)) (hOc : IsCompact (O : Set R)) :
    IsCompact (congrSubgroup n O I hI : Set (GL (Fin n) R)) := by
  have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
    have := isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin n => hOc))
    have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
        (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R)) :=
      Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact this
  have hP := hM.prod (hM.image MulOpposite.continuous_op)
  have hE := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage hP
  refine hE.of_isClosed_subset
    ((congrSubgroup n O I hI).isClosed_of_isOpen (isOpen_congrSubgroup n O I hI hO hIo)) ?_
  rintro g ⟨g1, g2, -⟩
  exact ⟨g1, _, g2, rfl⟩

theorem exists_compactOpen_congr :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (c : v.adicCompletion F), c ≠ 0 →
    ∃ K : Subgroup (GL (Fin n) (v.adicCompletion F)), IsOpen (K : Set (GL (Fin n) (v.adicCompletion F))) ∧
      IsCompact (K : Set (GL (Fin n) (v.adicCompletion F))) ∧ ∀ g ∈ K, ∀ i j,
        Valued.v ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) ≤
          Valued.v c := by
  intro F _ _ v n c hc
  let O : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring
  have hO : IsOpen (O : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
  have hOc : IsCompact (O : Set (v.adicCompletion F)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  let I : AddSubgroup (v.adicCompletion F) := Valued.v.leAddSubgroup (Valued.v c)
  have hI : ∀ a ∈ O, ∀ x ∈ I, a * x ∈ I := fun a ha x hx => by
    change Valued.v (a * x) ≤ Valued.v c
    rw [map_mul]
    have ha' : Valued.v a ≤ 1 := ha
    have hx' : Valued.v x ≤ Valued.v c := hx
    simpa using mul_le_mul' ha' hx'
  have hIo : IsOpen (I : Set (v.adicCompletion F)) := by
    have e : (I : Set (v.adicCompletion F)) = (fun x => x / c) ⁻¹' (O : Set (v.adicCompletion F)) := by
      ext x
      change Valued.v x ≤ Valued.v c ↔ Valued.v (x / c) ≤ 1
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
    rw [e]
    exact hO.preimage (continuous_id.div_const c)
  exact ⟨congrSubgroup n O I hI, isOpen_congrSubgroup n O I hI hO hIo,
    isCompact_congrSubgroup n O I hI hO hIo hOc, fun g hg => hg.2.2⟩

end GlobalTheory.GLCongrCptOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNhdsOneUnitaryGroupRationalPointEqOne
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbeddingStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact GlobalTheory.Mem.LatGood.lawGood S emb σ lam hF hS hS.lsh_full_lat h
end

