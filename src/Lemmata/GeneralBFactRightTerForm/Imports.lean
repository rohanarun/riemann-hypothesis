module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right_ter_form

open NumberField

open scoped Pointwise in
theorem goal1 {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * (2 * c) + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : σ ∈ MulAction.stabilizer (Gal(L/ℚ)) P) : σ x = x := by
  have hsq : (σ x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  have hx' : x ^ 2 = 8 * (c : L) + 1 := by rw [hx]; push_cast; ring
  have hint : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (2 * c), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat]
      linear_combination hx' / 4
  let y : NumberField.RingOfIntegers L := ⟨(1 + x) / 2, hint⟩
  have hy : algebraMap (NumberField.RingOfIntegers L) L y = (1 + x) / 2 := rfl
  have h2 : (2 : NumberField.RingOfIntegers L) ∈ P := by
    have h0 := (Ideal.mem_of_liesOver P (Ideal.span {(2 : ℤ)}) (2 : ℤ)).mp
      (Ideal.subset_span rfl)
    simpa using h0
  have hprod : y * (y - 1) = 2 * (c : NumberField.RingOfIntegers L) := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (NumberField.RingOfIntegers L) L (y * (y - 1)) =
      algebraMap (NumberField.RingOfIntegers L) L (2 * (c : NumberField.RingOfIntegers L))
    rw [map_mul, map_sub, map_one, map_mul, map_ofNat, map_intCast, hy]
    linear_combination hx' / 4
  have hmem : y * (y - 1) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2
  have hσP : Ideal.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) P
      = P := hσ
  have key : ∀ a ∈ P, σ • a ∈ P := fun a ha => by
    have h3 := Ideal.mem_map_of_mem
      (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) ha
    rw [hσP] at h3
    exact h3
  have hσy : σ • y = 1 - y := by
    apply NumberField.RingOfIntegers.ext
    change σ (algebraMap (NumberField.RingOfIntegers L) L y) =
      algebraMap (NumberField.RingOfIntegers L) L (1 - y)
    rw [map_sub, map_one, hy, map_div₀, map_add (f := _), map_one, h, map_ofNat]
    ring
  have h1 : (1 : NumberField.RingOfIntegers L) ∈ P := by
    rcases hP.mem_or_mem hmem with h' | h'
    · have h4 := key y h'
      rw [hσy] at h4
      have e : (1 : NumberField.RingOfIntegers L) = (1 - y) + y := by ring
      rw [e]
      exact P.add_mem h4 h'
    · have h4 := key _ h'
      rw [smul_sub, hσy, smul_one] at h4
      have e : (1 : NumberField.RingOfIntegers L) = -((1 - y - 1) + (y - 1)) := by ring
      rw [e]
      exact P.neg_mem (P.add_mem h4 h')
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

end Bl.general_b_fact_right_ter_form
