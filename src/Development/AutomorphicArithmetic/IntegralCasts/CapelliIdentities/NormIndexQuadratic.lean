module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0003

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Pl :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.Kv :
    {F : Type} → [inst : Field F] → [NumberField F] → UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F → Type :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

@[reducible] noncomputable def UpperTheory.Reformulated.B.NormIndexQuadratic.cv :
    {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) → F →+* UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v :=
    fun {F : Type} [Field F] [NumberField F] (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F) ↦ Algebra.algebraMap F (UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v)

open IsDedekindDomain NumberField Module

namespace UpperTheory.Reformulated.B.NormIndexQuadratic

private lemma exists_quad {K : Type} [Field K] [NumberField K] {θ : K} (h : ¬ IsSquare θ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (r : L) (σ : L ≃ₐ[K] L),
      r ^ 2 = algebraMap K L θ ∧ σ r = -r ∧
      (∀ x : L, ∃ a b : K, x = algebraMap K L a + algebraMap K L b * r) ∧ finrank K L = 2 := by
  have : Fact (∀ r : K, r ^ 2 ≠ θ + 0 * r) := ⟨fun r hr => h ⟨r, by rw [← sq, hr]; simp⟩⟩
  have : NumberField (QuadraticAlgebra K θ 0) := NumberField.of_module_finite K _
  refine ⟨QuadraticAlgebra K θ 0, inferInstance, this, inferInstance, QuadraticAlgebra.omega,
    { (starRingAut : RingAut (QuadraticAlgebra K θ 0)) with commutes' := ?_ }, ?_, ?_, ?_,
    QuadraticAlgebra.finrank_eq_two _ _⟩
  · intro r; ext <;> simp
  · ext <;> simp [sq]
  · show star _ = _
    ext <;> simp
  · intro x
    exact ⟨x.re, x.im, by ext <;> simp⟩

end UpperTheory.Reformulated.B.NormIndexQuadratic

theorem UpperTheory.Reformulated.B.NormIndexQuadratic.glob_neg_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {Δ d : F},
      Δ ≠ (0 : F) →
        (∀ (v : UpperTheory.Reformulated.B.NormIndexQuadratic.Pl F),
            ∃ (a : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) (b : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v),
              (-1 : UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) =
                a ^ (2 : ℕ) - (UpperTheory.Reformulated.B.NormIndexQuadratic.cv v : F → UpperTheory.Reformulated.B.NormIndexQuadratic.Kv v) Δ * b ^ (2 : ℕ)) →
          ∀ (σ₀ : F →+* ℝ),
            (∀ (σ : F →+* ℝ), (σ : F → ℝ) d < (0 : ℝ)) →
              ∃ (p₀ : F) (p₁ : F) (q₀ : F) (q₁ : F),
                p₀ ^ (2 : ℕ) + d * p₁ ^ (2 : ℕ) - Δ * (q₀ ^ (2 : ℕ) + d * q₁ ^ (2 : ℕ)) = (-1 : F) ∧ p₀ * p₁ = Δ * q₀ * q₁ := by
  intro F _ _ Δ d hΔ hloc σ₀ hd
  have hsq : ¬ IsSquare d := by
    rintro ⟨t, rfl⟩
    exact absurd (hd σ₀) (not_lt.2 (by rw [map_mul]; exact mul_self_nonneg _))
  obtain ⟨E, _, _, _, r, σ, hr, hσ, hbasis, -⟩ := exists_quad hsq
  -- Apply the quadratic Hasse norm theorem over F(√d). Negativity of d
  -- rules out real places, and the local witnesses extend to each finite place.
  obtain ⟨p, q, hpq⟩ := GlobalTheory.QNorm.hasseNormSt E (algebraMap F E Δ) (-1)
    ((map_ne_zero _).2 hΔ) (by simp) (fun τ => by
      have hneg := hd (τ.comp (algebraMap F E))
      rw [RingHom.comp_apply, ← hr, map_pow] at hneg
      exact (not_lt_of_ge (sq_nonneg _) hneg).elim) (fun w => by
      obtain ⟨v, φ, hφ⟩ := GlobalTheory.LocalQuad.exists_ringHom_adicCompletion F E w
      obtain ⟨a, b, hab⟩ := hloc v
      refine ⟨φ a, φ b, ?_⟩
      change (-1 : v.adicCompletion F) = a ^ 2 - algebraMap F _ Δ * b ^ 2 at hab
      simpa only [map_neg, map_one, map_sub, map_mul, map_pow, hφ] using congrArg φ hab)
  -- Comparing the equation with its conjugate recovers both coordinates over F.
  have hr0 : r ≠ 0 := by
    rintro rfl
    refine hsq ⟨0, (algebraMap F E).injective ?_⟩
    rw [← hr]; simp
  obtain ⟨p₀, p₁, rfl⟩ := hbasis p
  obtain ⟨q₀, q₁, rfl⟩ := hbasis q
  have hconj := congrArg σ hpq
  simp only [map_neg, map_one, map_sub, map_mul, map_add (f := _), map_pow, hσ, σ.commutes] at hconj
  refine ⟨p₀, p₁, q₀, q₁, (algebraMap F E).injective ?_, (algebraMap F E).injective ?_⟩
  · simp only [map_neg, map_one, map_sub, map_mul, map_add (f := _), map_pow, ← hr]
    linear_combination (-1 / 2) * hpq + (-1 / 2) * hconj
  · simp only [map_mul]
    refine mul_right_cancel₀ hr0 ?_
    linear_combination (-1 / 4) * hpq + (1 / 4) * hconj
