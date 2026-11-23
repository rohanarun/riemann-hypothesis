module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRightA
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma infR_hasFDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) x) x := by
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  have hU : x ∈ Ps1.Uset ε := by
    intro k
    have hk : toMK k⁻¹ = (toMK k)ᴴ := Ps1.toMK_inv_eq k
    have hinv : toMK k⁻¹ * toMK k = 1 := by
      unfold toMK toM
      simp
    have hinj : Function.Injective (toMK k).mulVec := by
      intro v w hvw
      have := congrArg (toMK k⁻¹).mulVec hvw
      simpa [Matrix.mulVec_mulVec, hinv] using this
    have hpd : (toMK k⁻¹ * x * toMK k).PosDef := by
      rw [hk]
      exact hx.conjTranspose_mul_mul_same hinj
    intro i
    unfold lead
    rw [dite_eq_left (by omega)]
    exact ((hpd.submatrix (Fin.castLE_injective _)).det_pos).ne'
  exact (Ps1.hasFDerivAt_psM T μ hU).differentiableAt.hasFDerivAt

lemma infR_conj (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    fderiv ℂ (psM T μ) x (x * A - A * x) = psM T μ x * T.dτ A - T.dτ A * psM T μ x := by
  obtain ⟨γ, -, hγ, hγm⟩ := exists_oneParam ε hA
  have h0 : γ 0 = 1 := by simpa using hγm 0 0
  have hinv : ∀ t, (γ (-t))⁻¹ = γ t := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hγm, neg_add_cancel, h0])

  have heq : ∀ t : ℝ, psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x * NormedSpace.exp ((t : ℂ) • A))
      = T.op (γ (-t)) * psM T μ x * T.op (γ t) := by
    intro t
    have h1 := psM_conj T μ (γ (-t)) x
    rw [hinv, hγ, hγ] at h1
    simpa [Complex.ofReal_neg, neg_smul] using h1

  have hL : HasDerivAt (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
      NormedSpace.exp ((t : ℂ) • A))) (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hc := dga_path A x
    have hψ := infR_hasFDerivAt T μ hx
    exact (hψ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)

  have hR1 := T.hasDeriv A hA γ hγ
  have hR1' : HasDerivAt (fun t => ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (T.dτ A) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hR1
  have hR2 := hR1'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have hR := (hR2.mul (hasDerivAt_const (0 : ℝ) (psM T μ x))).mul hR1
  have hL' : HasDerivAt (fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) *
      psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V))
      (fderiv ℂ (psM T μ) x (x * A - A * x)) 0 := by
    have hfun : (fun t : ℝ => psM T μ (NormedSpace.exp (-((t : ℂ) • A)) * x *
        NormedSpace.exp ((t : ℂ) • A))) = fun t : ℝ => ((T.τ (γ (-t)) : unitary (T.V →L[ℂ] T.V)) :
          T.V →L[ℂ] T.V) * psM T μ x * ((T.τ (γ t) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext t
      exact heq t
    rw [hfun] at hL
    exact hL
  rw [hL'.unique hR]
  simp [h0]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ToMKMulInv
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma op_mul' (T : KType ε Λ) (k k' : KG ε) : T.op (k * k') = T.op k * T.op k' := by
  show ((T.τ (k * k') : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

lemma op_one' (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

lemma toMK_mul_inv' (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by rw [← toMK_mul', mul_inv_cancel, toMK_one']

lemma toMK_inv_mul' (k : KG ε) : toMK k⁻¹ * toMK k = 1 := by rw [← toMK_mul', inv_mul_cancel, toMK_one']

theorem psiM_kexp (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    PsiM T μ (toMK k * NormedSpace.exp X) = T.op k * psM T μ (NormedSpace.exp X) := by
  have h : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X' := ⟨k, X, hX, rfl⟩
  obtain ⟨hk, hXX⟩ := polar_unique hX h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  rw [PsiM, dite_eq_left h, ← hXX, ← hk]

theorem psiM_equiv (T : KType ε Λ) (μ : Fin n → ℤ) (k₁ k₂ : KG ε) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    PsiM T μ (toMK k₁ * g * toMK k₂) = T.op k₁ * PsiM T μ g * T.op k₂ := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  obtain ⟨hX', hexp⟩ := inP_conj k₂⁻¹ hX
  rw [inv_inv] at hX' hexp
  have hc := psM_conj T μ k₂⁻¹ (NormedSpace.exp X)
  rw [inv_inv] at hc
  have hg' : toMK k₁ * (toMK k * NormedSpace.exp X) * toMK k₂ =
      toMK (k₁ * k * k₂) * NormedSpace.exp (toMK k₂⁻¹ * X * toMK k₂) := by
    rw [hexp, toMK_mul', toMK_mul']
    simp only [_root_.mul_assoc]
    rw [← _root_.mul_assoc (toMK k₂) (toMK k₂⁻¹), toMK_mul_inv', _root_.one_mul]
  rw [hg', psiM_kexp T μ _ hX', psiM_kexp T μ k hX, hexp, hc, op_mul', op_mul']
  simp only [_root_.mul_assoc]
  rw [← _root_.mul_assoc (T.op k₂) (T.op k₂⁻¹), ← op_mul', mul_inv_cancel, op_one', _root_.one_mul]

theorem psiM_one (T : KType ε Λ) (μ : Fin n → ℤ) : PsiM T μ 1 = 1 := by
  have h0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by
    first | exact ⟨by simp [inG], by simp⟩ | exact ⟨by first | exact inG_zero ε | exact inG_zero, by simp⟩
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = toMK (1 : KG ε) * NormedSpace.exp (0 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [toMK_one', NormedSpace.exp_zero, one_mul]
  rw [h1, psiM_kexp T μ 1 h0, op_one', one_mul, NormedSpace.exp_zero]
  first | exact psM_one T μ | exact psM_one | simp [psM_one]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

