module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectors
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.IsoFrame

private theorem half_smul_sub_mul_mul_mul_self {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℂ) (hAA : A * A = A + A)
    (hSAS : S * A * S = S) :
    ((1 / 2 : ℂ) • (A - A * S * A)) * ((1 / 2 : ℂ) • (A - A * S * A)) =
      (1 / 2 : ℂ) • (A - A * S * A) := by
  have h5 : A * S * A * S * A = A * S * A := by
    rw [show A * S * A * S * A = A * (S * A * S) * A by noncomm_ring, hSAS]
  have key : (A - A * S * A) * (A - A * S * A) = (A - A * S * A) + (A - A * S * A) := by
    calc (A - A * S * A) * (A - A * S * A)
        = A * A - (A * A) * S * A - A * S * (A * A) + A * S * (A * A) * S * A := by noncomm_ring
      _ = (A + A) - (A + A) * S * A - A * S * (A + A) + A * S * (A + A) * S * A := by rw [hAA]
      _ = (A + A) - (A * S * A + A * S * A) - (A * S * A + A * S * A)
            + (A * S * A * S * A + A * S * A * S * A) := by noncomm_ring
      _ = (A - A * S * A) + (A - A * S * A) := by rw [h5]; abel
  rw [Matrix.smul_mul, Matrix.mul_smul, key, ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem exists_eigenframe {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J) (p : ℕ)
    (hp : Matrix.trace (1 + J) = 2 * (p : ℂ)) {a : ℕ} (j : Fin a → ℕ)
    (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (h1 : ∀ i, (T i)ᴴ * T i = 1)
    (h2 : ∀ i k, i ≠ k → (T i)ᴴ * T k = 0) (h3 : ∀ i k, (T i)ᴴ * J * T k = 0) :
    ∃ P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ, (∀ i, (T i)ᴴ * P = 0) ∧ Pᴴ * P = 1 ∧ J * P = P ∧
      P * Pᴴ = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by

  have hA : ∀ i k, (T i)ᴴ * (1 + J) * T k = (T i)ᴴ * T k := by
    intro i k
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h3, add_zero]
  have hTS : ∀ i, (T i)ᴴ * (1 + J) * (∑ k, T k * (T k)ᴴ) = (T i)ᴴ := by
    intro i
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, hA, h1, Matrix.one_mul]
    · intro k _ hk
      rw [← Matrix.mul_assoc, hA, h2 i k (Ne.symm hk), Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hSAS : (∑ k, T k * (T k)ᴴ) * (1 + J) * (∑ k, T k * (T k)ᴴ) = ∑ k, T k * (T k)ᴴ := by
    rw [Matrix.mul_assoc, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T k)ᴴ, hTS]
  have hAA : (1 + J) * (1 + J) = (1 + J) + (1 + J) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJJ]; abel
  have hJA : J * (1 + J) = 1 + J := by
    rw [Matrix.mul_add, Matrix.mul_one, hJJ, add_comm]

  have hRR := half_smul_sub_mul_mul_mul_self (1 + J) (∑ k, T k * (T k)ᴴ) hAA hSAS
  have hAh : (1 + J)ᴴ = 1 + J := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hJh]
  have hSh : (∑ k, T k * (T k)ᴴ)ᴴ = ∑ k, T k * (T k)ᴴ := by
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hRh : ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))ᴴ
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hAh, hSh, ← Matrix.mul_assoc]
    congr 1
    simp

  have htrS : Matrix.trace ((1 + J) * (∑ k, T k * (T k)ᴴ)) = ∑ k, (j k : ℂ) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hA, h1, Matrix.trace_one,
      Fintype.card_fin]
  have htrR : Matrix.trace ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_sub, hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAA,
      Matrix.add_mul, Matrix.trace_add, htrS]
    simp only [smul_eq_mul]; ring
  obtain ⟨r, P, hPP, hPR⟩ := GlobalTheory.hermitian_idempotent_eq_isometry_mul_conjTranspose n _ hRh hRR
  have hr : (r : ℂ) = (p : ℂ) - ∑ i, (j i : ℂ) := by
    rw [← htrR, ← hPR, Matrix.trace_mul_comm, hPP, Matrix.trace_one, Fintype.card_fin]
  have hr' : r = p - ∑ i, j i := by
    have hc : ((r + ∑ i, j i : ℕ) : ℂ) = (p : ℂ) := by push_cast; rw [hr]; ring
    have h' : r + ∑ i, j i = p := by exact_mod_cast hc
    omega
  subst hr'
  have hRP : (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) * P = P := by
    rw [← hPR, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have hTR : ∀ i, (T i)ᴴ * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J))) = 0 := by
    intro i
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hTS, sub_self, smul_zero]
  have hJR : J * ((1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)))
      = (1 / 2 : ℂ) • ((1 + J) - (1 + J) * (∑ i, T i * (T i)ᴴ) * (1 + J)) := by
    rw [Matrix.mul_smul, Matrix.mul_sub]
    simp only [← Matrix.mul_assoc, hJA]
  refine ⟨P, fun i => ?_, hPP, ?_, hPR⟩
  · rw [← hRP, ← Matrix.mul_assoc, hTR i, Matrix.zero_mul]
  · rw [← hRP, ← Matrix.mul_assoc, hJR]

theorem complete_isotropic_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  intro n ε p q hp hq a j T h1 h2 h3

  have hJdef : Formalism.REAL.Jm ε = Matrix.diagonal (fun b => if ε b = true then (1 : ℂ) else -1) := by
    unfold Formalism.REAL.Jm
    try rfl
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [hJdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext b; split_ifs <;> norm_num
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [hJdef, Matrix.diagonal_conjTranspose]
    congr 1; funext b; simp only [Pi.star_apply]; split_ifs <;> simp
  have htp : Matrix.trace (1 + Formalism.REAL.Jm ε) = 2 * (p : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = true then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hp]; ring
  have htq : Matrix.trace (1 + -Formalism.REAL.Jm ε) = 2 * (q : ℂ) := by
    rw [hJdef, ← Matrix.diagonal_one, Matrix.diagonal_neg, Matrix.diagonal_add, Matrix.trace_diagonal]
    refine (Finset.sum_congr rfl (g := fun b => if ε b = false then (2 : ℂ) else 0) fun b _ => ?_).trans ?_
    · try dsimp only
      cases ε b <;> norm_num
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hq]; ring

  obtain ⟨P, hP0, hPP, hJP, hPR⟩ := exists_eigenframe _ hJJ hJh p htp j T h1 h2 h3
  have h3' : ∀ i k, (T i)ᴴ * (-Formalism.REAL.Jm ε) * T k = 0 := by
    intro i k; rw [Matrix.mul_neg, Matrix.neg_mul, h3, neg_zero]
  obtain ⟨Q, hQ0, hQQ, hJQ, hQR⟩ := exists_eigenframe (-Formalism.REAL.Jm ε)
    (by rw [neg_mul_neg, hJJ]) (by rw [Matrix.conjTranspose_neg, hJh]) q htq j T h1 h2 h3'
  refine ⟨P, Q, hP0, hQ0, hPP, hQQ, hJP, ?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_iff_eq_neg] at hJQ; exact hJQ
  · have hsum : (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε))
        = (∑ i, T i * (T i)ᴴ) + Formalism.REAL.Jm ε * (∑ i, T i * (T i)ᴴ) * Formalism.REAL.Jm ε := by
      rw [Finset.sum_add_distrib, Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum, hPR, hQR]
    generalize (∑ i, T i * (T i)ᴴ) = S
    generalize Formalism.REAL.Jm ε = J

    have hX : ((1 + J) - (1 + J) * S * (1 + J)) + ((1 + -J) - (1 + -J) * S * (1 + -J))
        = (1 - S - J * S * J) + (1 - S - J * S * J) := by noncomm_ring
    rw [add_assoc (S + J * S * J), ← smul_add, hX, ← two_smul ℂ, smul_smul,
      show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul]
    abel

end GlobalTheory.IsoFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem isFdegG_tensor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ)
    (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v)) :
    IsFdegG (muInf B.I) B.σs (∏ v, d v) := by
  have hd : 0 < ∏ v, d v := Finset.prod_pos fun v _ => (hF v).1
  obtain ⟨hi, hs, hdense⟩ := B.tens_spec
  refine isFdegG_of_total B.I.Ginf (muInf B.I) B.Hs B.σs (∏ v, d v) (Set.range B.tens)
    (GlobalTheory.HilbTensorUnitary.isURep_rows B hU) hd hdense ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨x', rfl⟩ _ ⟨y', rfl⟩

  have hfun : (fun g : B.I.Ginf => ⟪B.tens y, B.σs g (B.tens x)⟫_ℂ * star ⟪B.tens y', B.σs g (B.tens x')⟫_ℂ) =
      fun g => ∏ v, (coefOn (B.σ v) (x v) (y v) (g v) * star (coefOn (B.σ v) (x' v) (y' v) (g v))) := by
    funext g
    rw [hs, hs, hi, hi, star_prod, ← Finset.prod_mul_distrib]
    rfl
  have hloc := fun v => (hF v).2 (x v) (y v) (x' v) (y' v)
  rw [hfun]
  unfold muInf
  refine ⟨Integrable.fintype_prod_dep fun v => (hloc v).1, ?_⟩
  refine (integral_fintype_prod_eq_prod (μ := fun v => muG (B.I.ε v))
    (fun v g => coefOn (B.σ v) (x v) (y v) g * star (coefOn (B.σ v) (x' v) (y' v) g))).trans ?_
  rw [Finset.prod_congr rfl fun v _ => (hloc v).2, hi, hi, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  push_cast
  rfl

theorem tensorRep : TensorRep := by
  intro B d hB
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => (hB v).2.1.2.2.1
  have hF : ∀ v, IsFdeg (muG (B.I.ε v)) (B.σ v) (d v) := fun v => (hB v).2.2.2
  have hG := isFdegG_tensor B d hU hF
  obtain ⟨hi, hs, -⟩ := B.tens_spec
  refine ⟨GlobalTheory.HilbTensorUnitary.isURep_rows B hU, (isIrr_and_dense_of_isFdegG _ _ _ _ _ hG).1, hG, ?_, ?_⟩
  ·
    have h1 : ⟪B.tens B.w, B.tens B.w⟫_ℂ = 1 := by
      rw [hi]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [inner_self_eq_norm_sq_to_K, (hB v).2.2.1.1]
      simp
    have h2 : ‖B.tens B.w‖ ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
      simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  · intro g
    rw [hs, hi]
    rfl

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjPowOfMulEqOne
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.NearElement

theorem conj_pow_of_mul_eq_one {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : (Y * G * X) ^ m = Y * G ^ m * X := by
  induction m with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    calc Y * G ^ m * X * (Y * G * X) = Y * G ^ m * (X * Y) * G * X := by simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc, mul_one, one_mul]

theorem trace_conj_pow {A n : Type} [CommRing A] [Fintype n] [DecidableEq n]
    (X Y G : Matrix n n A) (h : X * Y = 1) (m : ℕ) : ((Y * G * X) ^ m).trace = (G ^ m).trace := by
  rw [conj_pow_of_mul_eq_one X Y G h, Matrix.trace_mul_cycle, h, one_mul]

theorem trace_pow_cong (E : Type) [Field E] [NumberField E] (n g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E))
    (G : Matrix (Fin n) (Fin n) E) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hrad : (Ideal.span {(g : 𝓞 E)}).IsRadical) (hg : 1 ≤ g) (hG : ∀ y ∈ Λ, G *ᵥ y ∈ Λ)
    (hU : ∀ y ∈ Λ, ∃ z ∈ Λ, ((G - 1) ^ n) *ᵥ y = (g : E) • z) (j : ℕ) :
    ∃ t : 𝓞 E, (G ^ j).trace - n = (g : E) * (t : E) := by
  have hpow : ∀ (M : Matrix (Fin n) (Fin n) E), (∀ y ∈ Λ, M *ᵥ y ∈ Λ) → ∀ m : ℕ, ∀ y ∈ Λ, (M ^ m) *ᵥ y ∈ Λ := by
    intro M hM m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ, ← mulVec_mulVec]; exact ih _ (hM y hy)
  set S := ∑ i ∈ Finset.range j, G ^ i with hS
  have hSΛ : ∀ y ∈ Λ, S *ᵥ y ∈ Λ := by
    intro y hy
    rw [hS, Matrix.sum_mulVec]
    exact Λ.sum_mem fun i _ => hpow G hG i y hy
  have e : G ^ j - 1 = (G - 1) * S := (mul_geom_sum G j).symm
  have hc : Commute (G - 1) S := by
    show (G - 1) * S = S * (G - 1)
    rw [hS, mul_geom_sum, geom_sum_mul]
  obtain ⟨t, ht⟩ := GlobalTheory.trace_mem_of_nilpotent_mod_radical E n n g Λ (G ^ j - 1) hfg hsp hrad hg
    (fun y hy => by rw [sub_mulVec, one_mulVec]; exact Λ.sub_mem (hpow G hG j y hy) hy)
    (fun y hy => by rw [e, hc.mul_pow, ← mulVec_mulVec]; exact hU _ (hpow S hSΛ n y hy))
  exact ⟨t, by rw [← ht]; simp⟩

theorem embedding_eq_or_conj (I : AutInst) (ι : I.E →+* ℂ) :
    ∃ v, ι = I.φ v ∨ ι = ComplexEmbedding.conjugate (I.φ v) := by
  refine ⟨(InfinitePlace.mk ι).comap (algebraMap I.F I.E), ?_⟩
  rcases GlobalTheory.Count.Test.embedding_cases I (InfinitePlace.mk ι) with h | h <;>
    rcases InfinitePlace.embedding_mk_eq ι with h' | h'
  · exact Or.inl (h'.symm.trans h)
  · right
    rw [← h, h']; simp
  · exact Or.inr (h'.symm.trans h)
  · left
    exact star_injective (h'.symm.trans h)

theorem radius_bounds (c : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 10 ^ 5) (n f : ℝ) (hn : 1 ≤ n) (hf : 1 ≤ f) :
    n * (c / (n ^ 8 * f ^ 2)) ≤ 1 / 4 ∧ 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) < 1 / 4 ∧
      ∀ q : ℝ, 0 ≤ q → q ^ 2 ≤ n → 3 * Real.sqrt (n * (c / (n ^ 8 * f ^ 2))) * q * n * f ≤ 1 / 100 := by
  have key : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) ≤ c := by
    have e : n * (c / (n ^ 8 * f ^ 2)) * (n ^ 3 * f ^ 2) = c / n ^ 4 := by field_simp
    rw [e]
    exact div_le_self hc.le (one_le_pow₀ hn)
  have h0 : 0 ≤ n * (c / (n ^ 8 * f ^ 2)) := by positivity
  generalize n * (c / (n ^ 8 * f ^ 2)) = a at key h0
  have h1 : 1 ≤ n ^ 3 * f ^ 2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (one_le_pow₀ hf)
  have ha : a ≤ c := le_trans (le_mul_of_one_le_right h0 h1) key
  refine ⟨by linarith, ?_, fun q hq hqn => ?_⟩
  · have : Real.sqrt a < 1 / 12 := by
      rw [Real.sqrt_lt' (by norm_num)]; linarith
    linarith
  · refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
    have e : (3 * Real.sqrt a * q * n * f) ^ 2 = 9 * (a * (q ^ 2 * n ^ 2 * f ^ 2)) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt h0]; ring
    have h2 : a * (q ^ 2 * n ^ 2 * f ^ 2) ≤ a * (n ^ 3 * f ^ 2) := by
      rw [pow_succ' n 2]; gcongr
    rw [e]; linarith

theorem near_unipotent : NearUnip := by
  intro B d c hc hc' hn hg hrad ep δ hep hδ
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨r1, r2, r3⟩ := radius_bounds c hc hc' B.I.n B.I.f (by exact_mod_cast hn) (by exact_mod_cast hf)
  rw [← hep] at r1 r2 r3
  rw [← hδ] at r2 r3
  refine ⟨?_, r2, fun q hq => r3 q (Nat.cast_nonneg q) (by exact_mod_cast hq)⟩
  rintro x a ⟨ha, hne, hd⟩
  have hep0 : 0 ≤ ep := by rw [hep]; positivity
  have he : B.e (x⁻¹ * a * x).2 ≠ 0 := right_ne_zero_of_mul hne
  have hK := B.e_adm.2.2.2.2.1 _ he
  have hU := B.e_adm.2.2.2.2.2.2 _ he
  obtain ⟨γ, -, hinf, hfin⟩ := id ha
  have hg1 : 1 ≤ B.g₀ := by omega
  obtain ⟨hG, hGU⟩ := GlobalTheory.PointLattice.lamX_unipMod B.I x a γ B.g₀ hg1 hfin hK hU
  obtain ⟨-, hfg, hsp, -⟩ := GlobalTheory.PointLattice.lamX_selfDual B.I x
  generalize (γ : Matrix (Fin B.I.n) (Fin B.I.n) B.I.E) = G at hinf hfin hG hGU
  have hP : ∀ v, B.I.P v * (B.I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (B.I.P_unit v))
  have htr : ∀ v j, (uMat ((x⁻¹ * a * x).1 v) ^ j).trace = B.I.φ v (G ^ j).trace := by
    intro v j
    have e : uMat ((x⁻¹ * a * x).1 v) = uMat (x.1 v)⁻¹ * uMat (a.1 v) * uMat (x.1 v) := rfl
    rw [e, trace_conj_pow _ _ _ (Units.mul_inv _), hinf, trace_conj_pow _ _ _ (hP v), AddMonoidHom.map_trace]
    congr 1
    exact (map_pow (B.I.φ v).mapMatrix G j).symm
  have harch : ∀ v, (∀ j : ℕ, j ≤ B.I.n → ‖(uMat ((x⁻¹ * a * x).1 v) ^ j).trace - B.I.n‖ ≤ 3 * B.I.n) ∧
      ((uMat ((x⁻¹ * a * x).1 v)).trace = B.I.n →
        Real.sqrt (hs (uMat ((x⁻¹ * a * x).1 v) - 1)) ≤ 3 * Real.sqrt (B.I.n * ep)) := by
    intro v
    obtain ⟨k, X, hk, hX, e⟩ := (polar B.I.n (B.I.ε v)).1 (uMat ((x⁻¹ * a * x).1 v)) ((x⁻¹ * a * x).1 v).2
    have h1 := hd v
    rw [e, (GlobalTheory.Count.Cartan.cartan_distances _ _).1 k X hk hX] at h1
    rw [e]
    exact GlobalTheory.NearUnitaryExp.near_arch _ k X ep hk.1 ((pChar _ _ X).1.1 hX).1 hep0 h1 r1
  have htn : ∀ j, j ≤ B.I.n → (G ^ j).trace = B.I.n := by
    intro j hj
    obtain ⟨t, ht⟩ := trace_pow_cong B.I.E B.I.n B.g₀ _ G hfg hsp hrad hg1 hG hGU j
    have e : (((B.g₀ : 𝓞 B.I.E) * t : 𝓞 B.I.E) : B.I.E) = (G ^ j).trace - B.I.n := by rw [ht]; simp
    have h0 := GlobalTheory.ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le B.I.E B.g₀ (3 * B.I.n)
      ((B.g₀ : 𝓞 B.I.E) * t) (dvd_mul_right _ _) (fun ι => ?_) ?_
    · rw [h0] at e
      exact sub_eq_zero.1 (by simpa using e.symm)
    · obtain ⟨v, hv⟩ := embedding_eq_or_conj B.I ι
      have h2 := (harch v).1 j hj
      rw [htr, ← map_natCast (B.I.φ v), ← map_sub, ← e] at h2
      rcases hv with rfl | rfl
      · exact h2
      · rwa [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    · have : 3 * B.I.n < B.g₀ := by omega
      exact_mod_cast this
  have hnil := (GlobalTheory.unipotent_of_trace_pow_eq_size B.I.E B.I.n G fun j _ hj => htn j hj).2
  have hmap : ∀ {A : Type} [CommRing A] (ι : B.I.E →+* A), (G.map ι - 1) ^ B.I.n = 0 := by
    intro A _ ι
    have := congrArg ι.mapMatrix hnil
    rw [map_pow, map_sub, map_one, map_zero] at this
    exact this
  refine ⟨by rw [hfin]; exact hmap _, fun v => ?_, ha, hK, fun v => ?_⟩
  · have e : uMat (a.1 v) - 1 = (B.I.P v)⁻¹ * (G.map (B.I.φ v) - 1) * B.I.P v := by
      rw [hinf, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 (hP v)]
    rw [e, conj_pow_of_mul_eq_one _ _ _ (hP v), hmap, mul_zero, zero_mul]
  · rw [hδ]
    apply (harch v).2
    have := htr v 1
    rw [htn 1 hn, pow_one, map_natCast] at this
    exact this

end GlobalTheory.NearElement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolProdLeTsumSlices
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem covol_prod_le_tsum_slices : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (A : Set (G₁ × G₂)) (ι : Type) [Countable ι] (x : ι → G₂) (Γc Ac : ι → Set G₁), MeasurableSet (K : Set G₂) → (∀ c, ∀ g ∈ Γc c, ∃ γ ∈ Γ, γ.1 = g ∧ (x c)⁻¹ * γ.2 * x c ∈ K) → (∀ y ∈ A, ∃ c, ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * y.2 = x c * k ∧ γ.1 * y.1 ∈ Ac c) → μ₂ K ≠ ⊤ → covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤ μ₂ K * ∑' c, covol (Γc c) μ₁ (Ac c) := by
  intro G₁ G₂ _ _ _ _ _ μ₁ μ₂ _ _ _ Γ K A ι _ x Γc Ac hK hΓ hA hfin
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  obtain ⟨ε', hε', hsum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (ε : ENNReal))
    (by exact_mod_cast hε.ne') ι
  have key : ∀ c, ∃ D : Set G₁, MeasurableSet D ∧
      μ₂ K * μ₁ D ≤ μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c ∧
      (D = Set.univ ∨ ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D) := by
    intro c
    by_cases h0 : μ₂ K = 0
    · exact ⟨Set.univ, MeasurableSet.univ, by simp [h0], Or.inl rfl⟩
    · have hc : μ₂ K * covol (Γc c) μ₁ (Ac c) ≠ ⊤ :=
        ne_top_of_le_ne_top hb.ne (by
          gcongr
          exact le_tsum (fun i => covol (Γc i) μ₁ (Ac i)) c)
      have hlt : μ₂ K * covol (Γc c) μ₁ (Ac c) < μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c :=
        ENNReal.lt_add_right hc (by exact_mod_cast (hε' c).ne')
      have h2 : μ₂ K * covol (Γc c) μ₁ (Ac c) = ⨅ (D : Set G₁) (_ : MeasurableSet D)
          (_ : ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D), μ₂ K * μ₁ D := by
        simp only [covol, ENNReal.mul_iInf_of_ne h0 hfin]
      rw [h2] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨D, hD, hcov, hlt⟩ := hlt
      rw [← h2] at hlt
      exact ⟨D, hD, hlt.le, Or.inr hcov⟩
  choose D hDm hDle hDcov using key
  have hKm : ∀ c, MeasurableSet ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)) := fun c =>
    measurable_const_mul _ hK
  have h1 : covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤
      (μ₁.prod μ₂) (⋃ c, D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂))) := by
    refine iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion fun c => (hDm c).prod (hKm c))
      (iInf_le_of_le ?_ le_rfl))
    intro y hy
    obtain ⟨c, γ, hγ, k, hk, h2, h1⟩ := hA y hy
    rcases hDcov c with hu | hcov
    · refine ⟨γ, hγ, Set.mem_iUnion.2 ⟨c, by simp [hu], ?_⟩⟩
      simpa [h2] using hk
    · obtain ⟨g, hg, hgD⟩ := hcov _ h1
      obtain ⟨δ, hδ, rfl, hδK⟩ := hΓ c g hg
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨c, by simpa [mul_assoc] using hgD, ?_⟩⟩
      have := K.mul_mem hδK hk
      simpa [mul_assoc, h2] using this
  refine h1.trans ((measure_iUnion_le _).trans ?_)
  calc ∑' c, (μ₁.prod μ₂) (D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)))
      ≤ ∑' c, (μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
        exact hDle c
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        exact add_le_add le_rfl hsum.le

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasWPrescribed
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
end

