module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Mathlib
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFive
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem a_bounds_of_ge_two_n_pow_five : ∀ (k r : ℕ) (a : ℝ), 1 ≤ k → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 ≤ a → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a / 2 ∧ (2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1) + 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ a := by
  intro k r a hk ha
  have hM : ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) = 2 * ((r : ℝ) ^ 2 + r + 1) := by push_cast; ring
  rw [hM]
  generalize hN : ((2 * r + k + 1 : ℕ) : ℝ) = N at ha ⊢
  have hN' : N = 2 * (r : ℝ) + k + 1 := by rw [← hN]; push_cast; ring
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (0 : ℝ) ≤ r := r.cast_nonneg
  have h2 : 2 ≤ N := by linarith
  have hrn : 2 * ((r : ℝ) + 1) ≤ N := by linarith
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by nlinarith
  have hN4 : 4 * N ^ 2 ≤ N ^ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN2) (sq_nonneg N)]
  have h5a : 8 * N ^ 2 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr hN3) (sq_nonneg N)]
  have h5b : 2 * N ^ 4 ≤ N ^ 5 := by nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg (by linarith : (0:ℝ) ≤ N) 4)]
  have hm : 4 * ((r : ℝ) ^ 2 + r + 1) ≤ N ^ 2 := by nlinarith
  have hm2 : 4 * ((r : ℝ) ^ 2 + r + 1) * N ^ 2 ≤ N ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hm (sq_nonneg N)]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonality
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelEqOnOfContinuousOnAeEq
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AeqCont

theorem null_preimage_lmulM {k r : ℕ} {μG : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μG)
    {s : Mat k r} (hs : s ∈ GG k r) {N : Set (Mt k r)} (hN : μG N = 0) :
    μG (lmulM s ⁻¹' N) = 0 := by
  have hm : Measurable (lmulM s : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  refine le_antisymm ?_ bot_le
  calc μG (lmulM s ⁻¹' N) ≤ μG (lmulM s ⁻¹' toMeasurable μG N) :=
        measure_mono (Set.preimage_mono (subset_toMeasurable μG N))
    _ = (μG.map (lmulM s)) (toMeasurable μG N) :=
        (Measure.map_apply hm (measurableSet_toMeasurable μG N)).symm
    _ = μG (toMeasurable μG N) := by rw [hμ.2.2.2 s hs]
    _ = 0 := by rw [measure_toMeasurable, hN]

theorem eqOn_of_ae (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r))
    (f g : Mat k r → B) (hμ : IsHaarOn (GG k r) μG) (hf : ContinuousOn f (GG k r))
    (hg : ContinuousOn g (GG k r))
    (hfg : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x))) :
    ∀ x ∈ GG k r, f x = g x := by
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ _ hH
  intro x0 hx0
  by_contra hne
  obtain ⟨U, hUo, hU⟩ := (continuousOn_iff'.1 (hf.sub hg)) ({0}ᶜ : Set B) isOpen_compl_singleton
  have hmemU : ∀ y ∈ GG k r, y ∈ U → f y ≠ g y := by
    intro y hy hyU h
    have : y ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r := by rw [hU]; exact ⟨hyU, hy⟩
    exact this.1 (by simp [h])
  have hx0U : x0 ∈ U := by
    have : x0 ∈ (f - g) ⁻¹' ({0}ᶜ : Set B) ∩ GG k r :=
      ⟨by simpa [sub_eq_zero] using hne, hx0⟩
    rw [hU] at this; exact this.1
  set N : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ U ∧ (Matrix.of x : Mat k r) ∈ GG k r} with hNdef
  have hN : μG N = 0 := by
    have h0 : μG {x | ¬ f (Matrix.of x) = g (Matrix.of x)} = 0 := ae_iff.1 hfg
    exact measure_mono_null (fun x hx => hmemU _ hx.2 hx.1) h0
  let O : GG k r → Set (Mt k r) := fun s => {x | (s.1 * Matrix.of x : Mat k r) ∈ U}
  have hO : ∀ s, IsOpen (O s) := fun s =>
    hUo.preimage (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable O hO
  have hcov : {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} ⊆ ⋃ s ∈ T, lmulM s.1 ⁻¹' N := by
    intro x hx
    have hdet : IsUnit (Matrix.of x : Mat k r).det := (hgrp.2.2 _ hx).1
    have hxinv : (Matrix.of x : Mat k r)⁻¹ ∈ GG k r := (hgrp.2.2 _ hx).2
    let s : GG k r := ⟨x0 * (Matrix.of x : Mat k r)⁻¹, hgrp.2.1 _ hx0 _ hxinv⟩
    have hxO : x ∈ ⋃ i, O i := Set.mem_iUnion.2 ⟨s, by
      show x0 * (Matrix.of x : Mat k r)⁻¹ * Matrix.of x ∈ U
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]; exact hx0U⟩
    rw [← hT] at hxO
    obtain ⟨t, htT, hxt⟩ := Set.mem_iUnion₂.1 hxO
    exact Set.mem_iUnion₂.2 ⟨t, htT, hxt, hgrp.2.1 _ t.2 _ hx⟩
  have hG0 : μG {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} = 0 :=
    measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun s _ => null_preimage_lmulM hμ s.2 hN)
  have huniv : μG Set.univ = 0 := by
    have : (Set.univ : Set (Mt k r)) =
        {x | (Matrix.of x : Mat k r) ∈ GG k r} ∪ {x | (Matrix.of x : Mat k r) ∉ GG k r} := by
      ext x; by_cases h : (Matrix.of x : Mat k r) ∈ GG k r <;> simp [h]
    rw [this]; exact measure_union_null hG0 hμ.2.2.1
  exact hμ.2.1 (Measure.measure_univ_eq_zero.1 huniv)

end GlobalTheory.SgInf.AeqCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormProperties
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.OpNormU

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ eucl v := Real.sqrt_nonneg _

theorem eucl_mulVec_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    eucl (x *ᵥ v) ≤ opn x * eucl v := by
  rw [eucl_eq, eucl_eq, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem continuous_opn {N : ℕ} : Continuous fun x : Matrix (Fin N) (Fin N) ℂ => opn x :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)).toAlgEquiv.toLinearMap).norm

theorem opn_conjTranspose {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn xᴴ = opn x := by
  unfold opn
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

theorem norm_entry_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ‖x i j‖ ≤ opn x := by
  have h := eucl_mulVec_le x (Pi.single j 1)
  have h1 : eucl (Pi.single j (1 : ℂ) : Fin N → ℂ) = 1 := by
    rw [eucl_eq]; simpa using (EuclideanSpace.norm_single (𝕜 := ℂ) j (1 : ℂ))
  have h2 : ‖x i j‖ ≤ eucl (x *ᵥ Pi.single j 1) := by
    rw [eucl_eq]
    have := PiLp.norm_apply_le (p := 2) (WithLp.toLp 2 (x *ᵥ Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin N)) i
    simpa [Matrix.mulVec_single] using this
  rw [h1, mul_one] at h
  exact h2.trans h

theorem herm_le {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v : Fin N → ℂ) :
    ‖herm H u v‖ ≤ opn H * eucl u * eucl v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) (WithLp.toLp 2 (H *ᵥ u))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, ← eucl_eq, ← eucl_eq, mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (eucl_mulVec_le H u) (eucl_nonneg _))

theorem eucl_mulVec_le_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    eucl (x *ᵥ w) ≤ Real.sqrt (Formalism.REAL.hs x) * eucl w := by
  unfold eucl
  have hnn : 0 ≤ Formalism.REAL.hs x := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← Real.sqrt_mul hnn]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_eq_norm_sq, Formalism.REAL.hs, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(x *ᵥ w) i‖ ≤ ∑ j, ‖x i j‖ * ‖w j‖ := by
    rw [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  calc ‖(x *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖x i j‖ * ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖x i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := Finset.sum_mul _ _ _

theorem opn_le_sqrt_hs {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) : opn x ≤ Real.sqrt (Formalism.REAL.hs x) := by
  unfold opn
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → ℂ, v = WithLp.toLp 2 w := ⟨v.ofLp, rfl⟩
  rw [Matrix.toEuclideanCLM_toLp, ← eucl_eq, ← eucl_eq]
  exact eucl_mulVec_le_hs x w

theorem sqrt_hs_le {N : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) :
    Real.sqrt (Formalism.REAL.hs x) ≤ (N : ℝ) * opn x := by
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (opn_nonneg _), ?_⟩
  calc Formalism.REAL.hs x ≤ ∑ _i : Fin N, ∑ _j : Fin N, opn x ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_entry_le x i j) 2
    _ = ((N : ℝ) * opn x) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable {k r : ℕ}

theorem opn_Hpk (k r : ℕ) : opn (Hpk k r) = 1 := by
  have h : opn ((Hpk k r)ᴴ * Hpk k r) = opn (Hpk k r) * opn (Hpk k r) := by
    unfold opn
    rw [← Matrix.star_eq_conjTranspose, map_mul, map_star, CStarRing.norm_star_mul_self]
  rw [GBasic.Hpk_herm, GBasic.Hpk_sq, opn_one] at h
  rcases mul_self_eq_one_iff.mp h.symm with h1 | h1
  · exact h1
  · have := opn_nonneg (Hpk k r); linarith

theorem left_inv {g : Mat k r} (hg : g ∈ GG k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', GBasic.Hpk_sq]

theorem inv_eq {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (left_inv hg)

theorem inv_mul {g : Mat k r} (hg : g ∈ GG k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact left_inv hg

theorem mul_inv {g : Mat k r} (hg : g ∈ GG k r) : g * g⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (left_inv hg))

theorem opn_inv_le {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ ≤ opn g := by
  rw [inv_eq hg]
  calc opn (Hpk k r * gᴴ * Hpk k r) ≤ opn (Hpk k r) * opn gᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem le_opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g ≤ opn g⁻¹ := by
  have e : g = Hpk k r * (g⁻¹)ᴴ * Hpk k r := by
    rw [inv_eq hg]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, GBasic.Hpk_herm, ← Matrix.mul_assoc,
      GBasic.Hpk_sq, Matrix.one_mul]
    rw [Matrix.mul_assoc, GBasic.Hpk_sq, Matrix.mul_one]
  calc opn g = opn (Hpk k r * (g⁻¹)ᴴ * Hpk k r) := congrArg opn e
    _ ≤ opn (Hpk k r) * opn (g⁻¹)ᴴ * opn (Hpk k r) :=
        (opn_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _))
    _ = opn g⁻¹ := by rw [opn_Hpk, opn_conjTranspose]; ring

theorem opn_inv {g : Mat k r} (hg : g ∈ GG k r) : opn g⁻¹ = opn g :=
  le_antisymm (opn_inv_le hg) (le_opn_inv hg)

theorem one_le_opn {g : Mat k r} (hg : g ∈ GG k r) : 1 ≤ opn g := by
  have h : (1 : ℝ) ≤ opn g * opn g := by
    have := opn_mul_le g g⁻¹
    rwa [mul_inv hg, opn_one, opn_inv hg] at this
  by_contra h'
  have h0 := opn_nonneg g
  nlinarith

theorem opn_pos {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := lt_of_lt_of_le one_pos (one_le_opn hg)

theorem div_le_opn_mul {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) :
    opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y) := by
  constructor
  · rw [div_le_iff₀ (opn_pos hy)]
    calc opn x = opn (x * y * y⁻¹) := by rw [Matrix.mul_assoc, mul_inv hy, Matrix.mul_one]
      _ ≤ opn (x * y) * opn y⁻¹ := opn_mul_le _ _
      _ = opn (x * y) * opn y := by rw [opn_inv hy]
  · rw [div_le_iff₀ (opn_pos hx)]
    calc opn y = opn (x⁻¹ * (x * y)) := by rw [← Matrix.mul_assoc, inv_mul hx, Matrix.one_mul]
      _ ≤ opn x⁻¹ * opn (x * y) := opn_mul_le _ _
      _ = opn (x * y) * opn x := by rw [opn_inv hx, mul_comm]

end GlobalTheory.SgInf.OpNormU

namespace GlobalTheory.SgInf

theorem opn_facts : ∀ (k r : ℕ) , (∀ g ∈ GG k r, opn g⁻¹ = opn g ∧ 1 ≤ opn g) ∧
    (∀ x y : Mat k r, opn (x * y) ≤ opn x * opn y) ∧ Continuous (fun x : Mat k r => opn x) ∧
    (∀ (x : Mat k r) i j, ‖x i j‖ ≤ opn x) ∧
    (∀ (x : Mat k r) (v : Fin (2 * r + k + 1) → ℂ), eucl (x *ᵥ v) ≤ opn x * eucl v) ∧
    (∀ u v : Fin (2 * r + k + 1) → ℂ, ‖herm (Hpk k r) u v‖ ≤ eucl u * eucl v) ∧
    (∀ x ∈ GG k r, ∀ y ∈ GG k r, opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y)) ∧
    (∀ x : Mat k r, opn x ≤ Real.sqrt (Formalism.REAL.hs x) ∧
      Real.sqrt (Formalism.REAL.hs x) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * opn x) := by
  intro k r
  refine ⟨fun g hg => ⟨OpNormU.opn_inv hg, OpNormU.one_le_opn hg⟩, fun x y => opn_mul_le x y,
    OpNormU.continuous_opn, OpNormU.norm_entry_le, OpNormU.eucl_mulVec_le, fun u v => ?_,
    fun x hx y hy => OpNormU.div_le_opn_mul hx hy,
    fun x => ⟨OpNormU.opn_le_sqrt_hs x, OpNormU.sqrt_hs_le x⟩⟩
  simpa [OpNormU.opn_Hpk] using OpNormU.herm_le (Hpk k r) u v

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSchurTranslatedMatrixCoefficient
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem schur_translated_coef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ σ w a μG d hStd u u₁ v t ht
  obtain ⟨_, ⟨⟨h1, hmul⟩, hiso, _⟩, _, _, ⟨_, _, hnull, _⟩, ⟨_, hS⟩, _⟩ := hStd
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hH
  have htu : IsUnit t.det := (hgrp.2.2 t ht).1
  have hti : t⁻¹ ∈ GG k r := (hgrp.2.2 t ht).2
  have htt : t * t⁻¹ = 1 := Matrix.mul_nonsing_inv t htu
  let L : H →ₗᵢ[ℂ] H := ⟨(σ t : H →ₗ[ℂ] H), fun x => hiso t ht x⟩
  have hinv : σ t (σ t⁻¹ v) = v := by
    have := hmul t ht t⁻¹ hti
    rw [htt, h1] at this
    have h' := congrArg (fun f : H →L[ℂ] H => f v) this
    simpa using h'.symm
  have hadj : ∀ x : H, ⟪v, σ t x⟫_ℂ = ⟪σ t⁻¹ v, x⟫_ℂ := by
    intro x
    have := L.inner_map_map (σ t⁻¹ v) x
    conv_lhs => rw [← hinv]
    exact this
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) =
      coef σ u v (Matrix.of y) * star (coef σ u₁ (σ t⁻¹ v) (Matrix.of y)) := by
    have hmem : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hnull
    filter_upwards [hmem] with y hy
    congr 2
    simp only [coef]
    rw [hmul t ht _ hy, ContinuousLinearMap.comp_apply, hadj]
  rw [integral_congr_ae hae]
  exact (hS u v u₁ (σ t⁻¹ v)).2

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isClosedSub_of_closedSubgroup {k r : ℕ} {S : Set (Mat k r)} (hG : S ⊆ GG k r)
    (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) : IsClosedSub k r S :=
  ⟨hG, h.closed, h.one_mem, h.mul_mem, h.inv_mem⟩

theorem closedSub_groups : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧
      IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  intro k r z hz hT
  have cG : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (GG k r) := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have cN : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  have cW : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have sN : Nset k r ⊆ GG k r := fun g hg => hg.1
  have sW : UWset k r z ⊆ GG k r := fun g hg => hg.1
  have sS : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, n, hn, rfl⟩
    exact cG.mul_mem _ (sW hh) _ (sN hn)
  exact ⟨isClosedSub_of_closedSubgroup subset_rfl cG, isClosedSub_of_closedSubgroup sN cN,
    isClosedSub_of_closedSubgroup sW cW,
    isClosedSub_of_closedSubgroup sS (GlobalTheory.BesselPeriodCompare.closedS hz),
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT⟩

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIff
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.RegInv

theorem hpk_isUnit_det (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, GBasic.Hpk_sq, Matrix.det_one]
  exact ⟨⟨_, _, h, h⟩, rfl⟩

private lemma unit_lemma' {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : IsUnit γ.det ∧ γ⁻¹ ∈ GG k r :=
  (unitary_group_holds _ (Hpk k r) (hpk_isUnit_det k r)).2.2 γ h

theorem inv_mem {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : γ⁻¹ ∈ GG k r := (unit_lemma' h).2

private lemma herm_mulVec_eq_of_mem_GG {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ *ᵥ x) (γ *ᵥ y) = herm (Hpk k r) x y := by
  have hγ : γᴴ * Hpk k r * γ = Hpk k r := h
  simp only [herm]
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hγ]

private lemma herm_Hpk_swap (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

theorem herm_inv {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ⁻¹ *ᵥ v) w = star (herm (Hpk k r) (γ *ᵥ w) v) := by
  have hv : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_lemma' h).1, Matrix.one_mulVec]
  rw [← herm_mulVec_eq_of_mem_GG h (γ⁻¹ *ᵥ v) w, hv]
  exact herm_Hpk_swap k r _ _

theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ := by
  ext a b
  simp only [_root_.Formalism.QuantumDeterminants.Zhat, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact herm_inv h _ _

theorem dmin_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r)
    (l : Fin (r + 2)) : Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  simp only [Dmin]
  rw [zhat_inv z z' h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

theorem gf_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Gf k r z' z γ⁻¹ = Gf k r z z' γ := by
  simp only [Gf, dmin_inv z z' h, Complex.star_def, Complex.normSq_conj]
  ring

theorem zhat_inv_and_reg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  refine ⟨zhat_inv z z' h, ?_⟩
  simp only [Greg, Set.mem_ofPred_eq, dmin_inv z z' h, gf_inv z z' h, star_ne_zero, h, inv_mem h,
    true_and]

end GlobalTheory.SgInf.RegInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeOfSpan
section
open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.GenericOrder

theorem mem_locP' {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem frame_mem {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hL : IsLift Λ F) (hF : ∀ b, frame F b ∈ Λ)
    (b : Fin (r + 1)) : frame F b ∈ XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} := by
  have hb := hF b
  induction b using Fin.lastCases with
  | last =>
    refine Submodule.mem_sup_right (Submodule.subset_span ?_)
    simp [frame, Formalism.MainNotions.S.FlagG.fvec, hL.2]
  | cast i =>
    refine Submodule.mem_sup_left ⟨hb, ?_⟩
    have : frame F i.castSucc = F.fl.e i := by simp [frame, Formalism.MainNotions.S.FlagG.fvec]
    rw [this]
    exact Submodule.subset_span (s := Set.range F.fl.e) ⟨i, rfl⟩

end GlobalTheory.GenericOrder
end

