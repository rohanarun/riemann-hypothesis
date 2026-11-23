module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw IwaPf

variable {n : ℕ}

theorem detU1 : CayleyBlocksInvertible := by
  intro n y
  have hg : InG (mR y) := y.2
  refine ⟨det_ne (mR y) hg Complex.I (by norm_num [Complex.ext_iff]), ?_⟩
  show (-(Complex.I • toBlocks₂₁ (mR y)) + toBlocks₂₂ (mR y)).det ≠ 0
  rw [← neg_smul]
  exact det_ne (mR y) hg (-Complex.I) (by norm_num [Complex.ext_iff])

theorem rows_blocks (g : M2 n) (h : InG g) : g.toBlocks₂₁ * g.toBlocks₂₂ᴴ = g.toBlocks₂₂ * g.toBlocks₂₁ᴴ := by
  have hr := inG_rows g h
  rw [← fromBlocks_toBlocks g] at hr
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply] at hr
  have h22 := congrArg Matrix.toBlocks₂₂ hr
  simp at h22
  exact (neg_add_eq_zero.mp h22).symm

def kmat (U1 U2 : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (U1 + U2)) ((Complex.I / 2) • (U1 - U2)) (-((Complex.I / 2) • (U1 - U2)))
    ((1 / 2 : ℂ) • (U1 + U2))

theorem kmat_unit (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) :
    (kmat U1 U2)ᴴ * kmat U1 U2 = 1 := by
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  rw [← fromBlocks_one]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

theorem kmat_inG (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (h1 : U1ᴴ * U1 = 1) (h2 : U2ᴴ * U2 = 1) : InG (kmat U1 U2) := by
  unfold InG JJ
  simp only [kmat, fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_smul,
    conjTranspose_add, conjTranspose_sub, conjTranspose_neg, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    add_zero, zero_add, neg_neg, h1, h2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  congr 1
  all_goals (match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf)

private theorem mul_inv_mul_proj_of_ker_iff (g : M2 n) (h : InG g) : u1 g * (u1 g)ᴴ = u2 g * (u2 g)ᴴ := by
  have hr := rows_blocks g h
  simp only [u1, u2, conjTranspose_add, conjTranspose_neg, conjTranspose_smul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hr]
  simp only [Complex.star_def, Complex.conj_I]
  module

private theorem proj_mul_mul_proj_of_ker_iff (U1 U2 : Matrix (Fin n) (Fin n) ℂ) (Y : M2 n) :
    toBlocks₂₁ (Y * (kmat U1 U2)ᴴ) =
      (1 / 2 : ℂ) • (((-Complex.I) • u1 Y) * U1ᴴ + (Complex.I • u2 Y) * U2ᴴ) := by
  rw [← fromBlocks_toBlocks Y]
  simp only [u1, u2, kmat, fromBlocks_conjTranspose, fromBlocks_multiply, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, conjTranspose_smul, conjTranspose_add, conjTranspose_sub, conjTranspose_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_neg, smul_sub]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring_nf

private theorem inv_mul_unitary_of_mul_conjTranspose_eq (a b : Matrix (Fin n) (Fin n) ℂ) (hab : a * aᴴ = b * bᴴ) (h2d : b.det ≠ 0) :
    (b⁻¹ * a) * (b⁻¹ * a)ᴴ = 1 ∧ a * (b⁻¹ * a)ᴴ = b := by
  have hbu : IsUnit b.det := isUnit_iff_ne_zero.mpr h2d
  have hbH : IsUnit bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr h2d)
  have haV : a * (b⁻¹ * a)ᴴ = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, ← Matrix.mul_assoc, hab, Matrix.mul_assoc,
      mul_nonsing_inv _ hbH, Matrix.mul_one]
  refine ⟨?_, haV⟩
  rw [Matrix.mul_assoc, haV, nonsing_inv_mul b hbu]

theorem iwa : Iwa := by
  intro n y
  have hg : InG (mR y) := y.2
  obtain ⟨_, h2d⟩ := detU1 n y
  obtain ⟨hVV, haV⟩ := inv_mul_unitary_of_mul_conjTranspose_eq (u1 (mR y)) (u2 (mR y)) (mul_inv_mul_proj_of_ker_iff (mR y) hg) h2d
  have hVu := mul_eq_one_comm.mp hVV
  have h1' : (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 = 1 := by simp
  have hK := kmat_unit _ 1 hVu h1'
  have hK' := mul_eq_one_comm.mp hK
  let kGL : GL (Fin n ⊕ Fin n) ℂ := ⟨kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1, _, hK', hK⟩
  have hkG : kGL ∈ GR n := kmat_inG _ 1 hVu h1'
  let k : GR n := ⟨kGL, hkG⟩
  have hkK : k ∈ KR n := by
    show InK (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)
    exact ⟨kmat_inG _ 1 hVu h1', hK⟩
  refine ⟨y * k⁻¹, k, ?_, hkK, (inv_mul_cancel_right y k).symm⟩
  show toBlocks₂₁ (mR (y * k⁻¹)) = 0
  have hm : mR (y * k⁻¹) = mR y * (kmat ((u2 (mR y))⁻¹ * u1 (mR y)) 1)ᴴ := rfl
  rw [hm, proj_mul_mul_proj_of_ker_iff, Matrix.smul_mul, Matrix.smul_mul, haV, conjTranspose_one, Matrix.mul_one]
  simp

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZeroB
section
noncomputable section

open Matrix Filter Topology Set Polynomial

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def lowM (n : ℕ) (s : ℝ) : M2 n := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 ((s : ℂ) • 1) 1

lemma lowM_mul (s s' : ℝ) : lowM n s * lowM n s' = lowM n (s + s') := by
  simp only [lowM, fromBlocks_multiply]
  simp [add_smul]

lemma lowM_zero : lowM n 0 = 1 := by
  unfold lowM; simp [fromBlocks_one]

def lowU (n : ℕ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨lowM n s, lowM n (-s), by rw [lowM_mul, add_neg_cancel, lowM_zero], by rw [lowM_mul, neg_add_cancel, lowM_zero]⟩

def lowG (n : ℕ) (s : ℝ) : GR n := ⟨lowU n s, InG_lower s⟩

lemma lowG_cont : Continuous (lowG n) := by
  unfold lowG
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  have hc : Continuous (fun s : ℝ => lowM n s) := by
    unfold lowM
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      (Complex.continuous_ofReal.smul continuous_const) continuous_const
  exact ⟨hc, hc.comp continuous_neg⟩

lemma lowG_zero : lowG n 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact lowM_zero

lemma mR_mul (a b : GR n) : mR (a * b) = mR a * mR b := rfl

lemma lower_left_block_lowering_mul (y : GR n) (s : ℝ) :
    (mR (y * lowG n s)).toBlocks₂₁ = (mR y).toBlocks₂₁ + (s : ℂ) • (mR y).toBlocks₂₂ := by
  rw [mR_mul]
  show (mR y * lowM n s).toBlocks₂₁ = _
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  unfold lowM
  rw [fromBlocks_multiply]
  simp

lemma dense_cell (y : GR n) : y ∈ closure {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, C = (mR y).toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (mR y).toBlocks₂₂ := ⟨_, rfl⟩
  have hG : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hgg : mR y * mR y⁻¹ = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    rfl
  have hJJ : JJ n * JJ n = -1 := by
    rw [JJ, fromBlocks_multiply]
    simp [← fromBlocks_one, fromBlocks_neg]
  have key : mR y * JJ n * (mR y)ᴴ = JJ n := by
    have h1 : (mR y)ᴴ * JJ n = JJ n * mR y⁻¹ := by
      calc (mR y)ᴴ * JJ n = (mR y)ᴴ * JJ n * (mR y * mR y⁻¹) := by rw [hgg, Matrix.mul_one]
        _ = ((mR y)ᴴ * JJ n * mR y) * mR y⁻¹ := by simp only [Matrix.mul_assoc]
        _ = JJ n * mR y⁻¹ := by rw [hG]
    calc mR y * JJ n * (mR y)ᴴ = mR y * JJ n * (mR y)ᴴ * (JJ n * JJ n) * (-1) := by
          rw [hJJ]; simp
      _ = mR y * JJ n * ((mR y)ᴴ * JJ n) * JJ n * (-1) := by simp only [Matrix.mul_assoc]
      _ = mR y * (JJ n * JJ n) * mR y⁻¹ * JJ n * (-1) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = JJ n := by
          rw [hJJ]
          simp [hgg]
  have hherm : C * Dᴴ = D * Cᴴ := by
    have hb := congrArg Matrix.toBlocks₂₂ key
    rw [← fromBlocks_toBlocks (mR y), JJ, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply] at hb
    simp at hb
    rw [← hC, ← hD] at hb
    exact (neg_add_eq_zero.mp hb).symm
  have hpos : ((C * Cᴴ + D * Dᴴ).det) ≠ 0 := by
    have hu : IsUnit (mR y) := ⟨(y : GL (Fin n ⊕ Fin n) ℂ), rfl⟩
    open ComplexOrder in
    have hpd : ((mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr).PosDef :=
      (Matrix.PosDef.mul_conjTranspose_self _
        (Matrix.vecMul_injective_iff_isUnit.mpr hu)).submatrix Sum.inr_injective
    have he : (mR y * (mR y)ᴴ).submatrix Sum.inr Sum.inr = C * Cᴴ + D * Dᴴ := by
      change Matrix.toBlocks₂₂ (mR y * (mR y)ᴴ) = _
      rw [hC, hD]
      conv_lhs => rw [← fromBlocks_toBlocks (mR y), fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
    rw [← he]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit |>.ne_zero
  have hprod : (C + Complex.I • D) * (C + Complex.I • D)ᴴ = C * Cᴴ + D * Dᴴ := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [← hherm, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
    abel
  have hI : (C + Complex.I • D).det ≠ 0 := by
    intro h
    apply hpos
    rw [← hprod, Matrix.det_mul, h, zero_mul]
  let P : Polynomial ℂ :=
    Matrix.det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C)
  have hev : ∀ r : ℂ, P.eval r = (C + r • D).det := by
    intro r
    show Polynomial.evalRingHom r (Matrix.det _) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP : P ≠ 0 := fun h => hI (by rw [← hev, h, Polynomial.eval_zero])
  have hfin : {s : ℝ | P.eval (s : ℂ) = 0}.Finite := by
    apply Set.Finite.subset ((P.roots.toFinset.finite_toSet).preimage
      Complex.ofReal_injective.injOn)
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    simp [Polynomial.mem_roots hP, hs]
  have hT : Tendsto (fun s : ℝ => y * lowG n s) (𝓝[≠] (0 : ℝ)) (𝓝 y) := by
    have h0 : Tendsto (fun s : ℝ => y * lowG n s) (𝓝 0) (𝓝 (y * lowG n 0)) :=
      (continuous_const.mul lowG_cont).tendsto 0
    rw [lowG_zero, mul_one] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hT
  have hopen : ({s : ℝ | P.eval (s : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hfin.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with s hs hs0
  show ((mR (y * lowG n s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_lowering_mul, ← hC, ← hD, ← hev]
  intro h
  exact hs ⟨h, hs0⟩

end PositivityTheory.Rg.Sw.AbsSt.SZ
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalSectionContinuousNeZero
section
noncomputable section

open Matrix Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def Dm (X : Fin n → ℝ) (s : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)) 0 0 (diagonal fun j => ((Real.exp (-(s * X j)) : ℝ) : ℂ))

theorem Dm_mul (X : Fin n → ℝ) (s t : ℝ) : Dm X s * Dm X t = Dm X (s + t) := by
  simp only [Dm, fromBlocks_multiply, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 2
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  · funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring

theorem Dm_zero (X : Fin n → ℝ) : Dm X 0 = 1 := by
  simp [Dm, fromBlocks_one]

def dGL (X : Fin n → ℝ) (s : ℝ) : GL (Fin n ⊕ Fin n) ℂ :=
  ⟨Dm X s, Dm X (-s), by rw [Dm_mul, add_neg_cancel, Dm_zero], by rw [Dm_mul, neg_add_cancel, Dm_zero]⟩

theorem diag_conjT_mul (f g : Fin n → ℝ) :
    (diagonal fun j => ((f j : ℝ) : ℂ))ᴴ * diagonal (fun j => ((g j : ℝ) : ℂ)) = diagonal fun j => ((f j * g j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext j
  simp [Complex.conj_ofReal]

theorem inG_blocks (A B : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * B = 1) : InG (fromBlocks A 0 0 B) := by
  have h' : Bᴴ * A = 1 := by
    have := congrArg Matrix.conjTranspose h
    simpa [Matrix.conjTranspose_mul] using this
  unfold InG JJ
  rw [fromBlocks_conjTranspose]
  simp only [conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [h, h']

theorem inG_Dm (X : Fin n → ℝ) (s : ℝ) : InG (Dm X s) := by
  apply inG_blocks
  rw [diag_conjT_mul, ← diagonal_one]
  congr 1
  funext j
  rw [← Real.exp_add]
  simp

def aD (X : Fin n → ℝ) (s : ℝ) : GR n := ⟨dGL X s, inG_Dm X s⟩

theorem isDil_aD (X : Fin n → ℝ) (s : ℝ) : IsDil X s (aD X s) := rfl

theorem isDil_unique (X : Fin n → ℝ) (s : ℝ) (a a' : GR n) (h : IsDil X s a) (h' : IsDil X s a') : a = a' := by
  apply Subtype.ext
  apply Units.ext
  exact h.trans h'.symm

theorem form_inv (g : M2 n) (hg : InG g) (V : Fin n ⊕ Fin n → ℂ) :
    star (g *ᵥ V) ⬝ᵥ (JJ n *ᵥ (g *ᵥ V)) = star V ⬝ᵥ (JJ n *ᵥ V) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold InG at hg
  rw [hg]

theorem JJ_mulVec (y z : Fin n → ℂ) : JJ n *ᵥ Sum.elim y z = Sum.elim z (-y) := by
  funext i
  rcases i with i | i <;> simp [JJ, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

theorem dot_elim (a b c d : Fin n → ℂ) : Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_elim (a b : Fin n → ℂ) : star (Sum.elim a b) = Sum.elim (star a) (star b) := by
  funext i
  rcases i with i | i <;> rfl

theorem mulVec_elim (g : M2 n) (y z : Fin n → ℂ) :
    g *ᵥ Sum.elim y z = Sum.elim (g.toBlocks₁₁ *ᵥ y + g.toBlocks₁₂ *ᵥ z) (g.toBlocks₂₁ *ᵥ y + g.toBlocks₂₂ *ᵥ z) := by
  funext i
  rcases i with i | i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁,
    toBlocks₂₂]

theorem u_det_ne (g : M2 n) (hg : InG g) (w : ℂ) (hw : w = Complex.I ∨ w = -Complex.I) :
    (w • g.toBlocks₂₁ + g.toBlocks₂₂).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have key := form_inv g hg (Sum.elim (w • x) x)
  rw [mulVec_elim] at key
  have hl : g.toBlocks₂₁ *ᵥ (w • x) + g.toBlocks₂₂ *ᵥ x = 0 := by
    rw [Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]
    exact hx
  rw [hl, JJ_mulVec, JJ_mulVec, star_elim, star_elim, dot_elim, dot_elim] at key
  have hs : star (w • x) = star w • star x := by
    funext j; simp [mul_comm]
  rw [hs] at key
  simp only [dotProduct_zero, zero_add, Pi.star_apply, star_zero, zero_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at key
  have hxx : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.mp h)
  rcases hw with rfl | rfl
  · apply hxx
    have h2 : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (-(2 * Complex.I)) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h
  · apply hxx
    have h2 : star (-Complex.I) = Complex.I := by simp [Complex.star_def]
    rw [h2] at key
    have : (2 * Complex.I) * (star x ⬝ᵥ x) = 0 := by linear_combination -key
    rcases mul_eq_zero.mp this with h | h
    · simp at h
    · exact h

theorem automorphy_first_det_ne_zero (h : GR n) : (u1 (mR h)).det ≠ 0 := u_det_ne _ h.2 _ (Or.inl rfl)

theorem automorphy_second_det_ne_zero (h : GR n) : (u2 (mR h)).det ≠ 0 := by
  have : u2 (mR h) = (-Complex.I) • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ := by
    simp [u2, neg_smul]
  rw [this]
  exact u_det_ne _ h.2 _ (Or.inr rfl)

theorem det_mR_ne (h : GR n) : (mR h).det ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit h.1)
  exact this.ne_zero

theorem continuous_mR : Continuous (mR (n := n)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_group_lower_left_block : Continuous fun h : GR n => (mR h).toBlocks₂₁ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inl j : Fin n ⊕ Fin n))

theorem continuous_group_lower_right_block : Continuous fun h : GR n => (mR h).toBlocks₂₂ :=
  continuous_mR.matrix_submatrix (fun i : Fin n => (Sum.inr i : Fin n ⊕ Fin n)) (fun j : Fin n => (Sum.inr j : Fin n ⊕ Fin n))

theorem spherical_section_continuous_ne_zero (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) ∧ ∀ k : GR n, F0 p q e k ≠ 0 := by
  have c1 : Continuous fun h : GR n => (mR h).det := continuous_mR.matrix_det
  have c2 : Continuous fun h : GR n => (u1 (mR h)).det := by
    have : Continuous fun h : GR n => Complex.I • (mR h).toBlocks₂₁ + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).add continuous_group_lower_right_block
    unfold u1
    exact this.matrix_det
  have c3 : Continuous fun h : GR n => (u2 (mR h)).det := by
    have : Continuous fun h : GR n => -(Complex.I • (mR h).toBlocks₂₁) + (mR h).toBlocks₂₂ :=
      (continuous_group_lower_left_block.const_smul Complex.I).neg.add continuous_group_lower_right_block
    unfold u2
    exact this.matrix_det
  refine ⟨?_, fun k => ?_⟩
  · unfold F0 f0
    exact (c1.zpow₀ e fun h => Or.inl (det_mR_ne h)).mul
      ((c2.zpow₀ _ fun h => Or.inl (automorphy_first_det_ne_zero h)).mul (c3.zpow₀ _ fun h => Or.inl (automorphy_second_det_ne_zero h)))
  · unfold F0 f0
    exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne k))
      (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero k)) (zpow_ne_zero _ (automorphy_second_det_ne_zero k)))

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection
section
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def aZ {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  fromBlocks (diagonal fun j => Complex.exp (z * X j)) 0 0 (diagonal fun j => Complex.exp (-(z * X j)))

def twistedScalarSection {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) : ℂ := M.det ^ e * f0 p q M

def TSBFacts : Prop :=
  CayleyBlocksInvertible → ∀ (n p q : ℕ) (e : ℤ),
    CompactSpace (KR n) ∧ Continuous (mR : GR n → M2 n) ∧ Continuous (F0 p q e : GR n → ℂ) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ), ∃ a : GR n, IsDil X t a) ∧
    (∀ (X : Fin n → ℝ) (t : ℝ) (a : GR n), IsDil X t a → mR a = aZ X t) ∧
    ∀ (X : Fin n → ℝ) (C : Set (GR n)), IsCompact C → ∃ U : Set ℂ, IsOpen U ∧ (∀ t : ℝ, (t : ℂ) ∈ U) ∧
      ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U) ∧
      ∀ y ∈ C, DifferentiableOn ℂ (fun z => twistedScalarSection p q e (mR y * aZ X z)) U

end PositivityTheory.Rg.Sw.AbsSt
end
end

