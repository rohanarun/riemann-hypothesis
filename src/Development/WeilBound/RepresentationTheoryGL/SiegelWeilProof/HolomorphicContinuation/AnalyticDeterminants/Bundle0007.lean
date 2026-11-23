module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Imports
section
noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB

variable {n : ℕ}

theorem span_top (W : Submodule ℂ (M2 n))
    (hu : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → (fromBlocks 0 b 0 0 : M2 n) ∈ W)
    (hl : ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c → (fromBlocks 0 0 c 0 : M2 n) ∈ W)
    (hbr : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c → (fromBlocks (-(b * c)) 0 0 (c * b) : M2 n) ∈ W)
    (h1 : (1 : M2 n) ∈ W) : W = ⊤ := by

  have dec : ∀ B : Matrix (Fin n) (Fin n) ℂ, ∃ b₁ b₂ : Matrix (Fin n) (Fin n) ℂ, b₁ᴴ = b₁ ∧ b₂ᴴ = b₂ ∧
      B = b₁ + Complex.I • b₂ := by
    intro B
    have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; norm_num
    refine ⟨(1 / 2 : ℂ) • (B + Bᴴ), (-(Complex.I / 2)) • (B - Bᴴ), ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
      congr 1
      simp [Complex.ext_iff]
    · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      rw [show (Bᴴ - B) = -(B - Bᴴ) by abel, smul_neg, ← neg_smul]
      congr 1
      simp [Complex.ext_iff]
      norm_num
    · rw [smul_smul, hI]
      module
  have hU : ∀ B, (fromBlocks 0 B 0 0 : M2 n) ∈ W := by
    intro B
    obtain ⟨b₁, b₂, h₁, h₂, rfl⟩ := dec B
    have : (fromBlocks 0 (b₁ + Complex.I • b₂) 0 0 : M2 n) =
        fromBlocks 0 b₁ 0 0 + Complex.I • fromBlocks 0 b₂ 0 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hu b₁ h₁) (W.smul_mem _ (hu b₂ h₂))
  have hL : ∀ C, (fromBlocks 0 0 C 0 : M2 n) ∈ W := by
    intro C
    obtain ⟨c₁, c₂, h₁, h₂, rfl⟩ := dec C
    have : (fromBlocks 0 0 (c₁ + Complex.I • c₂) 0 : M2 n) =
        fromBlocks 0 0 c₁ 0 + Complex.I • fromBlocks 0 0 c₂ 0 := by
      simp [fromBlocks_smul, fromBlocks_add]
    rw [this]
    exact W.add_mem (hl c₁ h₁) (W.smul_mem _ (hl c₂ h₂))
  have hBr : ∀ B C : Matrix (Fin n) (Fin n) ℂ, (fromBlocks (-(B * C)) 0 0 (C * B) : M2 n) ∈ W := by
    intro B C
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := dec B
    obtain ⟨c₁, c₂, hc₁, hc₂, rfl⟩ := dec C
    have e : (fromBlocks (-((b₁ + Complex.I • b₂) * (c₁ + Complex.I • c₂))) 0 0
        ((c₁ + Complex.I • c₂) * (b₁ + Complex.I • b₂)) : M2 n) =
        fromBlocks (-(b₁ * c₁)) 0 0 (c₁ * b₁) + Complex.I • fromBlocks (-(b₁ * c₂)) 0 0 (c₂ * b₁) +
          Complex.I • fromBlocks (-(b₂ * c₁)) 0 0 (c₁ * b₂) + (-1 : ℂ) • fromBlocks (-(b₂ * c₂)) 0 0 (c₂ * b₂) := by
      simp only [fromBlocks_smul, fromBlocks_add, smul_zero, add_zero]
      congr 1
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
      · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
        match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
    rw [e]
    exact W.add_mem (W.add_mem (W.add_mem (hbr _ _ hb₁ hc₁) (W.smul_mem _ (hbr _ _ hb₁ hc₂)))
      (W.smul_mem _ (hbr _ _ hb₂ hc₁))) (W.smul_mem _ (hbr _ _ hb₂ hc₂))

  let ιA : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun A => fromBlocks A 0 0 0
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  let ιD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M2 n :=
    { toFun := fun D => fromBlocks 0 0 0 D
      map_add' := fun A B => by simp [fromBlocks_add]
      map_smul' := fun c A => by simp [fromBlocks_smul] }
  have sgl : ∀ (a b : Fin n) (c : ℂ), Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
    intro a b c; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have offA : ∀ a b : Fin n, a ≠ b → ιA (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single a b 1) (Matrix.single b b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    have : ιA (Matrix.single a b 1) = -(fromBlocks (-(Matrix.single a b (1 : ℂ))) 0 0 0 : M2 n) := by
      simp [ιA, fromBlocks_neg]
    rw [this]; exact W.neg_mem h
  have offD : ∀ a b : Fin n, a ≠ b → ιD (Matrix.single a b 1) ∈ W := by
    intro a b hab
    have h := hBr (Matrix.single b b 1) (Matrix.single a b 1)
    rw [Matrix.single_mul_single_of_ne (h := Ne.symm hab), Matrix.single_mul_single_same, mul_one] at h
    simpa [ιD] using h
  have dif : ∀ a k : Fin n, ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) ∈ W := by
    intro a k
    have h := hBr (Matrix.single a k 1) (Matrix.single k a 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_one] at h
    have : ιD (Matrix.single k k 1) - ιA (Matrix.single a a 1) =
        (fromBlocks (-(Matrix.single a a (1 : ℂ))) 0 0 (Matrix.single k k 1) : M2 n) := by
      simp [ιA, ιD, sub_eq_add_neg, fromBlocks_add, fromBlocks_neg]
    rw [this]; exact h
  have one_sum : (∑ a : Fin n, Matrix.single a a (1 : ℂ)) = 1 := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases h : i = j
    · subst h; simp [Matrix.single_apply]
    · simp [Matrix.single_apply, Matrix.one_apply, h]
  have hST : ∑ a, ιA (Matrix.single a a 1) + ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum, one_sum]
    have : ιA 1 + ιD 1 = (1 : M2 n) := by simp [ιA, ιD, fromBlocks_add, ← fromBlocks_one]
    rw [this]; exact h1
  have hTS : ∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    rw [← Finset.sum_sub_distrib]
    exact W.sum_mem fun k _ => dif k k
  have hT : ∑ k, ιD (Matrix.single k k 1) ∈ W := by
    have h2 := W.add_mem hST hTS
    have : ∑ k, ιD (Matrix.single k k 1) = (1 / 2 : ℂ) • ((∑ a, ιA (Matrix.single a a 1) +
        ∑ k, ιD (Matrix.single k k 1)) + (∑ k, ιD (Matrix.single k k 1) - ∑ a, ιA (Matrix.single a a 1))) := by
      module
    rw [this]; exact W.smul_mem _ h2
  have hS : ∑ a, ιA (Matrix.single a a 1) ∈ W := by
    have := W.sub_mem hST hT
    simpa using this
  have diagA : ∀ a : Fin n, ιA (Matrix.single a a 1) ∈ W := by
    intro a
    have hn : (Fintype.card (Fin n) : ℂ) ≠ 0 := by
      simp only [Fintype.card_fin, ne_eq, Nat.cast_eq_zero]; exact Fin.pos a |>.ne'
    have hdiff : ∀ b : Fin n, ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) ∈ W := by
      intro b
      have := W.sub_mem (dif b a) (dif a a)
      have e : ιD (Matrix.single a a 1) - ιA (Matrix.single b b 1) - (ιD (Matrix.single a a 1) -
          ιA (Matrix.single a a 1)) = ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1) := by abel
      rwa [e] at this
    have hsum := W.add_mem (W.sum_mem fun b (_ : b ∈ Finset.univ) => hdiff b) hS
    have e : ∑ b, (ιA (Matrix.single a a 1) - ιA (Matrix.single b b 1)) + ∑ a, ιA (Matrix.single a a 1) =
        (Fintype.card (Fin n) : ℂ) • ιA (Matrix.single a a 1) := by
      rw [Finset.sum_sub_distrib, sub_add_cancel, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [e] at hsum
    have := W.smul_mem ((Fintype.card (Fin n) : ℂ)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  have diagD : ∀ k : Fin n, ιD (Matrix.single k k 1) ∈ W := by
    intro k
    have := W.add_mem (dif k k) (diagA k)
    simpa using this
  have allA : ∀ A : Matrix (Fin n) (Fin n) ℂ, ιA A ∈ W := by
    intro A
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single A, map_sum]
    refine W.sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagA i
    · exact offA i j hij
  have allD : ∀ D : Matrix (Fin n) (Fin n) ℂ, ιD D ∈ W := by
    intro D
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.matrix_eq_sum_single D, map_sum]
    refine W.sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine W.sum_mem fun j _ => ?_
    rw [sgl, map_smul]
    refine W.smul_mem _ ?_
    by_cases hij : i = j
    · subst hij; exact diagD i
    · exact offD i j hij
  rw [eq_top_iff]
  intro M _
  rw [← Matrix.fromBlocks_toBlocks M]
  have e : (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ : M2 n) =
      ιA M.toBlocks₁₁ + fromBlocks 0 M.toBlocks₁₂ 0 0 + fromBlocks 0 0 M.toBlocks₂₁ 0 + ιD M.toBlocks₂₂ := by
    simp [ιA, ιD, fromBlocks_add]
  rw [e]
  exact W.add_mem (W.add_mem (W.add_mem (allA _) (hU _)) (hL _)) (allD _)

end PositivityTheory.Rg.Sw.LVs.HolC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCCalc
section
noncomputable section

open scoped ContDiff
open Set Filter Topology

namespace PositivityTheory.Rg.Sw.LVs.TC

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma iter_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) :
    ContDiffOn ℂ ∞ (iteratedFDeriv ℂ i F) Ω := by
  intro y hy
  have hle : (∞ : WithTop ℕ∞) + i ≤ ∞ := by
    exact_mod_cast (le_top : (⊤ : ℕ∞) + i ≤ ⊤)
  exact ((hF.contDiffAt (hΩ.mem_nhds hy)).iteratedFDeriv_right hle).contDiffWithinAt

lemma iter_diffAt {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (i : ℕ) {y : V} (hy : y ∈ Ω) :
    DifferentiableAt ℂ (iteratedFDeriv ℂ i F) y := by
  exact ((iter_smooth hΩ hF i).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hy)

end

theorem iterAffine : IterAffine := by
  intro V W _ _ _ _ F Ω hΩ hF c hc L k
  have hT : Continuous (fun y : V => c + y) := continuous_const.add continuous_id
  have hΩ1 : IsOpen ((fun y : V => c + y) ⁻¹' Ω) := hΩ.preimage hT
  have hΩ2 : IsOpen (L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω)) := hΩ1.preimage L.continuous
  have hG : ContDiffOn ℂ ∞ (fun y : V => F (c + y)) ((fun y : V => c + y) ⁻¹' Ω) :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have hm2 : (0 : W) ∈ L ⁻¹' ((fun y : V => c + y) ⁻¹' Ω) := by simpa using hc
  have hm1 : L 0 ∈ (fun y : V => c + y) ⁻¹' Ω := by simpa using hc
  have hk : (k : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hG hΩ1.uniqueDiffOn
    hΩ2.uniqueDiffOn hm1 hk
  rw [iteratedFDerivWithin_of_isOpen k hΩ2 hm2, iteratedFDerivWithin_of_isOpen k hΩ1 hm1,
    iteratedFDeriv_comp_add_left] at h1
  simp only [map_zero, add_zero] at h1
  exact h1

def predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) : Equiv.Perm (Fin k) where
  toFun i := (σ i.succ).pred (fun h => Fin.succ_ne_zero i (σ.injective (h.trans h0.symm)))
  invFun i := (σ⁻¹ i.succ).pred (fun h => by
    have : σ⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, h0]
    exact Fin.succ_ne_zero i ((σ⁻¹).injective (h.trans this.symm)))
  left_inv i := by simp
  right_inv i := by simp

lemma predPerm_succ {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (i : Fin k) :
    (predPerm σ h0 i).succ = σ i.succ := by
  simp [predPerm]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma symm_fix {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    (ih : ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)), iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v)
    {c : V} (hc : c ∈ Ω) (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) (v : Fin (k + 1) → V) :
    iteratedFDeriv ℂ (k + 1) F c (v ∘ σ) = iteratedFDeriv ℂ (k + 1) F c v := by
  have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k F) c := iter_diffAt hΩ hF k hc
  have ht : Fin.tail (v ∘ σ) = Fin.tail v ∘ predPerm σ h0 := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [predPerm_succ]
  have h0' : (v ∘ σ) 0 = v 0 := by simp [h0]
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, ht, h0',
    ← fderiv_continuousMultilinear_apply_const_apply hd,
    ← fderiv_continuousMultilinear_apply_const_apply hd]
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hΩ.mem_nhds hc] with y hy
  exact ih y hy (Fin.tail v) (predPerm σ h0)

private theorem iteratedFDeriv_add_two_apply {F : V → ℂ} (k : ℕ) (c : V) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c v =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k F)) c (v 0) (v 1) (Fin.tail (Fin.tail v)) := by
  rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
  simp [LinearIsometryEquiv.comp_fderiv, Fin.tail]

lemma symm_swap {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) {k : ℕ}
    {c : V} (hc : c ∈ Ω) (v : Fin (k + 2) → V) :
    iteratedFDeriv ℂ (k + 2) F c (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℂ (k + 2) F c v := by
  have hG : ContDiffAt ℂ ∞ (iteratedFDeriv ℂ k F) c :=
    (iter_smooth hΩ hF k).contDiffAt (hΩ.mem_nhds hc)
  have hmin : minSmoothness ℂ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hs := hG.isSymmSndFDerivAt hmin
  have htt : Fin.tail (Fin.tail (v ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail v) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [Fin.ext_iff]
  rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, htt]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hs (v 1) (v 0)]

end

theorem iterSymm : IterSymm := by
  intro V _ _ F Ω hΩ hF
  suffices h : ∀ k : ℕ, ∀ c ∈ Ω, ∀ (v : Fin k → V) (σ : Equiv.Perm (Fin k)),
      iteratedFDeriv ℂ k F c (v ∘ σ) = iteratedFDeriv ℂ k F c v from
    fun c hc k v σ => h k c hc v σ
  intro k
  induction k with
  | zero =>
    intro c hc v σ
    congr 1
    funext i
    exact i.elim0
  | succ k ih =>
    intro c hc v σ
    have key : ∀ (j : Fin (k + 1)) (u : Fin (k + 1) → V),
        iteratedFDeriv ℂ (k + 1) F c (u ∘ Equiv.swap 0 j) = iteratedFDeriv ℂ (k + 1) F c u := by
      intro j u
      by_cases hj0 : j = 0
      · subst hj0
        simp
      · cases k with
        | zero => exact absurd (Fin.fin_one_eq_zero j) hj0
        | succ m =>
          by_cases hj1 : j = 1
          · subst hj1
            exact symm_swap hΩ hF hc u
          · have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp [Fin.ext_iff]
            have hs : Equiv.swap (0 : Fin (m + 2)) j =
                Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j := by
              rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
            have hfix : ∀ w : Fin (m + 2) → V,
                iteratedFDeriv ℂ (m + 2) F c (w ∘ Equiv.swap 1 j) = iteratedFDeriv ℂ (m + 2) F c w :=
              fun w => symm_fix hΩ hF ih hc (Equiv.swap 1 j)
                (Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)) w
            have hcomp : u ∘ ⇑((Equiv.swap 1 j * Equiv.swap 0 1 * Equiv.swap 1 j :
                Equiv.Perm (Fin (m + 2)))) =
                ((u ∘ Equiv.swap 1 j) ∘ Equiv.swap 0 1) ∘ Equiv.swap 1 j := by
              funext i
              simp [Equiv.Perm.mul_apply]
            rw [hs, hcomp, hfix, symm_swap hΩ hF hc, hfix]
    have h0 : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.Perm.mul_apply]
    have hv : v ∘ σ = (v ∘ Equiv.swap 0 (σ 0)) ∘ ⇑(Equiv.swap 0 (σ 0) * σ) := by
      funext i
      simp [Equiv.Perm.mul_apply]
    rw [hv, symm_fix hΩ hF ih hc _ h0, key]

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

lemma eval_smooth {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω :=
  (ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => V) ℂ w).contDiff.comp_contDiffOn (iter_smooth hΩ hF b)

lemma iter_mixed {F : V → ℂ} {Ω : Set V} (hΩ : IsOpen Ω) (hF : ContDiffOn ℂ ∞ F Ω) (b : ℕ) (w : Fin b → V) :
    ∀ (a : ℕ) {c : V}, c ∈ Ω → ∀ (u : Fin a → V),
      iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) c u = iteratedFDeriv ℂ (a + b) F c (Fin.append u w) := by
  intro a
  induction a with
  | zero =>
    intro c hc u
    rw [iteratedFDeriv_zero_apply, iter_cast (zero_add b) (Fin.append u w),
      Fin.append_left_nil u w rfl]
    congr 1
  | succ a ih =>
    intro c hc u
    have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x w) Ω := eval_smooth hΩ hF b w
    have hd1 := iter_diffAt hΩ hg a hc
    have hd2 := iter_diffAt hΩ hF (a + b) hc
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply hd1]
    have he : (fun y => iteratedFDeriv ℂ a (fun x => iteratedFDeriv ℂ b F x w) y (Fin.tail u))
        =ᶠ[𝓝 c] (fun y => iteratedFDeriv ℂ (a + b) F y (Fin.append (Fin.tail u) w)) := by
      filter_upwards [hΩ.mem_nhds hc] with y hy
      exact ih hy (Fin.tail u)
    rw [he.fderiv_eq, fderiv_continuousMultilinear_apply_const_apply hd2]
    have hs := iteratedFDeriv_succ_apply_left (𝕜 := ℂ) (f := F) (x := c) (n := a + b)
      (Fin.cons (u 0) (Fin.append (Fin.tail u) w))
    rw [Fin.cons_zero, Fin.tail_cons] at hs
    rw [← hs, iter_cast (show a + 1 + b = a + b + 1 by omega) (Fin.append u w)]
    congr 1
    conv_rhs => rw [← Fin.cons_self_tail u, Fin.append_cons]
    funext i
    simp

end

theorem iterNested : IterNested := by
  intro V W1 W2 _ _ _ _ _ _ F Ω hΩ hF c hc L1 L2 a b u w
  have hg : ContDiffOn ℂ ∞ (fun x => iteratedFDeriv ℂ b F x (fun i => L2 (w i))) Ω :=
    eval_smooth hΩ hF b _
  have hU : ∀ᶠ t1 in 𝓝 (0 : W1), c + L1 t1 ∈ Ω := by
    have hcont : Continuous (fun t1 : W1 => c + L1 t1) := continuous_const.add L1.continuous
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hΩ.mem_nhds hc
  have he : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    filter_upwards [hU] with t1 ht1
    rw [iterAffine V W2 F Ω hΩ hF (c + L1 t1) ht1 L2 b]
    rfl
  have he' : (fun t1 => iteratedFDeriv ℂ b (fun t2 => F (c + L1 t1 + L2 t2)) 0 w) =ᶠ[𝓝[univ] 0]
      (fun t1 => iteratedFDeriv ℂ b F (c + L1 t1) (fun i => L2 (w i))) := by
    rw [nhdsWithin_univ]
    exact he
  have hE := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℂ) he' he.eq_of_nhds a
  simp only [iteratedFDerivWithin_univ] at hE
  rw [hE, iterAffine V W1 _ Ω hΩ hg c hc L1 a]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact iter_mixed hΩ hF b _ a hc _

end PositivityTheory.Rg.Sw.LVs.TC
end
end

