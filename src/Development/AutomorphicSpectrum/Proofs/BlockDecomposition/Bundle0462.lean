module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0455
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.LocFinType
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBound
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {r : ℕ}

theorem cone_anti {c c' : ℝ} (hcc : c' ≤ c) {t : Fin r → ℝ} (ht : t ∈ cone r c) : t ∈ cone r c' :=
  ⟨ht.1, fun i j h => (mul_le_mul_of_nonneg_right hcc (ht.1 j).le).trans (ht.2.1 i j h),
    fun i h => hcc.trans (ht.2.2 i h)⟩

theorem cone_step {c : ℝ} (hc0 : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (d : ℕ) :
    ∀ a b : Fin r, b.val = a.val + d → c ^ d * t b ≤ t a := by
  induction d with
  | zero =>
    intro a b h
    have e : b = a := Fin.ext (by simpa using h)
    subst e
    simp
  | succ d ih =>
    intro a b h
    have hm : a.val + d < r := by
      have := b.2
      omega
    have h1 := ih a ⟨a.val + d, hm⟩ rfl
    have h2 := ht.2.1 ⟨a.val + d, hm⟩ b (by simp only []; omega)
    calc c ^ (d + 1) * t b = c ^ d * (c * t b) := by ring
      _ ≤ c ^ d * t ⟨a.val + d, hm⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ t a := h1

theorem cone_pow_mul_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    {a b : Fin r} (hab : a ≤ b) : c ^ r * t b ≤ t a := by
  have hab' : a.val ≤ b.val := hab
  have h1 := cone_step hc0 ht (b.val - a.val) a b (by omega)
  have hle : c ^ r ≤ c ^ (b.val - a.val) :=
    pow_le_pow_of_le_one hc0.le hc1 (by have := b.2; omega)
  exact (mul_le_mul_of_nonneg_right hle (ht.1 b).le).trans h1

theorem cone_pow_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) {t : Fin r → ℝ} (ht : t ∈ cone r c)
    (i : Fin r) : c ^ r ≤ t i := by
  have hi := i.2
  have hl : r - 1 < r := by omega
  have h1 := cone_step hc0 ht (r - 1 - i.val) i ⟨r - 1, hl⟩ (by simp only []; omega)
  have h2 := ht.2.2 ⟨r - 1, hl⟩ (by simp only []; omega)
  calc c ^ r ≤ c ^ (r - 1 - i.val + 1) := pow_le_pow_of_le_one hc0.le hc1 (by omega)
    _ = c ^ (r - 1 - i.val) * c := pow_succ _ _
    _ ≤ c ^ (r - 1 - i.val) * t ⟨r - 1, hl⟩ := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ t i := h1

theorem weights_across_levels {e A T wa wb : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (heA : e ≤ A) (heT : e ≤ T)
    (h : (e * A ≤ wa ∧ wb * e ^ 2 ≤ T) ∨ (e ^ 2 ≤ wa * T ∧ e * A * wb ≤ 1) ∨ (e * A ≤ wa ∧ e * A * wb ≤ 1)) :
    wb * (e ^ 4 * A) ≤ T * wa := by
  have hA0 : 0 < A := he0.trans_le heA
  have hT0 : 0 < T := he0.trans_le heT
  have hee : e * e ^ 2 ≤ e ^ 2 := by
    have : 0 ≤ e ^ 2 := by positivity
    nlinarith
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h3 : e * (e * A) ≤ wa := by
      have : 0 ≤ e * A := by positivity
      nlinarith
    calc wb * (e ^ 4 * A) = (wb * e ^ 2) * (e * (e * A)) := by ring
      _ ≤ T * wa := mul_le_mul h2 h3 (by positivity) hT0.le
  · calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * e ^ 2 := mul_le_mul h2 hee (by positivity) zero_le_one
      _ = e ^ 2 := one_mul _
      _ ≤ wa * T := h1
      _ = T * wa := mul_comm _ _
  · have h3 : e * e ^ 2 ≤ T * wa := by
      calc e * e ^ 2 = e * (e * e) := by ring
        _ ≤ T * (e * A) := mul_le_mul heT (mul_le_mul_of_nonneg_left heA he0.le) (by positivity) hT0.le
        _ ≤ T * wa := mul_le_mul_of_nonneg_left h1 hT0.le
    calc wb * (e ^ 4 * A) = (e * A * wb) * (e * e ^ 2) := by ring
      _ ≤ 1 * (e * e ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = e * e ^ 2 := one_mul _
      _ ≤ T * wa := h3

theorem frameWt_div_le_div_ratio : ∀ (r : ℕ) (c : ℝ), 0 < c → ∃ K : ℝ, 0 ≤ K ∧ ∀ (s : Fin r), ∀ t ∈ cone r c,
    ∀ α β : FrameIx r, frameLev s β < frameLev s α → frameWt t β / frameWt t α ≤ K / ratio t s := by
  intro r c hc
  have hc0 : 0 < min c 1 := lt_min hc one_pos
  have hc1 : min c 1 ≤ 1 := min_le_right _ _
  set c' := min c 1 with hc'
  set e := c' ^ r with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := pow_le_one₀ hc0.le hc1
  refine ⟨(e ^ 4)⁻¹, by positivity, fun s t ht0 α β hlev => ?_⟩
  have ht : t ∈ cone r c' := cone_anti (min_le_left _ _) ht0
  have hpos := ht.1
  have hge : ∀ i, e ≤ t i := cone_pow_le hc0 hc1 ht
  have hle : ∀ {a b : Fin r}, a ≤ b → e * t b ≤ t a := fun h => cone_pow_mul_le hc0 hc1 ht h
  have hsq : e ^ 2 ≤ e := by nlinarith
  obtain ⟨T, heT, hrat, hTb⟩ : ∃ T, e ≤ T ∧ ratio t s = t s / T ∧ ∀ b : Fin r, s < b → e * t b ≤ T := by
    by_cases h : s.val + 1 < r
    · refine ⟨t ⟨s.val + 1, h⟩, hge _, by simp [ratio, h], fun b hb => hle ?_⟩
      have hb' : s.val < b.val := hb
      exact Fin.le_def.2 (by simp only []; omega)
    · refine ⟨1, he1, by simp [ratio, h], fun b hb => ?_⟩
      have hb' : s.val < b.val := hb
      have := b.2
      omega
  have hT0 : 0 < T := he0.trans_le heT
  have lev2 : ∀ γ, frameLev s γ = 2 → e * t s ≤ frameWt t γ := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simpa [frameWt] using hle ha
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
  have lev0 : ∀ γ, frameLev s γ = 0 → e * t s * frameWt t γ ≤ 1 := by
    intro γ h
    rcases γ with _ | a | a
    · simp [frameLev] at h
    · exfalso
      simp only [frameLev] at h
      split_ifs at h <;> omega
    · have ha : a ≤ s := by
        by_contra hn
        simp [frameLev, hn] at h
      simp only [frameWt]
      rw [← div_eq_mul_inv]
      exact (div_le_one (hpos a)).2 (hle ha)
  have lev1 : ∀ γ, frameLev s γ = 1 → e ^ 2 ≤ frameWt t γ * T ∧ frameWt t γ * e ^ 2 ≤ T := by
    intro γ h
    have key : ∀ b : Fin r, s < b → e ^ 2 ≤ t b * T ∧ t b * e ^ 2 ≤ T := fun b hb => by
      have h1 := hTb b hb
      have h2 := hge b
      constructor
      · rw [sq]
        exact mul_le_mul h2 heT he0.le (hpos b).le
      · have : 0 ≤ e * t b := (mul_pos he0 (hpos b)).le
        nlinarith
    rcases γ with _ | a | a
    · simp only [frameWt, one_mul]
      exact ⟨hsq.trans heT, hsq.trans heT⟩
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      simpa [frameWt] using key a ha
    · have ha : s < a := by
        by_contra hn
        simp [frameLev, not_lt.1 hn] at h
      have h1 := hTb a ha
      have h2 := hge a
      simp only [frameWt]
      rw [inv_mul_eq_div, inv_mul_eq_div, le_div_iff₀ (hpos a), div_le_iff₀ (hpos a)]
      constructor
      · have : 0 ≤ e * t a := (mul_pos he0 (hpos a)).le
        nlinarith
      · rw [sq]
        exact mul_le_mul heT h2 he0.le hT0.le |>.trans_eq' (by ring) |>.trans_eq (by ring)
  have lvl : ∀ γ, frameLev s γ = 0 ∨ frameLev s γ = 1 ∨ frameLev s γ = 2 := by
    intro γ
    rcases γ with _ | a | a <;> simp only [frameLev] <;> (try split_ifs) <;> simp
  have hcases : (e * t s ≤ frameWt t α ∧ frameWt t β * e ^ 2 ≤ T) ∨
      (e ^ 2 ≤ frameWt t α * T ∧ e * t s * frameWt t β ≤ 1) ∨
      (e * t s ≤ frameWt t α ∧ e * t s * frameWt t β ≤ 1) := by
    rcases lvl α with a | a | a <;> rcases lvl β with b | b | b <;> rw [a, b] at hlev <;>
      first
        | exact Or.inl ⟨lev2 α a, (lev1 β b).2⟩
        | exact Or.inr (Or.inl ⟨(lev1 α a).1, lev0 β b⟩)
        | exact Or.inr (Or.inr ⟨lev2 α a, lev0 β b⟩)
        | (exfalso; omega)
  have key := weights_across_levels he0 he1 (hge s) heT hcases
  have hwa : 0 < frameWt t α := frameWt_pos hpos α
  have hA0 : 0 < t s := hpos s
  have hK : (e ^ 4)⁻¹ / ratio t s = T / (e ^ 4 * t s) := by
    rw [hrat]
    field_simp
  rw [hK, div_le_div_iff₀ hwa (by positivity)]
  exact key

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeakHolo

open _root_.Metric Set Filter _root_.Topology Complex Real

theorem taylor_two {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r M : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ (3 * r) ⊆ U) (hM : ∀ z ∈ closedBall s₀ (3 * r), ‖f z‖ ≤ M) {η : ℂ}
    (hη : ‖η‖ ≤ r) : ‖f (s₀ + η) - f s₀ - η * deriv f s₀‖ ≤ M / r ^ 2 * ‖η‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U :=
    ((hf.analyticOnNhd hU).deriv_of_isOpen hU).differentiableOn
  have h1 : ∀ z ∈ closedBall s₀ (2 * r), ‖deriv f z‖ ≤ M / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (3 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hf.diffContOnCl_ball (hsub.trans hb))
      fun w hw => hM w (hsub (sphere_subset_closedBall hw))
  have h2 : ∀ z ∈ closedBall s₀ r, ‖deriv (deriv f) z‖ ≤ M / r / r := by
    intro z hz
    have hsub : closedBall z r ⊆ closedBall s₀ (2 * r) := by
      refine closedBall_subset_closedBall' ?_
      have := mem_closedBall.1 hz
      linarith
    have hsub' : closedBall s₀ (2 * r) ⊆ closedBall s₀ (3 * r) :=
      closedBall_subset_closedBall (by linarith)
    exact norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hdf.diffContOnCl_ball ((hsub.trans hsub').trans hb))
      fun w hw => h1 w (hsub (sphere_subset_closedBall hw))
  have hin : ∀ z ∈ closedBall s₀ r, z ∈ U := fun z hz =>
    hb (closedBall_subset_closedBall (by linarith) hz)
  have hc : s₀ ∈ closedBall s₀ r := mem_closedBall_self hr.le
  have h3 : ∀ z ∈ closedBall s₀ r, ‖deriv f z - deriv f s₀‖ ≤ M / r / r * ‖z - s₀‖ := fun z hz =>
    (convex_closedBall s₀ r).norm_image_sub_le_of_norm_deriv_le
      (fun y hy => (hdf y (hin y hy)).differentiableAt (hU.mem_nhds (hin y hy))) h2 hc hz
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM s₀ (mem_closedBall_self (by positivity)))
  have hs : closedBall s₀ ‖η‖ ⊆ closedBall s₀ r := closedBall_subset_closedBall hη
  have h4 := (convex_closedBall s₀ ‖η‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => f z - z * deriv f s₀) (f' := fun z => deriv f z - deriv f s₀) (C := M / r / r * ‖η‖)
    (fun z hz => by
      have a := ((hf z (hin z (hs hz))).differentiableAt (hU.mem_nhds (hin z (hs hz)))).hasDerivAt
      have b := (hasDerivAt_id z).mul_const (deriv f s₀)
      have c : HasDerivAt (fun z => f z - z * deriv f s₀) (deriv f z - 1 * deriv f s₀) z := a.sub b
      rw [one_mul] at c
      exact c.hasDerivWithinAt)
    (fun z hz => (h3 z (hs hz)).trans (by
      have := mem_closedBall_iff_norm.1 hz
      gcongr))
    (mem_closedBall_self (norm_nonneg η)) (x := s₀) (y := s₀ + η) (by simp [mem_closedBall_iff_norm])
  have e : f (s₀ + η) - f s₀ - η * deriv f s₀ =
      (f (s₀ + η) - (s₀ + η) * deriv f s₀) - (f s₀ - s₀ * deriv f s₀) := by ring
  rw [e]
  refine h4.trans (le_of_eq ?_)
  simp only [add_sub_cancel_left]
  field_simp

theorem deriv_circle {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) :
    deriv f c = (2 * π * I)⁻¹ * ∮ z in C(c, r), (1 / (z - c) ^ 2) • f z := by
  have := hf.circleIntegral_one_div_sub_center_pow_smul hr 1
  simp only [zero_add, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one] at this
  rw [this, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [pi_ne_zero]), one_mul]

theorem continuous_deriv_family {X : Type*} [TopologicalSpace X] {w : ℂ → X → ℂ} {S : Set ℂ} {s₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : closedBall s₀ r ⊆ S) (hd : ∀ x, DifferentiableOn ℂ (fun s => w s x) S)
    (hc : ContinuousOn (fun y : ℂ × X => w y.1 y.2) (S ×ˢ Set.univ)) :
    Continuous fun x => deriv (fun s => w s x) s₀ := by
  have e : (fun x => deriv (fun s => w s x) s₀) = fun x => (2 * π * I : ℂ)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap s₀ r) θ •
        ((1 / (circleMap s₀ r θ - s₀) ^ 2) • w (circleMap s₀ r θ) x) := by
    funext x
    rw [deriv_circle hr ((hd x).diffContOnCl_ball hb)]
    rfl
  rw [e]
  refine continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _)
  have hA : Continuous fun θ : ℝ => deriv (circleMap s₀ r) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hB : Continuous fun θ : ℝ => (1 / (circleMap s₀ r θ - s₀) ^ 2 : ℂ) :=
    continuous_const.div (((continuous_circleMap s₀ r).sub continuous_const).pow 2) fun θ =>
      pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
  have hC : Continuous fun p : X × ℝ => w (circleMap s₀ r p.2) p.1 :=
    hc.comp_continuous (((continuous_circleMap s₀ r).comp continuous_snd).prodMk continuous_fst)
      fun p => ⟨hb (circleMap_mem_closedBall s₀ hr.le p.2), mem_univ _⟩
  exact (hA.comp continuous_snd).smul ((hB.comp continuous_snd).smul hC)

theorem form_scale {X : Type*} {V : Submodule ℂ (X → ℂ)} (μ : V →ₗ[ℂ] ℂ) {b : X → ℝ} {K : ℝ}
    (hK : ∀ f : V, (∀ x, ‖f.1 x‖ ≤ b x) → ‖μ f‖ ≤ K) (f : V) {l : ℝ} (hl : 0 < l)
    (hf : ∀ x, ‖f.1 x‖ ≤ l * b x) : ‖μ f‖ ≤ K * l := by
  have h := hK (((l⁻¹ : ℝ) : ℂ) • f) fun x => by
    have e : ‖(((l⁻¹ : ℝ) : ℂ) • f).1 x‖ = l⁻¹ * ‖f.1 x‖ := by
      simp [abs_of_pos hl]
    rw [e, inv_mul_le_iff₀ hl]
    exact hf x
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl),
    inv_mul_le_iff₀ hl] at h
  linarith

theorem differentiableOn_form {X : Type*} [TopologicalSpace X] {h : X → ℝ} (hh : ∀ x, 0 ≤ h x)
    {V : Submodule ℂ (X → ℂ)}
    (hV : ∀ (g : X → ℂ) (A : ℝ) (N : ℕ), Continuous g → (∀ x, ‖g x‖ ≤ A * h x ^ N) → g ∈ V)
    (μ : V →ₗ[ℂ] ℂ) (hμ : ∀ N : ℕ, ∃ C : ℝ, ∀ f : V, (∀ x, ‖f.1 x‖ ≤ h x ^ N) → ‖μ f‖ ≤ C)
    (v : ℂ → V) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × X => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * h x ^ N) :
    DifferentiableOn ℂ (fun s => μ (v s)) S := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRS⟩ := nhds_basis_closedBall.mem_iff.1 (hS.mem_nhds hs₀)
  obtain ⟨C, N, hCN⟩ := hb _ hRS (isCompact_closedBall s₀ R)
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ R = 3 * r := ⟨R / 3, by positivity, by ring⟩
  have hsub : closedBall s₀ r ⊆ closedBall s₀ (3 * r) := closedBall_subset_closedBall (by linarith)
  let d : X → ℂ := fun x => deriv (fun s => (v s).1 x) s₀
  have dc : Continuous d := continuous_deriv_family (w := fun s => (v s).1) hr (hsub.trans hRS) hd hc
  have dB : ∀ x, ‖d x‖ ≤ C / r * h x ^ N := fun x => by
    have := norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun s => (v s).1 x) (c := s₀) hr
      ((hd x).diffContOnCl_ball (hsub.trans hRS)) (C := C * h x ^ N)
      fun z hz => hCN z (hsub (sphere_subset_closedBall hz)) x
    calc ‖d x‖ ≤ C * h x ^ N / r := this
      _ = C / r * h x ^ N := by ring
  let D : V := ⟨d, hV d _ N dc dB⟩
  obtain ⟨K, hK⟩ := hμ N
  set B : ℝ := |C| / r ^ 2 + 1 with hB
  have hBpos : 0 < B := by positivity
  have key : ∀ η : ℂ, ‖η‖ < r →
      ‖μ (v (s₀ + η)) - μ (v s₀) - η • μ D‖ ≤ K * B * ‖η ^ 2‖ := by
    intro η hη
    by_cases h0 : η = 0
    · simp [h0]
    have hηp : 0 < ‖η‖ := norm_pos_iff.2 h0
    have e : μ (v (s₀ + η)) - μ (v s₀) - η • μ D = μ (v (s₀ + η) - v s₀ - η • D) := by
      simp only [map_sub, map_smul]
    rw [e, norm_pow, mul_assoc]
    refine form_scale μ hK _ (by positivity) fun x => ?_
    have t := taylor_two hS (hd x) hr hRS (fun z hz => hCN z hz x) hη.le
    have hp : 0 ≤ h x ^ N := pow_nonneg (hh x) N
    have e2 : (v (s₀ + η) - v s₀ - η • D).1 x =
        (v (s₀ + η)).1 x - (v s₀).1 x - η * deriv (fun s => (v s).1 x) s₀ := rfl
    rw [e2]
    refine t.trans ?_
    have : C * h x ^ N / r ^ 2 * ‖η‖ ^ 2 = (C / r ^ 2) * (‖η‖ ^ 2 * h x ^ N) := by ring
    rw [this, show B * ‖η‖ ^ 2 * h x ^ N = B * (‖η‖ ^ 2 * h x ^ N) by ring]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [hB]
    have : C / r ^ 2 ≤ |C| / r ^ 2 := by gcongr; exact le_abs_self C
    linarith
  have hO : (fun η : ℂ => μ (v (s₀ + η)) - μ (v s₀) - η • μ D) =O[𝓝 0] fun η => η ^ 2 :=
    Asymptotics.IsBigO.of_bound (K * B) (Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hr)
      fun η hη => key η (by simpa using hη))
  exact (hasDerivAt_iff_isLittleO_nhds_zero.2
    (hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two))).differentiableAt.differentiableWithinAt

end GlobalTheory.CompanionTheory.WeakHolo

namespace GlobalTheory.CompanionTheory.WeakHolo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem mem_modFun {g : G2 σ Y → ℂ} {A : ℝ} {N : ℕ} (hg : Continuous g)
    (hA : ∀ x, ‖g x‖ ≤ A * (ht2 x : ℝ) ^ N) : g ∈ modFun σ Y := by
  have hp : 0 < |A| + 1 := by positivity
  have hq : (((|A| + 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((((|A| + 1 : ℝ)) : ℂ)⁻¹ • g) ∈ modFun σ Y := by
    refine Submodule.subset_span ⟨hg.const_smul _, N, fun x => ?_⟩
    have hh : 0 ≤ (ht2 x : ℝ) ^ N := by positivity
    rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
      inv_mul_le_iff₀ hp]
    refine (hA x).trans (mul_le_mul_of_nonneg_right ?_ hh)
    linarith [le_abs_self A]
  have := (modFun σ Y).smul_mem (((|A| + 1 : ℝ)) : ℂ) h1
  rwa [smul_inv_smul₀ hq] at this

theorem wholo_growForms (v : ℂ → modFun σ Y) {S : Set ℂ} (hS : IsOpen S)
    (hd : ∀ x, DifferentiableOn ℂ (fun s => (v s).1 x) S)
    (hc : ContinuousOn (fun y : ℂ × G2 σ Y => (v y.1).1 y.2) (S ×ˢ Set.univ))
    (hb : ∀ Q : Set ℂ, Q ⊆ S → IsCompact Q → ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Q, ∀ x, ‖(v s).1 x‖ ≤ C * (ht2 x : ℝ) ^ N) :
    WHolo {μ | IsGrowForm μ} v S := fun μ hμ =>
  differentiableOn_form (h := fun x : G2 σ Y => (ht2 x : ℝ)) (fun x => NNReal.coe_nonneg _)
    (fun _ _ _ hg hA => mem_modFun hg hA) μ hμ v hS hd hc hb

end GlobalTheory.CompanionTheory.WeakHolo

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CtGrowth
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.Growth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem exists_unip_bound {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : BlockIx a r → Ad E) (y : GL (Fin a) (Cinf E)),
      ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm) :=
    hCm.image (JointCont.continuous_finPart g)
  obtain ⟨C₀, N, hC₀, hgrow⟩ := GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT
  have hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x) := by
    have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
      continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)
    exact (JointCont.continuous_unip.comp h1).mul continuous_const
  obtain ⟨B, hB⟩ := (hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove
  have hc : (0 : ℝ) ≤ 1 + 2 * a := by positivity
  refine ⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  have e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) =
      ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y)) := by
    rw [unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]
  rw [e1, hφ.left]
  refine (hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_
  have hb : height (JointCont.infPart g x') ≤ max B 1 := le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)
  have hy := one_le_height y
  have hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y := by
    refine (GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀

theorem ct_growth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g
  have := hμ
  obtain ⟨C, N, -, h⟩ := exists_unip_bound (r := r) hφ g
  refine ⟨C * μ.real 𝓕, N, fun y => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_
  ring

end GlobalTheory.CompanionTheory.CTFin.Growth

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOneStatement
section
open GlobalTheory.CompanionTheory.ModelS (SmF Kf)

theorem GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one :
    ∀ (n : ℕ) (S : Submodule ℂ (SmF n)), FiniteDimensional ℂ S →
      (∀ a b : Fin n, ∀ w ∈ S, Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
      ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 :=
  GlobalTheory.CompanionTheory.ModelS.Sep.main
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupportStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_char_zero_dim_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | exact GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.chi_eq_ncard_support <;> assumption)
end

