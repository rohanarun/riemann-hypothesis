module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowSizeWSizeBmSizeXpp
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem window_scale_bounds (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (cD ch : ℝ) :
    ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L →
      2 ≤ L.sc.x ∧ Real.sqrt L.sc.b ≤ L.sc.w'' D.R.n ∧ L.etaSz + 1 ≤ L.sc.w'' D.R.n ∧
      L.sc.w'' D.R.n ≤ L.sc.b' ∧ L.sc.b' ≤ L.sc.b ∧ ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b := by
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x2, h2⟩ := GlobalTheory.scale_poly_comparison eps (max ch 0 + 10) (1 / 2) he (by norm_num)
  obtain ⟨CN, x3, h3⟩ := GlobalTheory.topCount_and_lambda_bounds eps he he'
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 1 2 (2 * (max 1 C.GK.La * CN ^ 2)) 2 (by norm_num)
  refine ⟨max (max x1 x2) (max (max x3 x4) 2), fun D L hs hx hV => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx2 : x2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ L.sc.x :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx4 : x4 ≤ L.sc.x :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx))
  have hx5 : 2 ≤ L.sc.x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hf, hm, -⟩ := h1 L.sc D.R hs hx1 hV.ranks
  obtain ⟨-, -, -, hb', -, hw, -⟩ := h2 L.sc hs hx2
  obtain ⟨-, -, hLa⟩ := h3 L.sc hs hx3
  have hLa' := (hLa { C.GK with La := max 1 C.GK.La } (le_max_left _ _)).2
  have h4' := h4 L.sc.x hx4
  clear h1 h2 h3 h4 hLa hx1 hx2 hx3 hx4 hx
  have hetaE := hV.eta_eq
  have hLaE := hV.La_eq
  have hbT := hV.bT_le
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn0 : (0 : ℝ) ≤ D.R.n := Nat.cast_nonneg _
  obtain ⟨hw1, hw2, -⟩ := hw D.R.n hn1 (by linarith)
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hsq : L.sc.b ^ (1 - 1 / 2 : ℝ) = Real.sqrt L.sc.b := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hsq1 : 1 ≤ Real.sqrt L.sc.b := Real.one_le_sqrt.2 hb1
  rw [hsq] at hw1
  have hy1 : 1 ≤ L.sc.x ^ (max ch 0) := Real.one_le_rpow hone (le_max_right _ _)
  have hych : L.sc.x ^ ch ≤ L.sc.x ^ (max ch 0) := Real.rpow_le_rpow_of_exponent_le hone (le_max_left _ _)
  have hsplit : L.sc.x ^ (max ch 0 + 10) = L.sc.x ^ (max ch 0) * L.sc.x ^ 10 := by
    rw [Real.rpow_add hx0]; norm_num
  rw [hsplit] at hw1 hb'
  have hb'0 : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    positivity
  have hf3 : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by
    have : L.sc.x ^ (3 : ℝ) = L.sc.x ^ 3 := by norm_num
    rw [← this]; exact hf
  have hxe : L.sc.x ^ L.sc.eps ≤ L.sc.x := by
    have := Real.rpow_le_rpow_of_exponent_le hone (show L.sc.eps ≤ 1 by rw [hs]; linarith)
    rwa [Real.rpow_one] at this
  have hxe0 : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx0.le _
  have hd1 : L.sc.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hone (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hLa2 : L.LaG ≤ L.sc.x ^ 2 := by
    have ha : 0 ≤ Real.log L.sc.a := by
      apply Real.log_nonneg
      unfold Scale.a
      exact one_le_mul_of_one_le_of_one_le hone hb1
    have e1 : L.LaG ≤ G.La { C.GK with La := max 1 C.GK.La } L.sc := by
      rw [hLaE]
      unfold G.La
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) ha
    have e2 : L.sc.x ^ (2 : ℝ) = L.sc.x ^ 2 := by norm_num
    rw [Real.rpow_one, e2] at h4'
    have e3 : 0 ≤ max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 := by
      have : 0 ≤ max 1 C.GK.La := le_trans zero_le_one (le_max_left _ _)
      positivity
    have e4 : max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x) :=
      mul_le_mul_of_nonneg_left (by linarith) e3
    have e5 : G.La { C.GK with La := max 1 C.GK.La } L.sc ≤
        max 1 C.GK.La * CN ^ 2 * Real.log L.sc.x ^ 2 * (2 * L.sc.x ^ L.sc.eps) := hLa'
    linarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (show 1 ≤ D.R.k by omega)
  have hh0 : (h0v L.sc ch : ℝ) ≤ 4 * L.sc.x ^ (max ch 0) := by
    unfold h0v
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le ch)
    push_cast
    linarith
  have hh00 : (0 : ℝ) ≤ h0v L.sc ch := Nat.cast_nonneg _
  have heta : L.etaSz ≤ L.sc.x * (4 * L.sc.x ^ (max ch 0)) := by
    rw [hetaE]; exact mul_le_mul hm hh0 hh00 hx0.le
  have hterm : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) ≤
      L.sc.x ^ 6 * L.sc.b' := by
    have e1 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ 3 * 1 * L.sc.x := by
      have e0 : 2 * (D.R.n : ℝ) ≤ L.sc.x ^ 3 := hfn ▸ hf3
      exact mul_le_mul (mul_le_mul e0 hd1 hd0 (by positivity)) hxe hxe0 (by positivity)
    have e2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG ≤ L.sc.x ^ 6 := by
      calc _ ≤ 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.sc.x ^ 2 :=
            mul_le_mul_of_nonneg_left hLa2 (by positivity)
        _ ≤ L.sc.x ^ 3 * 1 * L.sc.x * L.sc.x ^ 2 := mul_le_mul_of_nonneg_right e1 (by positivity)
        _ = _ := by ring
    rw [div_le_iff₀ (by linarith)]
    calc _ ≤ L.sc.x ^ 6 * L.sc.b' := mul_le_mul_of_nonneg_right e2 hb'0.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hk1
  have hdiv : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0.le hone
  clear hych hsplit hh0 hLa' h4' hw
  generalize L.sc.x ^ (max ch 0) = y at hw1 hb' hy1 heta
  have hp4 : (16 : ℝ) ≤ L.sc.x ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hx5 4
    linarith
  have hp6 : L.sc.x ≤ L.sc.x ^ 6 := le_self_pow₀ hone (by norm_num)
  have hp10 : 16 * L.sc.x ^ 6 ≤ L.sc.x ^ 10 := by
    calc _ ≤ L.sc.x ^ 4 * L.sc.x ^ 6 := mul_le_mul_of_nonneg_right hp4 (by positivity)
      _ = _ := by ring
  have hyx : L.sc.x ^ 10 ≤ y * L.sc.x ^ 10 := le_mul_of_one_le_left (by positivity) hy1
  have hyx1 : 1 ≤ y * L.sc.x ^ 10 := by linarith
  have hA : y * (16 * L.sc.x) ≤ y * L.sc.x ^ 10 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : 1 ≤ y * L.sc.x := one_le_mul_of_one_le_of_one_le hy1 hone
  have hC : y * L.sc.x ^ 10 ≤ Real.sqrt L.sc.b * (y * L.sc.x ^ 10) := le_mul_of_one_le_left (by linarith) hsq1
  have hD : L.sc.b' * (L.sc.x ^ 6 + 2) ≤ L.sc.b' * (y * L.sc.x ^ 10) :=
    mul_le_mul_of_nonneg_left (by linarith) hb'0.le
  refine ⟨hx5, le_trans (le_mul_of_one_le_right (by linarith) hyx1) hw1, by linarith, hw2,
    le_trans (le_mul_of_one_le_right hb'0.le hyx1) hb', fun t => ?_⟩
  have := hbT t
  linarith

theorem place_top_or_thick_or_thin (D : D7) (τ : D.what₂.Tau) :
    (∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t) ∨
      (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces ∨ D.host.IsThin (D.eTau τ : D.R.GG) := by
  by_cases h1 : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · left
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  · by_cases h2 : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨(D.eTau τ).2, h1, h2⟩)

theorem szRow_sizeW_sizeBm_sizeXpp : SzRow (fun _ _ L => SizeW L ∧ SizeBm L ∧ SizeXpp L) := by
  intro eps he he' C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x0, h⟩ := window_scale_bounds eps he he' C cD ch
  refine ⟨x0, fun D L hs hx hV => ?_⟩
  obtain ⟨hx2, hW, heta, hwb, hbb, htop⟩ := h D L hs hx hV
  have heta0 := L.etaSz_pos
  have hx0 : 0 < L.sc.x := by linarith
  have hdiv : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx0.le
  refine ⟨hW, ?_, ?_⟩
  · intro τ hm
    obtain ⟨-, -, ⟨b1, hb, h1, h2, h3⟩, -⟩ := hV.hc
    have hlow : L.sc.w'' D.R.n ≤ (b1 τ : ℝ) := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · rw [h1 τ t ht]
        have e1 : (0 : ℝ) ≤ (⌊L.sc.b' / L.sc.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 hdiv
        have e2 := L.bT_ge t
        push_cast
        linarith
      · have e1 := Int.le_ceil L.sc.b
        have e2 : ((⌈L.sc.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast (h2 τ ht).1
        linarith
      · rw [h3 τ ht]; exact Int.le_ceil _
    rw [(hb τ _).1, (hb τ _).1]
    have e1 : ((D.R.m - 1 : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast Nat.sub_le _ _
    have e2 : ((D.R.m - 1 : ℕ) : ℝ) * (h0v L.sc ch : ℝ) ≤ L.etaSz := by
      rw [hV.eta_eq]; exact mul_le_mul_of_nonneg_right e1 (Nat.cast_nonneg _)
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Nat.cast_zero, zero_mul, add_zero]
    linarith
  · intro j τ j' τ' hj1 hj2 hj1' hj2'
    have hup : wj D j τ ≤ 2 * L.sc.b := by
      rcases place_top_or_thick_or_thin D τ with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j hj1 hj2 τ t ht).2
        have := htop t
        linarith
      · have := (L.win_thick j hj1 hj2 τ ht).2
        linarith
      · have := (L.win_thin j hj1 hj2 τ ht).2
        linarith
    have hlo : L.sc.w'' D.R.n ≤ wj D j' τ' := by
      rcases place_top_or_thick_or_thin D τ' with ⟨t, ht⟩ | ht | ht
      · have := (L.win_top j' hj1' hj2' τ' t ht).1
        have := L.bT_ge t
        linarith
      · have := (L.win_thick j' hj1' hj2' τ' ht).1
        linarith
      · exact (L.win_thin j' hj1' hj2' τ' ht).1
    have hw0 : 0 < L.sc.w'' D.R.n := by linarith
    have hb0 : 0 < L.sc.b := by linarith
    have hX0 : 0 ≤ L.sc.X'' D.R.n := by
      unfold Scale.X'' Scale.a; positivity
    have hXw : L.sc.X'' D.R.n * L.sc.w'' D.R.n = L.sc.x * L.sc.b := by
      unfold Scale.X'' Scale.a; exact div_mul_cancel₀ _ hw0.ne'
    calc wj D j τ ≤ 2 * L.sc.b := hup
      _ ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx2 hb0.le
      _ = _ := hXw.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hX0

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTypePrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_typePrimes : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  intro eps he he' C hC
  obtain ⟨-, -, -, -, -, hYL, -, -, -, -, -, -, hpde, -⟩ := hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he he' hpde
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.EX.rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow 0 eps 1608 1 he
  obtain ⟨x4, h4⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (eps / 5) eps (2 * |C.P.CY|) 2 (by linarith)
  refine ⟨max (max x1 x2) (max x3 x4), fun D L hL hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, -, -, hc, -⟩ := h1 L.sc D.R D.host hL hx1 V.ranks V.host
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := h2 L.sc D.R hL hx2 V.ranks
  have h3' := h3 _ hx3
  have h4' := h4 _ hx4
  rw [Real.rpow_zero, mul_one, pow_one] at h3'
  rw [← hL] at h3' h4'
  have hLdef : L.sc.L = L.sc.x ^ L.sc.eps := rfl
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  rw [← hLdef] at h3' h4'
  have hx1' : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlog : 0 < Real.log L.sc.x := Real.log_pos hx1'
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have h := V.ranks.2.2.1.1
    have : 1 ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := Real.one_le_rpow hx1'.le (by rw [hL]; linarith)
    linarith
  have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hbpos : 0 < L.sc.b := by rw [hb]; exact Real.exp_pos _
  have hkb : 0 < (D.R.k : ℝ) * L.sc.b := by positivity
  refine ⟨((D.R.k : ℝ) * L.sc.b) ^ 8, le_rfl, ?_, ?_, V.host.2.2.2.2.1⟩
  · have hY : (((D.R.k : ℝ) * L.sc.b) ^ 8) ^ ((1 : ℝ) / 4) = ((D.R.k : ℝ) * L.sc.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkb.le, ← Real.rpow_natCast]
      norm_num
    rw [hY]
    have hcE : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by
      unfold condE; push_cast; ring
    have hc1 : (1 : ℝ) ≤ (condE D : ℝ) := by
      have : condE D ≠ 0 := by
        have hQS := D.host.QS_pos
        have hq0 := D.host.hyp.1.pos
        have hd0 := D.host.hyp.2.1.pos
        unfold condE; positivity
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
    rw [← hcE] at hc
    have hlc : 0 ≤ Real.log (condE D : ℝ) := Real.log_nonneg hc1
    have hA : (condE D : ℝ) ^ C.P.CY ≤ L.sc.b := by
      rw [Real.rpow_def_of_pos (by linarith), hb]
      apply Real.exp_le_exp.mpr
      calc Real.log (condE D : ℝ) * C.P.CY ≤ Real.log (condE D : ℝ) * |C.P.CY| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hlc
        _ ≤ (2 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) * |C.P.CY| :=
            mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = 2 * |C.P.CY| * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 := by ring
        _ ≤ _ := h4'
    have hB : (D.R.N D.R.m : ℝ) ^ 4 ≤ L.sc.b := by
      calc (D.R.N D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ (402 : ℝ)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 4
        _ = Real.exp (1608 * Real.log L.sc.x) := by
            rw [Real.rpow_def_of_pos hx0, ← Real.exp_nat_mul]; congr 1; push_cast; ring
        _ ≤ L.sc.b := by rw [hb]; exact Real.exp_le_exp.mpr h3'
    calc (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ L.sc.b * L.sc.b :=
          mul_le_mul hB hA (Real.rpow_nonneg (by linarith) _) hbpos.le
      _ = L.sc.b ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ hbpos.le (le_mul_of_one_le_left hbpos.le hk1) 2
  · rw [hYL, Real.log_pow, Real.log_mul (by positivity) hbpos.ne', hb, Real.log_exp]
    have : Real.log (D.R.k : ℝ) ≤ 5 * Real.log L.sc.x := by
      rw [← Real.log_rpow hx0]; exact Real.log_le_log (by linarith) hk5
    push_cast
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section Inputs

open Formalism.MainNotions.TaylorLogMetric

def goodLifts (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {y | ∃ κ : 𝓞 D.host.K,
    ‖lamC lam (D.host.φ₀ (D.host.conj ((κ : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
    ∃ x ∈ La D T L L', y = (D.host.φ₀ ((κ : D.host.K) : D.host.E) * (N₀ : ℂ) / (p : ℂ) ^ n) • x}

def MomentsAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Ω : ℂ_[p]) : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
    ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
      ∀ (n : ℕ), ∀ y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L',
        CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L'))) Qbar ∧
        ∀ (m : ℕ) (y' : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) =
            lamC lam (kap D (tor0 D cc δ) (δ • embV D (tor0 D cc δ) (∑ i, (a i : D.host.E) • b i)) y) *
              ∏ j, pairN D lam Ω b (y' j) fun i => (a i : ℤ_[p])) →
          jet D lam y' (pSer D lam (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L')))) = μ g

def MovesAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ

def LatticeFactsAll : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ →
    ∀ a b : ℕ, Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b

end Inputs

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

def emb (x : HomE X.E a b) : VCx X.Tau a b := embH (X.embC A.σ₀) A.δ x

def Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) : VCx X.Tau a b → ℂ :=
  fun z => alV A.d A.sc (emb A x) * opU (HV A.sc) (emb A x) F z

def imH (x y : HomE X.E a b) : ℝ := altE (HV A.sc) (emb A x) (emb A y)

def coc (x y : HomE X.E a b) : ℝ := (Real.sqrt A.d * (HV A.sc (emb A x) (emb A y)).re + imH A x y) / 2

def brkE (y t : HomE X.E a b) : ℂ := brk (HV A.sc) (emb A y) (emb A t)

abbrev per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  perO A.AA N N'

def smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  M.map ((r • (LinearMap.id : HomE X.E a b →ₗ[X.E] HomE X.E a b)).restrictScalars (𝓞 X.E))

theorem mem_smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) (y : HomE X.E a b) :
    y ∈ smulLat r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl


variable (a b) in
def PtMom {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (v : X.E) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ t : HomE X.E a b, (∃ n : ℕ, Nat.Coprime n p ∧ (n : X.E) • t ∈ per A N N') →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      (∀ y ∈ per A N N', ∀ m, jetC A.cD (Wx A (((N₀ : X.E) * v) • y) (Wx A t (A.e a b N N'))) m ∈ TaylorLogMetric.Qbar) ∧
      InIntClosure (per A N N' : Set (HomE X.E a b))
        (fun x (k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ)) =>
          TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * v) • k.1) x) * ptTab ι un x k.2)
        {k | k.1 ∈ per A N N'}
        fun k => TaylorLogMetric.lamC lam (jetC A.cD (Wx A (((N₀ : X.E) * v) • k.1) (Wx A t (A.e a b N N'))) k.2)


variable (a b) in
def Ctx (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AAUnit (divs (X.conjO ϖ)) ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧
    IsCoprime ϖ (X.conjO ϖ) ∧ (∀ P, P ∈ S ↔ ϖ ∈ P.asIdeal ∨ P ∈ SG) ∧ (∀ P ∈ SG, (p : 𝓞 X.E) ∉ P.asIdeal) ∧
    Nat.Coprime g p ∧ Nat.Coprime cA p

end Ops

section Clo

variable {p : ℕ} [Fact p.Prime] {H I : Type}

theorem clo_zero (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) : InIntClosure Sup tab M fun _ => 0 := by
  intro F _ ε hε
  exact ⟨0, by simp, by simp, by simpa using fun _ _ => hε⟩

theorem clo_add {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (h' : InIntClosure Sup tab M J') : InIntClosure Sup tab M fun m => J m + J' m := by
  classical
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F hF ε hε
  obtain ⟨c', hc', hc1', hcF'⟩ := h' F hF ε hε
  refine ⟨c + c', ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add (Finset.mem_coe.1 hx)) with h | h
    exacts [hc h, hc' h]
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc1 x) (hc1' x))
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
    have : J m + J' m - ((c.sum fun x r => r * tab x m) + c'.sum fun x r => r * tab x m) =
        (J m - c.sum fun x r => r * tab x m) + (J' m - c'.sum fun x r => r * tab x m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hcF m hm) (hcF' m hm))

theorem clo_sum {κ : Type} {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} (s : Finset κ) (J : κ → I → ℂ_[p])
    (h : ∀ k ∈ s, InIntClosure Sup tab M (J k)) : InIntClosure Sup tab M fun m => ∑ k ∈ s, J k m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clo_zero Sup tab M
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact clo_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem clo_congr {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {M M' : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (hS : Sup ⊆ Sup') (hM : M' ⊆ M) (hJ : ∀ m ∈ M', J' m = J m) :
    InIntClosure Sup' tab M' J' := by
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F (hF.trans hM) ε hε
  exact ⟨c, hc.trans hS, hc1, fun m hm => by rw [hJ m (hF hm)]; exact hcF m hm⟩

theorem clo_comb {I' κ : Type} {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {tab' : H → I' → ℂ_[p]} {M : Set I} {M' : Set I'}
    {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J) (s : Finset κ) (r : κ → I' → ℂ_[p]) (φ : κ → I' → I)
    (hφ : ∀ k ∈ s, ∀ m ∈ M', φ k m ∈ M) (w : H → ℂ_[p]) (hw : ∀ x ∈ Sup, ‖w x‖ ≤ 1) (hw0 : ∀ x ∈ Sup, x ∉ Sup' → w x = 0)
    (htab : ∀ x ∈ Sup, ∀ m ∈ M', ∑ k ∈ s, r k m * tab x (φ k m) = w x * tab' x m) :
    InIntClosure Sup' tab' M' fun m => ∑ k ∈ s, r k m * J (φ k m) := by
  classical
  intro F hF ε hε
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ k ∈ s, ∀ m ∈ F, ‖r k m‖ ≤ C := by
    refine ⟨1 + ∑ q ∈ s ×ˢ F, ‖r q.1 q.2‖, by positivity, fun k hk m hm => ?_⟩
    have := Finset.single_le_sum (f := fun q : κ × I' => ‖r q.1 q.2‖) (fun _ _ => norm_nonneg _)
      (Finset.mk_mem_product hk hm)
    linarith
  obtain ⟨c, hc, hc1, hcF⟩ := h ((s ×ˢ F).image fun q => φ q.1 q.2) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hφ _ (Finset.mem_product.1 hq).1 _ (hF (Finset.mem_product.1 hq).2)) (ε / 2 / C) (by positivity)
  have hmem : ∀ x, c x ≠ 0 → x ∈ Sup := fun x hx => hc (Finsupp.mem_support_iff.2 hx)
  refine ⟨Finsupp.onFinset c.support (fun x => c x * w x) (fun x hx => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hx)),
    ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    have hx' : c x * w x ≠ 0 := by simpa using hx
    by_contra hn
    exact hx' (by rw [hw0 x (hmem x (left_ne_zero_of_mul hx')) hn, mul_zero])
  · rw [Finsupp.onFinset_apply]
    by_cases hx : c x = 0
    · simp [hx]
    · rw [norm_mul]; exact mul_le_one₀ (hc1 x) (norm_nonneg _) (hw x (hmem x hx))
  · rw [Finsupp.onFinset_sum _ (by simp)]
    have e : ∑ k ∈ s, r k m * J (φ k m) - ∑ x ∈ c.support, c x * w x * tab' x m =
        ∑ k ∈ s, r k m * (J (φ k m) - c.sum fun x q => q * tab x (φ k m)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finsupp.sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mul_assoc, ← htab x (hc hx) m (hF hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ε / 2) (by positivity) fun k hk => ?_)
      (by linarith)
    rw [norm_mul]
    have h1 := hcF (φ k m) (Finset.mem_image.2 ⟨(k, m), Finset.mk_mem_product hk hm, rfl⟩)
    calc _ ≤ C * (ε / 2 / C) := mul_le_mul (hC k hk m hm) h1.le (norm_nonneg _) hC0.le
      _ = ε / 2 := by field_simp

theorem clo_smul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r c : ℂ_[p]) (hc : c ≠ 0) (hr : ‖r‖ ≤ ‖c‖) :
    InIntClosure Sup (fun x m => c * tab x m) M fun m => r * J m := by
  have := clo_comb (Sup' := Sup) (tab' := fun x m => c * tab x m) (M' := M) h ({()} : Finset Unit) (fun _ _ => r) (fun _ m => m)
    (fun _ _ _ hm => hm) (fun _ => r / c)
    (fun _ _ => by rw [norm_div]; exact div_le_one_of_le₀ hr (norm_nonneg _)) (fun _ h h' => absurd h h')
    (fun x _ m _ => by simp only [Finset.sum_singleton]; field_simp)
  simpa using this

theorem clo_mul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r : ℂ_[p]) (hr : ‖r‖ ≤ 1) : InIntClosure Sup tab M fun m => r * J m := by
  simpa using clo_smul h r 1 one_ne_zero (by simpa using hr)

end Clo

end GlobalTheory.MomT
end
end

