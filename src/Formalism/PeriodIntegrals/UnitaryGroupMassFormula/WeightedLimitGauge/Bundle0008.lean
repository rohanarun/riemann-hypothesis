module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.UnimodS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvD

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem continuous_hq (k : ℕ) (T' : ℝ) : Continuous (fun p : (Fin k → ℂ) × ℝ => hq k T' p.1 p.2) := by
  unfold hq
  refine continuous_fst.prodMk ?_
  refine (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
    ((continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp
      ((continuous_apply i).comp continuous_fst)).add continuous_const))).mul ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem hq_periodic (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : hq k T' y (θ + 2 * Real.pi) = hq k T' y θ := by
  have key : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have e : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I = θ * Complex.I + 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold hq
  rw [key]

theorem lint_shift (P : ℝ → ℝ≥0∞) (hP : Measurable P) (hper : ∀ θ, P (θ + 2 * Real.pi) = P θ) :
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), P θ = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, P θ := by
  have hπ := Real.pi_pos
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume))]
  have h1 : Set.Ioc 0 (2 * Real.pi) = Set.Ioc 0 Real.pi ∪ Set.Ioc Real.pi (2 * Real.pi) :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have h2 : Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) 0 ∪ Set.Ioc 0 Real.pi :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  rw [h1, h2, lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl),
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl), add_comm]
  congr 1
  have hmp : MeasurePreserving (fun x : ℝ => x + 2 * Real.pi) volume volume := measurePreserving_add_right volume _
  have hpre : (fun x : ℝ => x + 2 * Real.pi) ⁻¹' Set.Ioc Real.pi (2 * Real.pi) = Set.Ioc (-Real.pi) 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩; constructor <;> linarith
    · rintro ⟨a, b⟩; constructor <;> linarith
  have := hmp.setLIntegral_comp_preimage (s := Set.Ioc Real.pi (2 * Real.pi)) measurableSet_Ioc hP
  rw [hpre] at this
  rw [← this]
  exact lintegral_congr fun a => hper a

theorem hypTh : HypTh := by
  intro k T' hT'
  let L : EuclideanSpace ℂ (Fin k) ≃L[ℝ] (Fin k → ℂ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℂ)
  set μ' : Measure (Fin k → ℂ) := (volume : Measure (EuclideanSpace ℂ (Fin k))).map L with hμ'def
  have hH : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map _
  have hμ' : μ' = Measure.addHaarScalarFactor μ' volume • volume := Measure.isAddLeftInvariant_eq_smul μ' volume
  have hc0 : 0 < Measure.addHaarScalarFactor μ' volume :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume
  set c := Measure.addHaarScalarFactor μ' volume with hcdef
  clear_value c
  refine ⟨(1 / 2) * (c : ℝ≥0∞), ?_, ?_, fun E hE => ?_⟩
  · exact mul_ne_zero (by simp) (by exact_mod_cast hc0.ne')
  · exact ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  have hF : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
    hf.comp (continuous_hq k T').measurable
  rw [← lintegral_indicator_one hE, ← hypMeas_eq k T' hf]
  unfold hypMeas hqI
  rw [mul_assoc]
  congr 1
  have e1 : ∀ (y : EuclideanSpace ℂ (Fin k)) (θ : ℝ),
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
        ((fun i => y i), (Real.sqrt (‖y‖ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I)) =
      E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' (L y) θ) := by
    intro y θ
    rw [← normSq_sum_eq]
    rfl
  simp_rw [e1]
  have hG : Measurable (fun y : Fin k → ℂ =>
      ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    hF.lintegral_prod_right'
  set G : (Fin k → ℂ) → ℝ≥0∞ := fun y =>
    ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ) with hGdef
  have eM : (∫⁻ y : EuclideanSpace ℂ (Fin k), G (L y)) = ∫⁻ y, G y ∂μ' :=
    (lintegral_map hG L.continuous.measurable).symm
  rw [eM, hμ', lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [hGdef]
  dsimp only
  rw [lintegral_lintegral_swap hF.aemeasurable]
  exact lint_shift _ hF.lintegral_prod_left' fun θ => by simp only [hq_periodic]

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix ComplexConjugate
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem hpk_mulVec_gen (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = HU.sgn k r i * v (HU.tau k r i) := hpk_mulVec_apply v i

theorem herm_bvec (u : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) u (bvec i) = (Hpk k r *ᵥ u) i := by
  unfold herm bvec
  have : star (Pi.single i (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single i (1 : ℂ) := by
    funext j; simp [Pi.single_apply]
  rw [this, single_dotProduct, one_mul]

theorem herm_pres {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (p *ᵥ u) (p *ᵥ v) = herm (Hpk k r) u v := by
  rw [herm_mulVec_right hp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (HU.isUnit_of_uh hp), Matrix.one_mulVec]

theorem uwb_emb {p : Mat k r} (hp : p ∈ UWb k r) :
    p = embWb k r (fun i j => p (wI k r i) (wI k r j)) := by
  ext i j
  by_cases hj : j.val < r ∨ r + k < j.val
  ·
    have hcol : p *ᵥ bvec j = bvec j := by
      rcases hj with hj | hj
      · have := (hp.2 ⟨j.val, hj⟩).1
        have e : eI k r ⟨j.val, hj⟩ = j := Fin.ext rfl
        rwa [e] at this
      · have := (hp.2 ⟨2 * r + k - j.val, by omega⟩).2
        have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rwa [e] at this
    have h1 := congrFun hcol i
    rw [MB.mulVec_bvec, MB.bvec_apply] at h1
    rw [h1]
    unfold embWb
    rw [dite_eq_right (by omega)]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos ⟨rfl, by omega⟩]
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  · push Not at hj
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (k + 1), wI k r j' = j :=
      ⟨⟨j.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
    by_cases hi : i.val < r ∨ r + k < i.val
    ·
      have hw : (p *ᵥ bvec (wI k r j')) i = 0 := by
        rcases hi with hi | hi
        ·
          set a : Fin r := ⟨i.val, hi⟩
          have hfix := (hp.2 a).2
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (esI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (esI k r a) = i := by
            unfold HU.tau esI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (esI k r a) = 1 := by
            unfold HU.sgn esI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
        · set a : Fin r := ⟨2 * r + k - i.val, by omega⟩
          have hfix := (hp.2 a).1
          have h1 := herm_pres hp.1 (bvec (wI k r j')) (bvec (eI k r a))
          rw [hfix, herm_bvec, herm_bvec, hpk_mulVec_gen, hpk_mulVec_gen] at h1
          have ht : HU.tau k r (eI k r a) = i := by
            unfold HU.tau eI; apply Fin.ext; simp only [a]; split_ifs <;> omega
          have hs : HU.sgn k r (eI k r a) = 1 := by
            unfold HU.sgn eI; simp only [a]; rw [if_neg (by omega)]
          rw [ht, hs, one_mul, one_mul, MB.bvec_apply, if_neg] at h1
          · exact h1
          · intro h; have := congrArg Fin.val h; simp only [wI] at this; omega
      rw [MB.mulVec_bvec] at hw
      rw [hw]
      unfold embWb
      rw [dite_eq_right (by omega), if_neg (fun h => by have := congrArg Fin.val h.1; simp only [wI] at this; omega)]
    · push Not at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (k + 1), wI k r i' = i :=
        ⟨⟨i.val - r, by omega⟩, by apply Fin.ext; simp only [wI]; omega⟩
      have := embWb_wI (k := k) (r := r) (fun i j => p (wI k r i) (wI k r j)) i' j'
      exact this.symm

theorem col_unitary (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hμ : μᴴ * Hb k * μ = Hb k) (l : ℂ)
    (hl : conj l * l = 1) (hcol : ∀ i, μ i (Fin.last k) = if i = Fin.last k then l else 0) : μᴴ * μ = 1 := by
  have hl0 : conj l ≠ 0 := by intro h; rw [h, zero_mul] at hl; exact zero_ne_one hl
  have hrow : ∀ j, j ≠ Fin.last k → μ (Fin.last k) j = 0 := by
    intro j hj
    have h := congrFun (congrFun hμ (Fin.last k)) j
    rw [form_apply] at h
    simp only [hcol, Fin.castSucc_ne_last, if_false, map_zero, zero_mul, Finset.sum_const_zero, if_true,
      zero_sub, Hb, Matrix.diagonal_apply_ne _ (Ne.symm hj)] at h
    have : conj l * μ (Fin.last k) j = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left hl0
  have key : ∀ i j, (μᴴ * μ) i j = Hb k i j + 2 * (conj (μ (Fin.last k) i) * μ (Fin.last k) j) := by
    intro i j
    have h := congrFun (congrFun hμ i) j
    rw [form_apply] at h
    rw [← h, Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [Matrix.conjTranspose_apply, Complex.star_def]
    ring
  ext i j
  rw [key]
  by_cases hi : i = Fin.last k
  · by_cases hj : j = Fin.last k
    · subst hi; subst hj
      rw [hcol, if_pos rfl, hl]
      simp [Hb]; norm_num
    · rw [hrow j hj, mul_zero, mul_zero, add_zero, Hb, Matrix.diagonal_apply_ne _ (fun h => hj (h.symm.trans hi)),
        Matrix.one_apply_ne (fun h => hj (h.symm.trans hi))]
  · rw [hrow i hi, map_zero, zero_mul, mul_zero, add_zero, Hb, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; exact hi (h1 ▸ h2))

theorem boost_herm (y : Fin k → ℂ) (n : ℝ) (hn : 0 < n) : (boost y (n : ℂ))ᴴ = boost y (n : ℂ) := by
  have hnn : ‖(n : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  ext i j
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [boost]
    | cast j => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [boost, hnn, hn0, abs_of_pos hn, div_self hn0]
    | cast j =>
      simp only [boost, Fin.lastCases_castSucc, hnn, map_add (f := _), map_div₀, map_mul, Complex.conj_conj,
        Complex.conj_ofReal, map_one]
      by_cases h : i = j
      · subst h; simp; ring
      · rw [if_neg (Ne.symm h), if_neg h]; simp; ring

theorem polarDecW : PolarDecW := by
  intro k r p hp
  set μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j => p (wI k r i) (wI k r j) with hμdef
  have hpμ : p = embWb k r μ := uwb_emb hp
  have hμ : μᴴ * Hb k * μ = Hb k := (MB.emb_mem μ).1 (hpμ ▸ hp.1)
  set y : Fin k → ℂ := fun l => μ l.castSucc (Fin.last k) with hy
  set c : ℂ := μ (Fin.last k) (Fin.last k) with hc
  have hform := congrFun (congrFun hμ (Fin.last k)) (Fin.last k)
  rw [form_apply] at hform
  have hS0 : ∑ l, conj (y l) * y l = conj c * c - 1 := by
    simp only [Hb, Matrix.diagonal_apply_eq, if_true] at hform
    simp only [hy, hc]; linear_combination hform
  have hA : ∑ l, conj (y l) * y l = ((∑ l, Complex.normSq (y l) : ℝ) : ℂ) := by
    push_cast [Complex.normSq_eq_conj_mul_self]; rfl
  have hA0 : 0 ≤ ∑ l, Complex.normSq (y l) := Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  have hcc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul, zero_sub, hA] at hS0
    have := congrArg Complex.re hS0
    simp at this; linarith
  set n : ℝ := ‖c‖ with hn
  have hnpos : 0 < n := norm_pos_iff.2 hc0
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hnpos.ne'
  set y' : Fin k → ℂ := fun l => y l * ((n : ℂ) / c) with hy'
  have hnn : ‖((n : ℝ) : ℂ)‖ = n := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  have hS' : ∑ l, conj (y' l) * y' l = ((‖((n : ℝ) : ℂ)‖ : ℝ) : ℂ) ^ 2 - 1 := by
    have e : ∀ l, conj (y' l) * y' l = conj (y l) * y l * (((n : ℂ) ^ 2) / (conj c * c)) := by
      intro l; simp only [hy', map_mul, map_div₀, Complex.conj_ofReal]; field_simp
    simp only [e, ← Finset.sum_mul, hS0, hcc, hnn]
    field_simp
  set B₀ := boost y' (n : ℂ) with hB₀
  have hB : B₀ᴴ * Hb k * B₀ = Hb k := boost_mem y' (n : ℂ) hS' hn0
  have hBh : B₀ᴴ = B₀ := boost_herm y' n hnpos
  have hHbh : (Hb k)ᴴ = Hb k := MB.Hb_conjT
  set Bi := Hb k * B₀ᴴ * Hb k with hBi
  have hBiB : Bi * B₀ = 1 := by
    calc Bi * B₀ = Hb k * (B₀ᴴ * Hb k * B₀) := by simp only [hBi, Matrix.mul_assoc]
      _ = 1 := by rw [hB, hb_sq]
  have hBBi : B₀ * Bi = 1 := mul_eq_one_comm.mp hBiB
  have hBHB : B₀ * Hb k * B₀ᴴ = Hb k := by
    have : B₀ * Hb k * B₀ᴴ * Hb k = 1 := by rw [← hBBi, hBi]; simp only [Matrix.mul_assoc]
    calc B₀ * Hb k * B₀ᴴ = B₀ * Hb k * B₀ᴴ * Hb k * Hb k := by rw [Matrix.mul_assoc (B₀ * Hb k * B₀ᴴ) (Hb k) (Hb k), hb_sq, Matrix.mul_one]
      _ = Hb k := by rw [this, Matrix.one_mul]
  set μq := Bi * μ with hμq
  have hμqU : μqᴴ * Hb k * μq = Hb k := by
    have hBi' : Biᴴ * Hb k * Bi = Hb k := by
      simp only [hBi, Matrix.conjTranspose_mul, hHbh, conjTranspose_conjTranspose]
      calc Hb k * (B₀ * Hb k) * Hb k * (Hb k * B₀ᴴ * Hb k) = Hb k * (B₀ * (Hb k * Hb k) * Hb k * B₀ᴴ) * Hb k := by
            simp only [Matrix.mul_assoc]
        _ = Hb k := by rw [hb_sq, Matrix.mul_one, hBHB, hb_sq, Matrix.one_mul]
    calc μqᴴ * Hb k * μq = μᴴ * (Biᴴ * Hb k * Bi) * μ := by
          simp only [hμq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hb k := by rw [hBi', hμ]
  set e : ℂ := c / n with he
  have hucol : ∀ l, μ l (Fin.last k) = e * B₀ l (Fin.last k) := by
    intro l
    induction l using Fin.lastCases with
    | last => simp only [hB₀, boost, Fin.lastCases_last, he, hc]; field_simp
    | cast j => simp only [hB₀, boost, Fin.lastCases_last, Fin.lastCases_castSucc, he, hy', hy]; field_simp
  have hcol : ∀ i, μq i (Fin.last k) = if i = Fin.last k then e else 0 := by
    intro i
    have : μq i (Fin.last k) = e * (Bi * B₀) i (Fin.last k) := by
      simp only [hμq, Matrix.mul_apply, hucol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [this, hBiB, Matrix.one_apply]
    split_ifs <;> simp
  have he1 : conj e * e = 1 := by
    simp only [he, map_div₀, Complex.conj_ofReal]
    rw [div_mul_div_comm, hcc]
    field_simp
  have hqu := col_unitary μq hμqU e he1 hcol
  refine ⟨B₀, hB, hBh, embWb k r μq, MB.emb_mem_UWb hμqU, ?_, ?_⟩
  · rw [MB.emb_conjT, ← MB.emb_mul, hqu, MB.emb_one]
  · rw [← MB.emb_mul, hμq, ← Matrix.mul_assoc, hBBi, Matrix.one_mul, ← hpμ]

theorem unimodW : UnimodW := unimodW_of_two ballConj polarDecW

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvOA
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def GhatF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (ζ : ℂ) : ℝ≥0∞ :=
  Gf μW F (embWb k r (secP k r z z' μsec ζ) *ᵥ z')

theorem section_vector_properties (hd : WbData k r z z' μW μW' a a' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  refine ⟨inWb_emb _ hd.z'_mem, herm_both _ _ (MB.emb_mem_UWb (hd.sec.2 ζ hζ).1).1 z' z', ?_⟩
  rw [_root_.PI.RhsWLim.W.ZetaZeros.herm_emb _ hd.z_mem hd.z'_mem]
  exact (hd.sec.2 ζ hζ).2

theorem meas_Ghat (hd : WbData k r z z' μW μW' a a' μsec) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (GhatF k r z z' μW μsec F) := by
  have := hd.haarW.1
  have hc : Continuous (fun m : Fin (k + 1) → Fin (k + 1) → ℂ => embWb k r (Matrix.of m) *ᵥ z') :=
    (cont_emb.comp continuous_id).matrix_mulVec continuous_const
  exact (meas_Gf hF).comp (hc.measurable.comp (meas_secP hd.sec))

theorem orbInv_of (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : OrbInv := by
  intro k r z z' μW μW' a a' μsec hd s hs F hF
  have := hd.haarW.1
  have := hd.haarW'.1
  obtain ⟨Q, hσQ, hQi, hQc, c, hc0, hcT, hpol⟩ := hQ k r z z' hd.k_pos hd.z_mem hd.z'_mem hd.T_pos hd.T'_pos
  have hfinW : μW Set.univ ≠ ⊤ := by rw [hd.massW]; exact ENNReal.ofReal_ne_top
  have hnull : Q {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} = 0 := by
    have hS : MeasurableSet {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'} :=
      measurableSet_le Complex.continuous_normSq.measurable measurable_const
    have h1 := hpol ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator 1) (measurable_one.indicator hS)
    have e : (fun v => ({ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞))
        (herm (Hpk k r) v z)) = ({v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'}).indicator 1 :=
      funext fun v => rfl
    have hmS : MeasurableSet {v | Complex.normSq (herm (Hpk k r) v z) ≤ Tz k r z * Tz k r z'} :=
      (cont_herm z).measurable hS
    rw [e, lintegral_indicator_one hmS] at h1
    rw [h1]
    have h2 : (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ) =ᵐ[volume] 0 := by
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      show ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        {ζ : ℂ | Complex.normSq ζ ≤ Tz k r z * Tz k r z'}.indicator (1 : ℂ → ℝ≥0∞) ζ = 0
      by_cases h : Complex.normSq ζ ≤ Tz k r z * Tz k r z'
      · have hlt : Complex.normSq ζ < Tz k r z * Tz k r z' := lt_of_le_of_ne h hζ
        have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 hlt)]
        rw [h0, ENNReal.ofReal_zero, zero_mul]
      · simp only [Set.indicator, Set.mem_ofPred_eq, h, if_false, mul_zero]
    rw [lintegral_congr_ae h2, Pi.zero_def, lintegral_zero, mul_zero]
  have key : ∀ F' : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F' →
      c * rhsW k r z z' μW μW' μsec (fun x => F' (orbV k r z' x)) =
        ENNReal.ofReal a' * (ENNReal.ofReal a * ∫⁻ v, F' v ∂Q) := by
    intro F' hF'
    have sA : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F' (embWb k r (μsec ζ) *ᵥ z') =
        ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * GhatF k r z z' μW μsec F' ζ := by
      refine lintegral_congr_ae ?_
      filter_upwards [circle_ae (Tz k r z * Tz k r z')] with ζ hζ
      by_cases h : Tz k r z * Tz k r z' < Complex.normSq ζ
      · unfold GhatF
        rw [secP_eq h]
      · have h0 : zWeight k (Tz k r z) (Tz k r z') ζ = 0 := by
          unfold zWeight
          rw [if_neg (not_le.2 (lt_of_le_of_ne (not_lt.1 h) hζ))]
        rw [h0, ENNReal.ofReal_zero, zero_mul, zero_mul]
    have sB : ∫⁻ v, GhatF k r z z' μW μsec F' (herm (Hpk k r) v z) ∂Q = ∫⁻ v, Gf μW F' v ∂Q := by
      refine lintegral_congr_ae ?_
      have hg1 : ∀ᵐ v ∂Q, inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z' := by
        rw [ae_iff]
        exact hQc
      have hg2 : ∀ᵐ v ∂Q, Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) v z) := by
        rw [ae_iff]
        exact measure_mono_null (fun v (hv : ¬ (Tz k r z * Tz k r z' < _)) => not_lt.1 hv) hnull
      filter_upwards [hg1, hg2] with v hv1 hv2
      obtain ⟨p1, p2, p3⟩ := section_vector_properties hd hv2
      unfold GhatF
      rw [secP_eq hv2]
      exact Gf_fib hU hT hd.haarW hfinW hd.z_mem hd.T_pos hF' p1 hv1.1 (p2.trans hv1.2.symm) p3
    rw [rhs_orb hd F', sA, ← hd.massW, ← avg_Q Q hQi hd.haarW hF', ← sB, hpol _ (meas_Ghat hd hF')]
    ring
  have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => s *ᵥ v) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have k1 := key (fun v => F (s *ᵥ v)) (hF.comp hmv)
  have k2 := key F hF
  have eQ : ∫⁻ v, F (s *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    rw [← lintegral_map hF hmv, hQi s hs]
  rw [eQ, ← k2] at k1
  exact (ENNReal.mul_right_inj hc0 hcT).1 k1

theorem rhsWInv_of_hyp (hQ : HypQ) (hU : UnimodK) (hT : FibTrans) : RhsWInv :=
  rhsWInv_of_orb (orbInv_of hQ hU hT)

end PI.RhsWLim.W.RI
end
end

