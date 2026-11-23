module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem hb_sq (k : ℕ) : Hb k * Hb k = 1 := by
  rw [Hb, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> norm_num

theorem herm_mulVec_right {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (p *ᵥ u) = herm (Hpk k r) (p⁻¹ *ᵥ v) u := by
  have hu := HU.isUnit_of_uh hp
  have hp' : pᴴ * Hpk k r * p = Hpk k r := hp
  have key : pᴴ * Hpk k r = Hpk k r * p⁻¹ := by
    calc pᴴ * Hpk k r = pᴴ * Hpk k r * (p * p⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (pᴴ * Hpk k r * p) * p⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * p⁻¹ := by rw [hp']
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]

theorem tau_wLast : HU.tau k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
  unfold HU.tau wI
  apply Fin.ext
  simp only [Fin.val_last]
  split_ifs <;> omega

theorem sgn_wLast : HU.sgn k r (wI k r (Fin.last k)) = -1 := by
  unfold HU.sgn wI
  simp

theorem hpk_mulVec_wLast (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (wI k r (Fin.last k)) = -v (wI k r (Fin.last k)) := by
  simp only [Matrix.mulVec, dotProduct, HU.hpk_row, tau_wLast, sgn_wLast, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem herm_wLast (v : Fin (2 * r + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k r) v ((s : ℂ) • wLast k r) = -((s : ℂ) * v (wI k r (Fin.last k))) := by
  have hs : star ((s : ℂ) • wLast k r) = Pi.single (wI k r (Fin.last k)) (s : ℂ) := by
    funext j
    simp only [wLast, bvec, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  unfold herm
  rw [hs, single_dotProduct, hpk_mulVec_wLast, mul_neg]

theorem pairF_std (z' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) (x : Mt k r) :
    pairF k r ((s : ℂ) • wLast k r) z' x = -((s : ℂ) * (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) :=
  herm_wLast _ _

theorem rmulM_cont (p : Mat k r) : Continuous (rmulM p : Mt k r → Mt k r) := by
  unfold rmulM
  exact (continuous_id (X := Mat k r)).matrix_mul continuous_const

theorem continuous_coords (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => ((fun i : Fin k => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i))),
      (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) := by
  have hc : Continuous fun x : Mt k r => Matrix.of x *ᵥ z' :=
    Continuous.matrix_mulVec (continuous_id (X := Mat k r)) continuous_const
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem orbitPushG_of (hO : OrbitPush) (hT : TransW) (hU : UnimodW) : OrbitPushG := by
  intro k r z' hk hz' hT' νg hG f hf
  obtain ⟨p, hp, hpz⟩ := hT k r z' hz' hT'
  set zs := ((Real.sqrt (Tz k r z') : ℂ) • wLast k r) with hzs
  have hFm := hf.comp (continuous_coords (k := k) (r := r) zs).measurable
  have e : ∀ x : Mt k r, Matrix.of x *ᵥ z' = Matrix.of (rmulM p x) *ᵥ zs := by
    intro x
    rw [← hpz]
    show Matrix.of x *ᵥ (p *ᵥ zs) = (Matrix.of x * p) *ᵥ zs
    rw [Matrix.mulVec_mulVec]
  calc ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg
      = ∫⁻ x, (fun y : Mt k r => f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k)))) (rmulM p x) ∂νg := by
        refine lintegral_congr fun x => ?_
        simp only [e x]
    _ = ∫⁻ y, f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k))) ∂(νg.map (rmulM p)) :=
        (lintegral_map hFm (rmulM_cont p).measurable).symm
    _ = _ := by
        rw [hU k r νg hk hG p hp]
        exact hO k r (Tz k r z') hk hT' νg hG f hf

theorem pairPush_of (hT : TransW) (hO : OrbitPushG) (h4 : PolarHyp) (h5 : VolURatio) : PairPush := by
  intro k r νg hk hG z z' hz hz' hTz hTz' g hg
  obtain ⟨p, hp, hpz⟩ := hT k r z hz hTz
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hTz).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs

  have e1 : ∀ x : Mt k r, pairF k r z z' x = pairF k r zs z' (lmulM p⁻¹ x) := by
    intro x
    unfold pairF
    rw [← hpz, herm_mulVec_right hp.1, Matrix.mulVec_mulVec]
    rfl
  have hgm : Measurable fun y : Mt k r => g (pairF k r zs z' y) := hg.comp (continuous_pairF k r zs z').measurable
  have hpinv := HU.uwb_inv hp
  have step1 : ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ y, g (pairF k r zs z' y) ∂νg := by
    calc ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ x, (fun y => g (pairF k r zs z' y)) (lmulM p⁻¹ x) ∂νg := by
          refine lintegral_congr fun x => ?_
          simp only [e1 x]
      _ = ∫⁻ y, g (pairF k r zs z' y) ∂(νg.map (lmulM p⁻¹)) :=
          (lintegral_map hgm (HU.lmulM_cont _).measurable).symm
      _ = _ := by rw [hG.1.2.2.2 _ hpinv]

  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 := hO k r z' hk hz' hTz' νg hG f hfm

  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := h4 k (Tz k r z) (Tz k r z') hk hTz hTz' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  rw [step1]
  have e2 : ∫⁻ y, g (pairF k r zs z' y) ∂νg = ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg := by
    refine lintegral_congr fun x => ?_
    rw [pairF_std]
  rw [e2, step2]
  have e3 : hypMeas k (Tz k r z') f =
      hypMeas k (Tz k r z') (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [e3, step3]
  simp only [hGdef, hcancel]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := volU_pos k; positivity)]
  congr 2
  have hV := h5 k hk
  have h1 := volU_pos (k - 1)
  have h2 : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
  have h3 := Real.pi_pos
  have h4 : Tz k r z ≠ 0 := hTz.ne'
  have h5 : Tz k r z' ≠ 0 := hTz'.ne'
  unfold pairConst
  rw [hV]
  field_simp
  ring

theorem constVal_of_polarHyp (hR : RhsTest) (hT : TransW) (hU : UnimodW) (hO : OrbitPush) (h4 : PolarHyp) :
    ConstVal :=
  constVal_of hR (pairPush_of hT (orbitPushG_of hO hT hU) h4 volURatio)

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
section
@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def psiE (k r : ℕ) (T' : ℝ) (q : TrE k) : (Fin k → ℂ) × ℂ :=
  opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')

def kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) : TrE k :=
  (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => match o with
    | none => Complex.arg v.2
    | some (a, b) => if b then (v.1 a).im else (v.1 a).re)

def phiT (k r : ℕ) (T' : ℝ) (q : TrE k) : TrE k := kapT k (psiE k r T' q)

def HypChart : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
    hypM k T' (opE k r T' ρ) = (1 / 2) * volume (phiT k r T' '' Metric.ball 0 ρ)

def PhiDiff : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    ContDiffAt ℝ 1 (phiT k r T') 0 ∧ (fderiv ℝ (phiT k r T') 0).det = (T' / 2) ^ k

theorem hypLocal_of (hJ : ChartJac) (hC : HypChart) (hD : PhiDiff) : HypLocal := by
  intro k r T' hk hT
  obtain ⟨hcd, hdet⟩ := hD k r T' hk hT
  obtain ⟨ε, hε, hV⟩ := hC k r T' hk hT
  have hdet0 : (fderiv ℝ (phiT k r T') 0).det ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by positivity)
  have hlim := hJ (TrE k) (phiT k r T') volume (fun _ => 1) hcd hdet0
    continuousAt_const ENNReal.one_ne_top ⟨Set.univ, Filter.univ_mem, fun A _ _ => by simp⟩
  have key := hlim.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((1 : ℝ≥0∞).toReal * |(fderiv ℝ (phiT k r T') 0).det|) =
      T' ^ k / 2 ^ (k + 1) := by
    rw [hdet, ENNReal.toReal_one, one_mul, abs_of_pos (by positivity), div_pow, pow_succ]
    field_simp
    try ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with ρ hρ0 hρε
  rw [hV ρ hρ0 hρε, tVol, ENNReal.toReal_mul, mul_div_assoc]
  congr 1
  simp

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def orbV (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : Fin (2 * r + k + 1) → ℂ := Matrix.of x *ᵥ z'

def rmulM (b : Mat k r) (x : Mt k r) : Mt k r := fun i j => (Matrix.of x * b) i j

def DescUniq : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (μW' : Measure (Mt k r)), IsHaarOn (UWset k r z') μW' →
    μW' Set.univ ≠ ⊤ → ∀ ν₁ ν₂ : Measure (Mt k r), SigmaFinite ν₁ → SigmaFinite ν₂ →
    ν₁ {x | Matrix.of x ∉ UWb k r} = 0 → ν₂ {x | Matrix.of x ∉ UWb k r} = 0 →
    (∀ b ∈ UWset k r z', ν₁.map (rmulM b) = ν₁) → (∀ b ∈ UWset k r z', ν₂.map (rmulM b) = ν₂) →
    ν₁.map (orbV k r z') = ν₂.map (orbV k r z') → ν₁ = ν₂

def RInvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ b ∈ UWset k r z',
      (nuR k r z z' μW μW' μsec).map (rmulM b) = nuR k r z z' μW μW' μsec

def OrbInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F →
      rhsW k r z z' μW μW' μsec (fun x => F (s *ᵥ orbV k r z' x)) =
        rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x))

theorem orbV_cont (z' : Fin (2 * r + k + 1) → ℂ) : Continuous (orbV k r z') := by
  unfold orbV
  exact Continuous.matrix_mulVec (continuous_id' (X := Mt k r)) continuous_const

theorem rmulM_cont (b : Mat k r) : Continuous (rmulM b : Mt k r → Mt k r) := by
  unfold rmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (Continuous.matrix_mul (continuous_id' (X := Mt k r)) continuous_const).matrix_elem i j

def lmulE (s : Mat k r) (hs : IsUnit s.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM s
  invFun := lmulM s⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left (A := s) (Matrix.of x) hs
  right_inv x := Matrix.mul_nonsing_inv_cancel_left (A := s) (Matrix.of x) hs
  measurable_toFun := (HU.lmulM_cont s).measurable
  measurable_invFun := (HU.lmulM_cont s⁻¹).measurable

theorem nu_conc (hD : WbData k r z z' μW μW' a a' μsec) :
    nuR k r z z' μW μW' μsec {x | Matrix.of x ∉ UWb k r} = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  apply measure_mono_null _ (src_null hD)
  intro q hq hg
  exact hq (mem_chart hD hg)

theorem rhsWInv_of (hD : DescUniq) (hR : RInvNu) (hO : OrbInv) : RhsWInv := by
  intro k r z z' μW μW' a a' μsec hd s hs φ hφ
  have := hd.haarW.1
  have := hd.haarW'.1
  have hσ : SigmaFinite (nuR k r z z' μW μW' μsec) := nu_sigmaFinite hd
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  have hσ1 : SigmaFinite ((nuR k r z z' μW μW' μsec).map (lmulM s)) :=
    (lmulE s (HU.uwb_unit hs)).sigmaFinite_map
  have hC1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)) {x | Matrix.of x ∉ UWb k r} = 0 := by
    rw [Measure.map_apply hl (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
      HU.amb_closed.isOpen_compl.measurableSet]
    apply measure_mono_null _ (nu_conc hd)
    intro x hx hx'
    exact hx (HU.uwb_mul hs hx')
  have hR1 : ∀ b ∈ UWset k r z', ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (rmulM b) =
      (nuR k r z z' μW μW' μsec).map (lmulM s) := by
    intro b hb
    have hr : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
    have e : rmulM b ∘ lmulM s = lmulM s ∘ rmulM b := by
      funext x
      show (s * Matrix.of x * b : Mat k r) = s * (Matrix.of x * b)
      exact Matrix.mul_assoc _ _ _
    rw [Measure.map_map hr hl, e, ← Measure.map_map hl hr, hR k r z z' μW μW' a a' μsec hd b hb]
  have hO1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (orbV k r z') =
      (nuR k r z z' μW μW' μsec).map (orbV k r z') := by
    have ho : Measurable (orbV k r z') := (orbV_cont z').measurable
    ext A hA
    rw [Measure.map_map ho hl, Measure.map_apply (ho.comp hl) hA, Measure.map_apply ho hA,
      ← lintegral_indicator_one ((ho.comp hl) hA), ← lintegral_indicator_one (ho hA)]
    have e1 : ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) =
        fun x => A.indicator 1 (s *ᵥ orbV k r z' x) := by
      funext x
      show ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator 1 x = A.indicator 1 (s *ᵥ (Matrix.of x *ᵥ z'))
      rw [Matrix.mulVec_mulVec]
      rfl
    have e2 : (orbV k r z' ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (orbV k r z' x) := by
      funext x
      rfl
    have hF : Measurable (A.indicator (1 : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞)) := measurable_one.indicator hA
    rw [e1, e2, ← repr hd (fun x => A.indicator 1 (s *ᵥ orbV k r z' x))
        (hF.comp ((continuous_const.matrix_mulVec continuous_id).measurable.comp ho)),
      ← repr hd (fun x => A.indicator 1 (orbV k r z' x)) (hF.comp ho), hO k r z z' μW μW' a a' μsec hd s hs _ hF]
  have key := hD k r z' μW' hd.haarW' (by rw [hd.massW']; exact ENNReal.ofReal_ne_top) _ _ hσ1 hσ hC1
    (nu_conc hd) hR1 (hR k r z z' μW μW' a a' μsec hd) hO1
  rw [repr hd (fun x => φ (lmulM s x)) (hφ.comp hl), repr hd _ hφ, ← lintegral_map hφ hl, key]

end PI.RhsWLim.W.RI
end
end

