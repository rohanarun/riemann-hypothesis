module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.ClosingHS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertSamuelProjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem secM_mul_mem (y : (Σ k, ι k) → Ω) {d e : K → ℕ} {s t : Ω} (hs : s ∈ secM y d)
    (ht : t ∈ secM y e) : s * t ∈ secM y (d + e) := by
  have hgen : ∀ g : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → aeval y g * t ∈ secM y (d + e) := by
    intro g hg
    change t ∈ Submodule.span ℤ _ at ht
    change _ ∈ Submodule.span ℤ _
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  change s ∈ Submodule.span ℤ _ at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hgen g hg
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul n x _ hx => rw [smul_mul_assoc]; exact zsmul_mem hx n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

lemma mem_source_chartIdx (A : FinHolAtlas D X) (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

lemma target_inter_symm_source (A : FinHolAtlas D X) (j : Fin A.n) :
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
  inter_eq_left.2 fun _ hy => (A.chart j).map_target hy

theorem LocalBergmanBound.proof (hC : ChartBergmanBound.Statement) :
    LocalBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV x ε hε
  have := dV.isProb
  set k := chartIdx A x with hk
  set e := A.chart k with he
  have hx : x ∈ e.source := mem_source_chartIdx A x
  have hy0 : e x ∈ e.target := e.map_source hx
  have hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target := by
    have := W.smooth k k
    rwa [target_inter_symm_source] at this
  have hmain := hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0
    (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0)
    (fun w => hW k (e x) hy0 w) ε hε
  have hb : bergmanDens W dV x =
      (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x) := by
    have hD : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
    exact mul_div_mul_left _ _ hD
  filter_upwards [hmain] with n hn
  rw [← hb] at hn
  set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK

  have hKpos : 0 < K := by
    by_contra hle
    have h1 := hn (fun _ => 1) analyticOnNhd_const
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h1
    have : 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) := by
      simp [Real.exp_pos]
    linarith
  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV n s.2
  have hcont := continuous_ptNormSq W hs
  have hnn : ∀ z, 0 ≤ ptNormSq W n s z := ptNormSq_nonneg W n s
  have hint : Integrable (ptNormSq W n s) dV.μ := integrable_ptNormSq W dV hs
  have hl2 : 0 ≤ sectionL2NormSq W dV n s := sectionL2NormSq_nonneg W dV n s

  have hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target := by
    have := hs.1 k k
    rwa [target_inter_symm_source] at this
  have h1 := hn _ hF
  have hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x := by
    simp only [Function.comp, e.left_inv hx]
    rfl
  have hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤
        ENNReal.ofReal (sectionL2NormSq W dV n s) := by
    have hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z) :=
      hcont.measurable.ennreal_ofReal
    calc _ = ∫⁻ y in e.target, ENNReal.ofReal (ptNormSq W n s (e.symm y)) *
          ENNReal.ofReal (dV.dens k y) := by
          refine setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]
          rfl
      _ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ :=
          (dV.chart_lintegral k _ hmeas).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sectionL2NormSq W dV n s) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
  rw [hleft] at h1
  have h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s) := by
    rw [ENNReal.ofReal_mul hKpos.le]
    exact h1.trans (by gcongr)
  have h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2
  rcases hl2.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hKpos.le
  · exact (div_le_iff₀ hpos).2 h3

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k


omit [Fintype K] in
theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp


omit [Fintype K] in
theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction e k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ m ihm =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul ihm (isMultiHomog_X k (c k))
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem MetricMaxComparison.proof : MetricMaxComparison.Statement := by
  intro K _ ι _ A hA

  let blk : (k : K) → ((Σ k, ι k) → ℂ) → (ι k → ℂ) := fun k z i => z ⟨k, i⟩
  have hblkc : ∀ k, Continuous (blk k) := fun k => continuous_pi fun i => continuous_apply _
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖blk k z‖ = 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hS : S = ⋂ k, (fun z => ‖blk k z‖) ⁻¹' {1} := by ext z; simp [S]
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage (hblkc k).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖blk p.1 z p.2‖ := rfl
        _ ≤ ‖blk p.1 z‖ := norm_le_pi_norm _ _
        _ = 1 := hz p.1
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : blk k z = 0 := funext h
    have h1 : ‖blk k z‖ = 1 := hz k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C0, hC0⟩ := hSc.exists_bound_of_continuousOn (hA.continuousOn.mono hSU)
  refine ⟨max C0 1, le_max_right _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖blk k z‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact norm_pos_iff.mpr fun h0 => hi (congrFun h0 i)
  let c : K → ℂ := fun k => ((‖blk k z‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖blk k z‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwS : (fun p : Σ k, ι k => c p.1 * z p) ∈ S := fun k => by
    have h1 : blk k (fun p : Σ k, ι k => c p.1 * z p) = c k • blk k z := rfl
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hmax : (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z = ∏ k, ‖blk k z‖ ^ A.a k := rfl
  have hprod : (∏ k, ‖blk k z‖ ^ A.a k) * (∏ k, ‖c k‖ ^ A.a k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcn, ← mul_zpow, mul_inv_cancel₀ (hn k).ne', one_zpow]
  have hz' : A.h z = (∏ k, ‖blk k z‖ ^ A.a k) * A.h (fun p : Σ k, ι k => c p.1 * z p) := by
    rw [A.smul c z hc0, ← mul_assoc, hprod, one_mul]
  have hpos : 0 ≤ ∏ k, ‖blk k z‖ ^ A.a k :=
    Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hbw : A.h (fun p : Σ k, ι k => c p.1 * z p) ≤ max C0 1 := by
    have h1 := hC0 _ hwS
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  rw [hmax, hz', mul_comm (max C0 1)]
  exact mul_le_mul_of_nonneg_left hbw hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionsAsymptotic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

set_option linter.unusedSectionVars false

section Coordinates

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem chartLatQ_eq_smul_one (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLatQ y a τ = chartLatQ y ((τ : ℤ) • a) 1 := by
  ext s
  show (∀ c : ∀ k, ι k, _ → _) ↔ (∀ c : ∀ k, ι k, _ → _)
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]

end Coordinates

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSMBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

