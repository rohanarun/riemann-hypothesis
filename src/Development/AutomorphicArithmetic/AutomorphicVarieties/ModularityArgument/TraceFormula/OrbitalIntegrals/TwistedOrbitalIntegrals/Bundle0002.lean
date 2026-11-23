module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotFubini
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc hiding twCent

theorem UpperTheory.V.Z.Tf.Orb.quotFubini :
    UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotFubini := by
  intro hM G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv F hF hFH hsupp
  obtain ⟨Y, C, hY, hC, hsupp⟩ := hsupp
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  swap
  · simp only [quotIntegral, dif_neg hex, integral_zero]
  simp only [quotIntegral, dif_pos hex]
  have hρ := hex.choose_spec
  generalize hex.choose = ρ at hρ ⊢
  obtain ⟨hS, hfin⟩ := (hM G μG hμG H hH μ hμ hinv ρ hρ).2 C hC
  set S : Set G := {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} with hSdef
  obtain ⟨M, hMb⟩ := (hY.prod hC).exists_bound_of_continuousOn hF.continuousOn
  have h1 : Integrable (S.indicator fun g => (ρ g).toReal) μG := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact integrable_toReal_of_lintegral_ne_top hρ.1.aemeasurable hfin
  have h2 : Integrable (Y.indicator fun _ => M) μG := by
    rw [integrable_indicator_iff hY.isClosed.measurableSet]
    exact integrableOn_const hY.measure_lt_top.ne
  have hint : Integrable (Function.uncurry fun g y => F y g * ((ρ g).toReal : ℂ)) (μG.prod μG) := by
    refine (h1.mul_prod h2).mono' ?_ (Filter.Eventually.of_forall ?_)
    · have a1 : Measurable fun p : G × G => F p.2 p.1 :=
        (hF.comp continuous_swap).measurable
      have a2 : Measurable fun p : G × G => ((ρ p.1).toReal : ℂ) :=
        Complex.measurable_ofReal.comp ((hρ.1.comp measurable_fst).ennreal_toReal)
      exact (a1.mul a2).aestronglyMeasurable
    · rintro ⟨g, y⟩
      show ‖F y g * ((ρ g).toReal : ℂ)‖ ≤ S.indicator (fun g => (ρ g).toReal) g * Y.indicator (fun _ => M) y
      by_cases h0 : F y g = 0
      · rw [h0, zero_mul, norm_zero]
        by_cases hg : g ∈ S
        · by_cases hy : y ∈ Y
          · obtain ⟨h, -, c, hc, -⟩ := hg
            have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMb (y, c) ⟨hy, hc⟩)
            exact mul_nonneg (Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _)
              (Set.indicator_nonneg (fun _ _ => hM0) _)
          · rw [Set.indicator_of_notMem hy, mul_zero]
        · rw [Set.indicator_of_notMem hg, zero_mul]
      · obtain ⟨hy, hg⟩ := hsupp y g h0
        have hg' : g ∈ S := hg
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hg', norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_comm]
        obtain ⟨h, hh, c, hc, rfl⟩ := hg
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [hFH y h hh c]
        exact hMb (y, c) ⟨hy, hc⟩
  rw [← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact (integral_mul_const _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotIndep
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc hiding twCent
open scoped ENNReal

section Core

variable {G T : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [Group T] [MeasurableSpace T] [MeasurableInv T]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {ν : Measure T} [SFinite ν] {j : T →* G}

omit [MeasurableInv G] [MeasurableInv T] in
private theorem ae_fin (hj : Measurable j) {ρ : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) :
    ∀ᵐ g ∂μ, ρ g < ∞ := by
  have hA : MeasurableSet {g | ρ g = ∞} := hm (measurableSet_singleton _)
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have h1 : ∫⁻ g, ∫⁻ t, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂ν ∂μ = 0 := by
    refine (lintegral_congr fun g => ?_).trans lintegral_zero
    have h2 : ∀ᵐ t ∂ν, ρ (j t * g) < ∞ := ae_lt_top (hm.comp (hj.mul_const g)) (by rw [h]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae (h2.mono fun t ht => ?_)).trans lintegral_zero
    exact Set.indicator_of_notMem (s := {g | ρ g = ∞}) ht.ne _
  rw [lintegral_lintegral_swap (f := fun g t => {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g))
    ((measurable_one.indicator hA).comp hmul).aemeasurable] at h1
  have h3 : ∀ t : T, ∫⁻ g, {g | ρ g = ∞}.indicator (1 : G → ℝ≥0∞) (j t * g) ∂μ = μ {g | ρ g = ∞} := fun t => by
    rw [lintegral_mul_left_eq_self, lintegral_indicator_one hA]
  simp only [h3, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · rw [ae_iff]
    simpa using h1
  · have := h 1
    rw [Measure.measure_univ_eq_zero.1 h1] at this
    simp at this

private theorem lint_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫⁻ g, F g * ρ g ∂μ = ∫⁻ g, F g * ρ' g ∂μ := by
  have hmul : Measurable fun p : G × T => j p.2 * p.1 := (hj.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => j p.2⁻¹ * p.1 := (hj.comp measurable_snd.inv).mul measurable_fst
  have a : ∀ g, F g * ρ g = ∫⁻ t, F g * ρ g * ρ' (j t * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ' (j t * g)) (hm'.comp (hj.mul_const g)), h', mul_one]
  have b : ∀ g, F g * ρ' g = ∫⁻ t, F g * ρ' g * ρ (j t⁻¹ * g) ∂ν := fun g => by
    rw [lintegral_const_mul _ (f := fun t => ρ (j t⁻¹ * g)) (hm.comp ((hj.comp measurable_inv).mul_const g)),
      lintegral_inv_eq_self (fun t : T => ρ (j t * g)), h, mul_one]
  rw [lintegral_congr a, lintegral_congr b,
    lintegral_lintegral_swap (f := fun g t => F g * ρ g * ρ' (j t * g))
      (((hF.comp measurable_fst).mul (hm.comp measurable_fst)).mul (hm'.comp hmul)).aemeasurable,
    lintegral_lintegral_swap (f := fun g t => F g * ρ' g * ρ (j t⁻¹ * g))
      (((hF.comp measurable_fst).mul (hm'.comp measurable_fst)).mul (hm.comp hmul')).aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_left_eq_self _ (j t⁻¹)]
  refine lintegral_congr fun g => ?_
  rw [hFH, ← mul_assoc (j t), ← map_mul, mul_inv_cancel, map_one, one_mul]
  ring

private theorem wd_eq [ν.IsInvInvariant] (hj : Measurable j) {F : G → ℂ} (hF : Measurable F) (hFH : ∀ t g, F (j t * g) = F g)
    {ρ ρ' : G → ℝ≥0∞} (hm : Measurable ρ) (h : ∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) (hm' : Measurable ρ') (h' : ∀ x, ∫⁻ t, ρ' (j t * x) ∂ν = 1) :
    ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ g, F g * ((ρ' g).toReal : ℂ) ∂μ := by
  have key : ∀ {ρ : G → ℝ≥0∞}, Measurable ρ → (∀ x, ∫⁻ t, ρ (j t * x) ∂ν = 1) →
      ∫ g, F g * ((ρ g).toReal : ℂ) ∂μ = ∫ z, z ∂((μ.withDensity ρ).map F) := fun {ρ} hm h => by
    rw [integral_map (f := fun z : ℂ => z) hF.aemeasurable aestronglyMeasurable_id, integral_withDensity_eq_integral_toReal_smul hm (ae_fin hj hm h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [mul_comm]
  rw [key hm h, key hm' h']
  congr 1
  ext A hA
  rw [Measure.map_apply hF hA, Measure.map_apply hF hA, withDensity_apply _ (hF hA), withDensity_apply _ (hF hA),
    ← lintegral_indicator (hF hA), ← lintegral_indicator (hF hA)]
  have e : ∀ ρ : G → ℝ≥0∞, (F ⁻¹' A).indicator ρ = fun g => (F ⁻¹' A).indicator 1 g * ρ g := fun ρ => funext fun g => by
    by_cases hg : g ∈ F ⁻¹' A <;> simp [hg]
  rw [e, e ρ']
  refine lint_eq hj (measurable_one.indicator (hF hA)) (fun t g => ?_) hm h hm' h'
  by_cases hg : F g ∈ A <;> simp [Set.indicator, hFH, hg]

end Core

theorem UpperTheory.V.Z.Tf.Orb.quotIndep :
    UpperTheory.V.Z.Tf.Orb.QuotIndep := by
  intro G _ _ _ _ _ _ _ _ μG hμ H μ _ _ F hF hFH ρ hρ
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hex : ∃ ρ, IsQuotNormaliser H μ ρ := ⟨ρ, hρ⟩
  rw [quotIntegral, dite_eq_left hex]
  exact wd_eq (j := H.subtype) measurable_subtype_coe hF (fun t g => hFH t t.2 g) hex.choose_spec.1 hex.choose_spec.2 hρ.1 hρ.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotMass
section
noncomputable section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc hiding twCent
open scoped ENNReal Pointwise

namespace UpperTheory.V.Z.Tf.Orb

private theorem unfold_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μ : Measure H} [SFinite μ] [μ.IsInvInvariant]
    {ψ ρ : G → ℝ≥0∞} (hψ : Measurable ψ) (hρ : IsQuotNormaliser H μ ρ) :
    ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG = ∫⁻ g, ψ g ∂μG := by
  have : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  have hmulH : Measurable fun p : H × G => (p.1 : G) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have e1 : ∫⁻ g, ρ g * ∫⁻ h : H, ψ ((h : G) * g) ∂μ ∂μG
      = ∫⁻ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG ∂μ := by
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul]
      exact hψ.comp (measurable_subtype_coe.mul_const g)
    · exact ((hρ.1.comp measurable_snd).mul (hψ.comp hmulH)).aemeasurable
  have e2 : ∀ h : H, ∫⁻ g, ρ g * ψ ((h : G) * g) ∂μG =
      ∫⁻ g, ψ g * ρ (((h⁻¹ : H) : G) * g) ∂μG := by
    intro h
    rw [← lintegral_mul_left_eq_self _ ((h : G)⁻¹)]
    refine lintegral_congr fun g => ?_
    rw [mul_inv_cancel_left, Subgroup.coe_inv, mul_comm]
  rw [e1, lintegral_congr e2, ← lintegral_lintegral_swap]
  · refine lintegral_congr fun g => ?_
    rw [lintegral_const_mul, lintegral_inv_eq_self (fun h : H => ρ ((h : G) * g)), hρ.2 g, mul_one]
    exact hρ.1.comp ((measurable_subtype_coe.comp measurable_inv).mul_const g)
  · have : Measurable fun p : G × H => ((p.2⁻¹ : H) : G) * p.1 :=
      (measurable_subtype_coe.comp (measurable_snd.inv)).mul measurable_fst
    exact ((hψ.comp measurable_fst).mul (hρ.1.comp this)).aemeasurable

theorem quotMass : QuotMass := by
  intro G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv ρ hρ
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  haveI : MeasurableInv H := ⟨(measurable_subtype_coe.inv).subtype_mk⟩
  haveI : μ.IsMulRightInvariant := by
    have h := (inferInstance : μ.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  have key : ∀ C : Set G, IsCompact C →
      IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} ∧
        ∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG ≠ ∞ := by
    intro C hC
    have hcl : IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} := by
      have e : {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} = (H : Set G) * C := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]
      rw [e]
      exact hH.mul_right_of_isCompact hC
    refine ⟨hcl, ?_⟩
    obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : G)
    have hD : IsCompact (V * C) := hV.mul hC
    have hDm : MeasurableSet (V * C) := hD.isClosed.measurableSet
    have hVm : MeasurableSet ((↑) ⁻¹' V : Set H) :=
      measurable_subtype_coe hV.isClosed.measurableSet
    have hm : μ ((↑) ⁻¹' V : Set H) ≠ 0 := by
      refine (Measure.measure_pos_of_mem_nhds μ (x := 1) ?_).ne'
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds hV1
    have hψ : Measurable ((V * C).indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hDm
    have hE := unfold_eq (μG := μG) hψ hρ
    rw [lintegral_indicator_one hDm] at hE
    have hlow : ∀ g ∈ {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c},
        μ ((↑) ⁻¹' V : Set H) ≤ ∫⁻ h : H, (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * g) ∂μ := by
      rintro g ⟨h0, hh0, c, hc, rfl⟩
      have := lintegral_mul_right_eq_self (μ := μ)
        (fun h : H => (V * C).indicator (1 : G → ℝ≥0∞) ((h : G) * c)) ⟨h0, hh0⟩
      simp only [Subgroup.coe_mul, mul_assoc] at this
      rw [this, ← lintegral_indicator_one hVm]
      refine lintegral_mono fun h => ?_
      by_cases hh : h ∈ ((↑) ⁻¹' V : Set H)
      · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (Set.mul_mem_mul (show (h : G) ∈ V from hh) hc)]
        rfl
      · rw [Set.indicator_of_notMem hh]
        exact zero_le
    have hle : (∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG) * μ ((↑) ⁻¹' V : Set H)
        ≤ μG (V * C) := by
      rw [← hE, ← lintegral_mul_const _ hρ.1]
      refine le_trans (setLIntegral_mono' hcl.measurableSet fun g hg => ?_)
        (setLIntegral_le_lintegral _ _)
      exact mul_le_mul_right (hlow g hg) _
    intro htop
    rw [htop, ENNReal.top_mul hm] at hle
    exact hD.measure_lt_top.not_ge hle
  refine ⟨?_, key⟩
  have hloc : ∀ n, ∀ᵐ g ∂μG, g ∈ compactCovering G n → ρ g ≠ ∞ := by
    intro n
    have hC := isCompact_compactCovering G n
    have h1 := ae_lt_top hρ.1 (key _ hC).2
    rw [ae_restrict_iff' (key _ hC).1.measurableSet] at h1
    filter_upwards [h1] with g hg hgC
    exact (hg ⟨1, H.one_mem, g, hgC, (one_mul g).symm⟩).ne
  filter_upwards [ae_all_iff.2 hloc] with g hg
  obtain ⟨n, hn⟩ := exists_mem_compactCovering g
  exact hg n hn

end UpperTheory.V.Z.Tf.Orb
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotPos
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc hiding twCent
open scoped ENNReal

theorem UpperTheory.V.Z.Tf.Orb.quotPos :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotMass → UpperTheory.V.Z.Tf.Orb.QuotPos := by
  intro _ hInt hMass G _ _ _ _ _ _ _ _ μG hμG H hH μ hμ hinv hex F hF hFH hC hnn hne
  have hρ := hex.choose_spec
  rw [quotIntegral, dite_eq_left hex]
  generalize hex.choose = ρ at hρ
  have hI := hInt G μG hμG H hH μ hμ hinv F hF hFH hC ρ hρ
  have hfin := (hMass G μG hμG H hH μ hμ hinv ρ hρ).1
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : SFinite μ := inferInstance
  have hre : (∫ g, F g * ((ρ g).toReal : ℂ) ∂μG).re = ∫ g, (F g).re * (ρ g).toReal ∂μG := by
    have := integral_re hI
    simpa using this.symm
  have hI' : Integrable (fun g => (F g).re * (ρ g).toReal) μG := by
    simpa using hI.re
  rw [hre]
  have h0 : 0 ≤ fun g => (F g).re * (ρ g).toReal := fun g => mul_nonneg (hnn g) ENNReal.toReal_nonneg
  refine lt_of_le_of_ne (integral_nonneg h0) fun hz => ?_
  have hae := (integral_eq_zero_iff_of_nonneg h0 hI').1 hz.symm
  set Φ : G → ℝ≥0∞ := fun g => ENNReal.ofReal (F g).re with hΦ
  have hΦc : Continuous Φ := ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp hF)
  have hΦm : Measurable Φ := hΦc.measurable
  have h1 : ∫⁻ g, Φ g * ρ g ∂μG = 0 := by
    refine (lintegral_eq_zero_iff (f := fun g => Φ g * ρ g) (hΦm.mul hρ.1)).2 ?_
    filter_upwards [hae, hfin] with g hg hg'
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.toReal_eq_zero_iff] at hg ⊢
    rcases hg with hg | hg | hg
    · left; simp [hΦ, hg]
    · right; exact hg
    · exact absurd hg hg'
  have hmul : Measurable fun p : G × H => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have h2 : ∫⁻ g, Φ g ∂μG = 0 := by
    calc ∫⁻ g, Φ g ∂μG = ∫⁻ g, ∫⁻ h : H, Φ g * ρ ((h : G) * g) ∂μ ∂μG := by
          refine lintegral_congr fun g => ?_
          rw [lintegral_const_mul, hρ.2 g, mul_one]
          exact hρ.1.comp (measurable_subtype_coe.mul_const g)
      _ = ∫⁻ h : H, ∫⁻ g, Φ g * ρ ((h : G) * g) ∂μG ∂μ :=
          lintegral_lintegral_swap ((hΦm.comp measurable_fst).mul (hρ.1.comp hmul)).aemeasurable
      _ = ∫⁻ _h : H, 0 ∂μ := by
          refine lintegral_congr fun h => ?_
          rw [← h1, ← lintegral_mul_left_eq_self (fun g => Φ g * ρ g) (h : G)]
          refine lintegral_congr fun g => ?_
          simp only [hΦ, hFH _ h.2]
      _ = 0 := lintegral_zero
  rw [lintegral_eq_zero_iff hΦm] at h2
  have h3 : Φ = 0 := (Continuous.ae_eq_iff_eq μG hΦc continuous_zero).1 h2
  obtain ⟨g, hg⟩ := hne
  have h4 := congrFun h3 g
  simp only [hΦ, Pi.zero_apply, ENNReal.ofReal_eq_zero] at h4
  exact hg (le_antisymm h4 (hnn g))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.QuotRight
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.V.Z.Tf.Orb.quotRight :
    UpperTheory.V.Z.Tf.Orb.QuotIndep → UpperTheory.V.Z.Tf.Orb.QuotRight := by
  intro hI G _ _ _ _ _ _ _ _ μG hμG hR H μ hs hinv F hF hFH y
  by_cases hex : ∃ ρ, IsQuotNormaliser H μ ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' : IsQuotNormaliser H μ (fun g => ρ (g * y)) := by
      refine ⟨hρ.1.comp (measurable_mul_const y), fun g => ?_⟩
      simpa only [mul_assoc] using hρ.2 (g * y)
    rw [hI G μG hμG H μ hs hinv F hF hFH ρ hρ,
      hI G μG hμG H μ hs hinv (fun g => F (g * y)) (hF.comp (measurable_mul_const y))
        (fun h hh g => by rw [mul_assoc, hFH h hh]) _ hρ']
    exact integral_mul_right_eq_self (fun g => F g * ((ρ g).toReal : ℂ)) y
  · simp only [quotIntegral, dif_neg hex]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwCent
section
open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc hiding twCent

theorem UpperTheory.V.Z.Tf.Orb.twCent :
    UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.CentComm → UpperTheory.V.Z.Tf.Orb.TwCent := by
  intro hE hG hC k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ _ n δ hδ
  have := (hG E n).2.2.1
  have hc := ((hE k E).2.2 n).2 σ
  have hp : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨isClosed_eq (f := fun g : GL (Fin n) E => g⁻¹ * δ * sigmaGL σ g) ((continuous_inv.mul continuous_const).mul hc)
    continuous_const, fun a ha b hb => ?_⟩
  have h1 := congrArg Units.val (twCent_commute_twNorm _ hp δ ha)
  have h2 := congrArg Units.val (twCent_commute_twNorm _ hp δ hb)
  exact Units.ext (hC E n _ a.val b.val hδ h1 h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbComm
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbComm :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.Unimod → UpperTheory.V.Z.Tf.Orb.AbsComm → UpperTheory.V.Z.Tf.Orb.TwOrbComm := by
  intro hG hX hC hP hH hU hA k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ a b a1 a2 b1 b2 ha
  obtain ⟨g1, g2, g3, -, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, -⟩ := hH _ _ c1 c2 μ hμ
  obtain ⟨u1, u2⟩ := hU E n μE hμE
  have hs := ((hX k E).2.2 n).2 σ
  have hl : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  have hp : ∀ (m : ℕ) x, a (((sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ m) x) = a x := fun m => by
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ_apply', ha, ih]
  have t := hA _ μE hμE u1 u2 (sigmaGL σ) hs _ Module.finrank_pos.ne' hl δ (hP k E σ hσ n δ hδ) μ hμ i2 a b a1 a2 b1 b2
  simpa only [hp] using t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbFin
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbFin :
    UpperTheory.V.Z.Tf.Orb.GLTop → UpperTheory.V.Z.Tf.Orb.ExtCont → UpperTheory.V.Z.Tf.Orb.TwCent → UpperTheory.V.Z.Tf.Orb.OrbProper → UpperTheory.V.Z.Tf.Orb.HaarComm → UpperTheory.V.Z.Tf.Orb.NormEx → UpperTheory.V.Z.Tf.Orb.QuotInt → UpperTheory.V.Z.Tf.Orb.QuotPos → UpperTheory.V.Z.Tf.Orb.TwOrbFin := by
  intro hG hX hC hP hH hN hI hQ k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE φ hφ hc δ hδ μ hμ
  obtain ⟨g1, g2, g3, g4, -⟩ := hG E n
  obtain ⟨c1, c2⟩ := hC k E σ hσ n δ hδ
  obtain ⟨-, i2, i3⟩ := hH _ _ c1 c2 μ hμ
  have hs := ((hX k E).2.2 n).2 σ
  obtain ⟨ρ, hρ, -⟩ := hN _ g4 _ c1 μ hμ i3
  have hF : Continuous fun g => φ (twConj (sigmaGL σ) g δ) := hφ.comp ((continuous_inv.mul continuous_const).mul hs)
  have hinv : ∀ h ∈ PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ, ∀ g, φ (twConj (sigmaGL σ) (h * g) δ) = φ (twConj (sigmaGL σ) g δ) :=
    fun h hh g => by rw [twConj_mul_left _ _ hh]
  have hM : CptMod (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) fun g => φ (twConj (sigmaGL σ) g δ) := by
    obtain ⟨D, hD, h⟩ := hP k E σ hσ n δ hδ _ hc
    exact ⟨D, hD, fun g hg => h g (subset_tsupport _ hg)⟩
  exact ⟨⟨ρ, hρ⟩, hI _ μE hμE _ c1 μ hμ i2 _ hF hinv hM,
    fun p q => hQ _ μE hμE _ c1 μ hμ i2 ⟨ρ, hρ⟩ _ hF hinv hM (fun g => p _) q⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.TwOrbLin
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

theorem UpperTheory.V.Z.Tf.Orb.twOrbLin :
    UpperTheory.V.Z.Tf.Orb.TwOrbFin → UpperTheory.V.Z.Tf.Orb.TwOrbLin := by
  intro hT k _ _ _ _ _ E _ _ _ _ _ _ _ _ σ hσ n _ _ μE hμE δ hδ μ hμ
  refine ⟨fun c φ => ?_, fun φ ψ a1 a2 b1 b2 => ?_⟩
  · simp only [twOrbIntegralC, quotIntegral]
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    · simp
  · obtain ⟨h, p, -⟩ := hT k E σ hσ n μE hμE φ a1 a2 δ hδ μ hμ
    obtain ⟨-, q, -⟩ := hT k E σ hσ n μE hμE ψ b1 b2 δ hδ μ hμ
    simp only [twOrbIntegralC, quotIntegral, dif_pos h, Pi.add_apply, add_mul]
    exact integral_add (p _ h.choose_spec) (q _ h.choose_spec)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Untwist
section
open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem aux {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μG : Measure G) (H H' : Subgroup G) (e : H' = H)
    (μ : Measure H) (hμ : μ.IsHaarMeasure) : ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser H' μ' ρ ↔ IsQuotNormaliser H μ ρ) ∧ ∀ F, quotIntegral μG H' μ' F = quotIntegral μG H μ F := by
  subst e
  exact ⟨μ, hμ, fun _ => Iff.rfl, fun _ => rfl⟩

theorem UpperTheory.V.Z.Tf.Orb.untwist :
    UpperTheory.V.Z.Tf.Orb.Untwist := by
  intro k _ _ _ _ n _ _ μk γ
  have h1 : ∀ g : GL (Fin n) k, sigmaGL (1 : k ≃ₐ[k] k) g = g := fun g => by rw [sigmaGL_one]; rfl
  refine ⟨fun τ => ?_, h1, fun h => ?_, fun μ hμ => ?_⟩
  · have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  · have : normGL (1 : k ≃ₐ[k] k) γ = γ := by
      rw [normGL, Module.finrank_self]
      simp [twNorm]
    rwa [IsTwRegSemisimple, this]
  · have e : PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ = Subgroup.centralizer {γ} := by
      ext x
      rw [mem_twCent, h1, Subgroup.mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
      rw [commute_iff_eq]
    obtain ⟨μ', a, b, c⟩ := aux μk _ _ e μ hμ
    refine ⟨μ', a, b, fun f => ?_⟩
    rw [twOrbIntegralC, orbIntegralC, c]
    simp only [twConj, h1]
end

