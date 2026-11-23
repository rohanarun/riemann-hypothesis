module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalChartSheetDecomposition
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens

section Change

open Set

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem restrict_chernPart_of_coords [SecondCountableTopology (GlobalTheory.CxPts q σ)] {φ : GlobalTheory.Weight q σ B} (h : φ.IsCInf)
    (ε : ℤˣ) (c : GlobalTheory.AlgChart q σ D) (e : OpenPartialHomeomorph (GlobalTheory.CxPts q σ) (Fin D → ℂ))
    (hsub : e.source ⊆ c.e.source) (hd : DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target) {ρ : (Fin D → ℂ) → ℝ}
    (hρ : ∀ v ∈ e.target, ρ v = ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v :
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (e.symm v)) :
    (φ.chernPart D ε).restrict e.source =
      ((volume.restrict e.target).withDensity fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ v)).map e.symm := by
  ext T hT
  set κ := c.finChart ∘ e.symm with hκ
  have ht := e.open_target.measurableSet
  have hs : AEMeasurable e.symm (volume.restrict e.target) := e.continuousOn_symm.aemeasurable ht
  have hS : MeasurableSet (T ∩ e.source) := hT.inter e.open_source.measurableSet
  have hSc : T ∩ e.source ⊆ c.finChart.source := inter_subset_right.trans hsub
  have hA : MeasurableSet (e.target ∩ e.symm ⁻¹' T) := by
    have hm : Measurable (e.target.restrict e.symm) :=
      (continuousOn_iff_continuous_restrict.1 e.continuousOn_symm).measurable
    have := ht.subtype_image (hm hT)
    convert this using 1
    ext v
    exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩
  have him : c.finChart.target ∩ c.finChart.symm ⁻¹' (T ∩ e.source) = κ '' (e.target ∩ e.symm ⁻¹' T) := by
    rw [← c.finChart.image_source_inter_eq', inter_eq_right.2 hSc]
    ext z
    constructor
    · rintro ⟨y, ⟨hyT, hys⟩, rfl⟩
      exact ⟨e y, ⟨e.map_source hys, by simpa only [mem_preimage, e.left_inv hys] using hyT⟩, by
        simp only [hκ, Function.comp_apply, e.left_inv hys]⟩
    · rintro ⟨v, ⟨hv, hvT⟩, rfl⟩
      exact ⟨e.symm v, ⟨hvT, e.map_target hv⟩, rfl⟩
  have hinj : InjOn κ (e.target ∩ e.symm ⁻¹' T) := fun v hv w hw hvw => by
    have h1 := c.finChart.injOn (hsub (e.map_target hv.1)) (hsub (e.map_target hw.1)) hvw
    exact e.symm.injOn hv.1 hw.1 h1
  have hder : ∀ v ∈ e.target ∩ e.symm ⁻¹' T, HasFDerivWithinAt κ
      ((fderiv ℂ κ v).restrictScalars ℝ) (e.target ∩ e.symm ⁻¹' T) v := fun v hv =>
    (((hd.differentiableAt (e.open_target.mem_nhds hv.1)).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have hsc : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable c.finChart.open_target.measurableSet
  have e1 : φ.chernPart D ε (T ∩ e.source) =
      ((φ.chernPart D ε).restrict c.finChart.source) (T ∩ e.source) := by
    rw [Measure.restrict_apply hS, inter_eq_left.2 hSc]
  rw [Measure.restrict_apply hT, e1, GlobalTheory.ChernMA.restrict_chernPart h ε c,
    Measure.map_apply_of_aemeasurable (hsc.mono_ac (withDensity_absolutelyContinuous _ _)) hS,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', withDensity_apply', Measure.restrict_restrict' c.finChart.open_target.measurableSet,
    Measure.restrict_restrict' ht, inter_comm, him, inter_comm (e.symm ⁻¹' T),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hder hinj]
  refine setLIntegral_congr_fun hA fun v hv => ?_
  have hdet : ((fderiv ℂ κ v).restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (fderiv ℂ κ v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
    ReciprocityTheory.AnForm.A.det_restrictScalars_real _
  have hleft : c.finChart.symm (κ v) = e.symm v := c.finChart.left_inv (hsub (e.map_target hv.1))
  simp only [hleft, hdet, hρ v hv.1]
  rw [abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  congr 1
  ring

end Change

section Piece

open Filter _root_.Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} (i : X ⟶ MP ℤ m n)

theorem mem_ptsIn_pre (W : (MP ℤ m n).Opens) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ W) ↔ PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

variable [IsClosedImmersion i] {D : ℕ} {e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)}
  {Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ}

theorem differentiableOn_coords (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (hsub : e.source ⊆ c.e.source) :
    DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target := by
  refine differentiableOn_pi.2 fun a => ?_
  have h := (GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 c.U (c.x a)
  refine (h.mono fun v hv => ⟨hv, c.source_subset (hsub (e.map_target hv))⟩).congr fun v hv => ?_
  exact c.finChart_eq_ev (hsub (e.map_target hv)) a

theorem maDensity_eq (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)) (hrep : IsHermRep Nh B)
    (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (hsub : e.source ⊆ c.e.source) {v : Fin D → ℂ} (hv : v ∈ e.target) :
    maDensity (fun _ y' => Real.log (B.h (Γ y'))) v =
      ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 *
        c.chernDens ((Nh.restr i).φ σ₀) (e.symm v) := by
  have hκd := differentiableOn_coords i hΓ hover c hsub
  set φ := (Nh.restr i).φ σ₀ with hφ
  have h : φ.IsCInf := (Nh.restr i).cInf σ₀
  set κ := c.finChart ∘ e.symm with hκ
  set y₀ := e.symm v with hy₀def
  have hy₀ : y₀ ∈ c.e.source := hsub (e.map_target hv)
  have hκv : AnalyticAt ℂ κ v := GlobalTheory.SCV.analyticAt_of_differentiableOn hκd (e.open_target.mem_nhds hv)
  have hκy : c.finChart.symm (κ v) = y₀ := c.finChart.left_inv hy₀
  have hz : κ v ∈ c.finChart.target := c.finChart.map_source hy₀
  have hma := h.maDens_eq c hz
  rw [hκy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (κ v) := rfl
  have hd := h.contDiffAt c hy₀ (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (κ v) :=
    (hd.comp (κ v) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) κ v hκv (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  have hC2 : ContDiffAt ℝ 2 ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    hψ.comp v (hκv.contDiffAt.restrict_scalars ℝ)
  obtain ⟨u, hu⟩ := (isHermRep_iff Nh B).1 hrep
  choose p hp using hmc v hv
  set b := pick φ.isLB y₀ with hbdef
  have hb : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (Nh.B.U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y₀) (fun _ => rfl) (mem_pick φ.isLB y₀) PUnit.unit
  have hmch : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart p) :=
    (GlobalTheory.CompanionTheory.MixZ.Holo.mem_ptsIn_mchart p).2 fun k => ((hover v hv) k (p k)).1.2 (hp k)
  set W := i ⁻¹ᵁ (Nh.B.U (b PUnit.unit) ⊓ mchart p) with hW
  let f : Γ(X, W) := i.app _ (u (b PUnit.unit) p).val
  set O := e.target ∩ e.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W with hOdef
  have hO : IsOpen O := e.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hvO : v ∈ O := ⟨hv, (mem_ptsIn_pre i _ _).2 (mem_ptsIn_inf.2 ⟨hb, hmch⟩)⟩
  let g : (Fin D → ℂ) → ℂ := fun w => (∏ k, Γ w ⟨k, p k⟩ ^ B.a k) * ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w)
  have hF : AnalyticAt ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ e.symm) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn
      ((GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 W f) (hO.mem_nhds hvO)
  have hΓk (k) : AnalyticAt ℂ (fun w => Γ w ⟨k, p k⟩) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 hΓ _) (e.open_target.mem_nhds hv)
  have hg : AnalyticAt ℂ g v := (Finset.analyticAt_fun_prod _ fun k _ => (hΓk k).zpow (hp k)).mul hF
  have hunit : IsUnit f := (u (b PUnit.unit) p).isUnit.map (i.app _).hom
  have hg0 : g v ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k))
    (ev_ne_zero hvO.2 hunit)
  have hev : (fun w => Real.log (B.h (Γ w))) =ᶠ[𝓝 v]
      fun w => ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) w + Real.log ‖g w‖ := by
    filter_upwards [hO.mem_nhds hvO] with w hw
    have hy : e.symm w ∈ c.e.source := hsub (e.map_target hw.1)
    have hmem := (mem_ptsIn_pre i _ _).1 hw.2
    have hrep' := hu.2.2 (b PUnit.unit) p (PtsOver.map i rfl _ (e.symm w)) (Γ w) (hover w hw.1) hmem
    have hzk : ∀ k, Γ w ⟨k, p k⟩ ≠ 0 := fun k =>
      ((hover w hw.1) k (p k)).1.1 (ptsIn_mono (mchart_le p k) (mem_ptsIn_inf.1 hmem).2)
    have hu0 : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) ≠ 0 := ev_ne_zero hw.2 hunit
    have hev' : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) =
        ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w)) :=
      CxPts.ev_app i rfl _ _ _
    have hg0w : g w ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hzk k)) hu0
    have hnorm : ‖g w‖ = (∏ k, ‖Γ w ⟨k, p k⟩‖ ^ B.a k) *
        ‖ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w))‖ := by
      simp only [g, norm_mul, norm_prod, norm_zpow, hev']
    have hφb : φ.φ b (e.symm w) = (Nh.φ σ₀).φ (b PUnit.unit) (PtsOver.map i rfl _ (e.symm w)) :=
      GlobalTheory.Weight.pull_φ _ i rfl b _
    have hleft : c.finChart.symm (κ w) = e.symm w := c.finChart.left_inv hy
    change Real.log (B.h (Γ w)) = φ.φ b (c.finChart.symm (κ w)) / 2 + Real.log ‖g w‖
    rw [hleft, hφb, hrep', ← hnorm, Real.log_mul (norm_ne_zero_iff.2 hg0w) (Real.exp_ne_zero _), Real.log_exp, add_comm]
  have hh : hessC (fun w => Real.log (B.h (Γ w))) v =
      hessC ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    (hessCGerm _ _ _ hev).trans (ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g v hC2 hg hg0)
  change maDens (fun _ y' => Real.log (B.h (Γ y'))) v = _
  rw [maDens_congr_hessC _ (fun _ => (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v fun _ => hh, hcomp]
  ring

theorem contDiffOn_log_metric {B : HermLine (Bk n)} (hB : IsSmoothHerm B) (hΓ : DifferentiableOn ℂ Γ e.target)
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) :
    ContDiffOn ℝ 2 (fun y' => Real.log (B.h (Γ y'))) e.target := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ e.target :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn e.open_target hΓ _).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => B.h (Γ y')) e.target := hB.comp h1 hmc
  exact (h2.log fun v hv => (B.pos _ (hmc v hv)).ne').of_le (by norm_cast)

end Piece

theorem piece_density : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  intro m n Nh B hrep hB X _ i _ D _ Ψ N e Γ hP
  obtain ⟨⟨c, hsub⟩, hΓ, hall⟩ := hP
  have hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v) := fun v hv => (hall v hv).1
  have hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0 := fun v hv => (hall v hv).2.1.1
  refine ⟨ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ e.open_target fun _ => contDiffOn_log_metric i hB hΓ hmc, fun ε => ?_⟩
  exact restrict_chernPart_of_coords ((Nh.restr i).cInf σ₀) ε c e hsub (differentiableOn_coords i hΓ hover c hsub)
    fun v hv => maDensity_eq i Nh B hrep hΓ hover hmc c hsub hv

end GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistOrbit

theorem finite_of_subset_mul' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K' : Subgroup G)
    (hK' : IsOpen (K' : Set G)) (D : Set G) (hD : IsCompact D)
    (P : G → Prop) (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set G) (K' : Set G) | P (Quotient.out q)}.Finite := by
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hD
    (show (interior (K' : Set G)).Nonempty from ⟨1, hK'.interior_eq.symm ▸ K'.one_mem⟩)
  refine (s.finite_toSet.image fun g => DoubleCoset.mk T K' g⁻¹).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  have := hs hd
  simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe] at this
  obtain ⟨g, hg, hgd⟩ := this
  refine ⟨g, hg, ?_⟩
  rw [← DoubleCoset.out_eq' q, DoubleCoset.eq]
  exact ⟨t, ht, g * d, hgd, by simp [hx, mul_assoc]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twConj' (hU : Unr E) (n : ℕ) (w : Pl E) (x y : GLw n w) :
    nrmL n w (x⁻¹ * y * thL n w x) = x⁻¹ * nrmL n w y * x := by
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    simp only [nrmL, if_pos hs, h1, MonoidHom.id_apply]
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).2
    rw [h1] at h2
    simp only [nrmL, if_neg hs, h1, map_mul, map_inv, h2]
    group

theorem continuous_nrmL' (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = fun u => u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    have hc := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
    rw [h1] at hc
    have e : nrmL n w = fun u => u * thetaGL n (cj w) u := funext fun u => by simp [nrmL, hs]
    rw [e]; exact continuous_id.mul hc

theorem proper' (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (C : Set (GLw n w)) (hC : IsCompact C) : ∃ D : Set (GLw n w), IsCompact D ∧
      ∀ x : GLw n w, x⁻¹ * y * thL n w x ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, x = t * d := by
  have hθ := (GlobalTheory.BCT.thL_continuous_involutive E hU n w).1
  obtain ⟨D₁, hD₁, h₁⟩ := _root_.GlobalTheory.OrbitCptW.orbit_cpt_w E hU n w (nrmL n w y) hy _ (hC.image (continuous_nrmL' hU n w))
  set C₂ := (fun p : GLw n w × GLw n w × GLw n w => p.1 * p.2.1 * (thL n w p.2.2)⁻¹) '' (D₁ ×ˢ C ×ˢ D₁)
  have hC₂ : IsCompact C₂ := (hD₁.prod (hC.prod hD₁)).image (by fun_prop)
  obtain ⟨D₂, hD₂, h₂⟩ := GlobalTheory.NormOneProper.main E hU n w y hy C₂ hC₂
  refine ⟨(fun p : GLw n w × GLw n w => p.1 * p.2) '' (D₂ ×ˢ D₁), (hD₂.prod hD₁).image (by fun_prop), ?_⟩
  intro x hx
  obtain ⟨z, hz, d, hd, rfl⟩ := h₁ x ⟨_, hx, by rw [nrmL_twConj' hU]⟩
  have hz2 : z⁻¹ * y * thL n w z ∈ C₂ := ⟨(d, (z * d)⁻¹ * y * thL n w (z * d), d), ⟨hd, hx, hd⟩, by
    simp only [map_mul]; group⟩
  obtain ⟨t, ht, d₂, hd₂, rfl⟩ := h₂ z hz hz2
  exact ⟨t, ht, d₂ * d, ⟨(d₂, d), ⟨hd₂, hd⟩, rfl⟩, by group⟩

theorem continuous_thPair (hU : Unr E) (a b : ℕ) (w : Pl E) :
    Continuous ((thL a w).prodMap (thL b w)) := by
  have h1 := (GlobalTheory.BCT.thL_continuous_involutive E hU a w).1
  have h2 := (GlobalTheory.BCT.thL_continuous_involutive E hU b w).1
  exact (h1.comp continuous_fst).prodMk (h2.comp continuous_snd)

theorem isOpen_isCompact_pair_integral_points (a b : ℕ) (w : Pl E) :
    IsOpen (K2 a b w : Set (GLw a w × GLw b w)) ∧ IsCompact (K2 a b w : Set (GLw a w × GLw b w)) := by
  obtain ⟨o₁, c₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨o₂, c₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [K2, Subgroup.coe_prod]
  exact ⟨o₁.prod o₂, c₁.prod c₂⟩

theorem proper_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    ∃ D : Set (GLw a w × GLw b w), IsCompact D ∧ ∀ x : GLw a w × GLw b w,
      x⁻¹ * y * ((thL a w).prodMap (thL b w)) x ∈ C →
        ∃ t ∈ twCent ((thL a w).prodMap (thL b w)) y, ∃ d ∈ D, x = t * d := by
  obtain ⟨D₁, hD₁, p₁⟩ := proper' hU a w y.1 h₁ _ (hC.image continuous_fst)
  obtain ⟨D₂, hD₂, p₂⟩ := proper' hU b w y.2 h₂ _ (hC.image continuous_snd)
  refine ⟨D₁ ×ˢ D₂, hD₁.prod hD₂, fun x hx => ?_⟩
  obtain ⟨t₁, ht₁, d₁, hd₁, e₁⟩ := p₁ x.1 ⟨_, hx, rfl⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, e₂⟩ := p₂ x.2 ⟨_, hx, rfl⟩
  refine ⟨(t₁, t₂), ?_, (d₁, d₂), ⟨hd₁, hd₂⟩, Prod.ext e₁ e₂⟩
  exact Prod.ext ht₁ ht₂

theorem finite_doubleCosets (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable)
    (C : Set (GLw a w × GLw b w)) (hC : IsCompact C) :
    {q : DoubleCoset.Quotient (twCent ((thL a w).prodMap (thL b w)) y : Set (GLw a w × GLw b w))
        (K2 a b w : Set (GLw a w × GLw b w)) |
      ∃ k ∈ K2 a b w, (Quotient.out q * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (Quotient.out q * k) ∈ C}.Finite := by
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  obtain ⟨D, hD, hp⟩ := proper_pair hU a b w y h₁ h₂ C hC
  have hD' : IsCompact ((fun p : (GLw a w × GLw b w) × (GLw a w × GLw b w) => p.1 * p.2⁻¹) ''
      (D ×ˢ (K2 a b w : Set (GLw a w × GLw b w)))) :=
    (hD.prod hKc).image (continuous_fst.mul continuous_snd.inv)
  refine finite_of_subset_mul' _ (K2 a b w) hKo _ hD'
    (fun x => ∃ k ∈ K2 a b w, (x * k)⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * k) ∈ C) ?_
  rintro x ⟨k, hk, hx⟩
  obtain ⟨t, ht, d, hd, e⟩ := hp _ hx
  refine ⟨t, ht, d * k⁻¹, ⟨(d, k), ⟨hd, hk⟩, rfl⟩, ?_⟩
  rw [← mul_assoc, ← e, mul_inv_cancel_right]

theorem rStab_index_ne_zero (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (K' : Subgroup (GLw a w × GLw b w)) (f : GLw a w × GLw b w → ℂ) (ho : IsOpen (K' : Set (GLw a w × GLw b w)))
    (hf : IsHecke K' f) (x : K2 a b w) :
    (rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      ((thL a w).prodMap (thL b w)) ((x : GLw a w × GLw b w) * k))).index ≠ 0 := by
  obtain ⟨-, hKc⟩ := isOpen_isCompact_pair_integral_points (E := E) a b w
  have hθ := continuous_thPair hU a b w
  set θ := (thL a w).prodMap (thL b w) with hθdef
  set W : Subgroup (GLw a w × GLw b w) := K' ⊓ K'.comap θ with hW
  have hWo : IsOpen (W : Set (GLw a w × GLw b w)) := by
    rw [hW, Subgroup.coe_inf]
    exact ho.inter (ho.preimage hθ)
  haveI : CompactSpace (K2 a b w) := isCompact_iff_compactSpace.mp hKc
  have hWo' : IsOpen ((W.subgroupOf (K2 a b w) : Subgroup (K2 a b w)) : Set (K2 a b w)) :=
    hWo.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hWo'
  haveI : (W.subgroupOf (K2 a b w)).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hle : W.subgroupOf (K2 a b w) ≤ rStab fun k : K2 a b w => f (((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
      θ ((x : GLw a w × GLw b w) * k)) := by
    intro k' hk' k
    have hk'W : (k' : GLw a w × GLw b w) ∈ W := Subgroup.mem_subgroupOf.mp hk'
    have hl : (k' : GLw a w × GLw b w)⁻¹ ∈ K' := K'.inv_mem hk'W.1
    have hr : θ (k' : GLw a w × GLw b w) ∈ K' := hk'W.2
    have e : (((x * (k * k') : K2 a b w) : GLw a w × GLw b w)⁻¹ * y * θ ((x : GLw a w × GLw b w) * (k * k' : K2 a b w))) =
        (k' : GLw a w × GLw b w)⁻¹ * ((((x * k : K2 a b w) : GLw a w × GLw b w)⁻¹ * y *
          θ ((x : GLw a w × GLw b w) * k)) * θ (k' : GLw a w × GLw b w)) := by
      simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev, mul_assoc]
    show f _ = f _
    rw [e, (hf.2 _ hl _).1, (hf.2 _ hr _).2]
  exact (Subgroup.finiteIndex_of_le hle).index_ne_zero

theorem locSupp : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact ⟨fun C hC => finite_doubleCosets hU a b w y h₁ h₂ C hC,
    fun K' f ho _ hf x => rStab_index_ne_zero hU a b w y K' f ho hf x⟩

end GlobalTheory.CompanionTheory.TwistOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_block_ne_zero_of_isUnder {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : IsUnder y z) (k : Fin (m + 1)) :
    ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨ptChart _ k, (h k _).1.1 (CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩

theorem combLine_unit_a (A : HermLine (Bk n)) : (combLine (fun _ : Unit => A) 1).a = A.a := by
  simp [combLine]

theorem combLine_unit_h (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = A.h z := by
  simp [combLine, if_pos hz]

theorem combLine_unit_h_off (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = 0 :=
  if_neg hz

theorem isHermRep_combLine_unit {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hA : IsHermRep M A) :
    IsHermRep M (combLine (fun _ : Unit => A) 1) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hA
  refine ⟨u, h₁, fun i c c' => ?_, fun i c y z hu hy => ?_⟩
  · rw [combLine_unit_a]
    exact h₂ i c c'
  · rw [combLine_unit_h A (exists_block_ne_zero_of_isUnder hu), combLine_unit_a]
    exact h₃ i c y z hu hy

theorem existsRead : ExistsRead := by
  rintro m n M ⟨c, t, e⟩
  obtain ⟨A, hA, -⟩ := _root_.GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB m n M c t e
  have hs : IsSmoothHerm A := GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep m n M A hA
  exact ⟨combLine (fun _ : Unit => A) 1, isSmoothHerm_combLine (fun _ => hs) 1, isHermRep_combLine_unit hA,
    fun z hz => combLine_unit_h_off A hz⟩

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiProductSingleFactorEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multi_product_single_factor_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | exact GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single | (intros; apply GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_clOf_single <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_unitary_group_invariant : QK → Law → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (h : GA D B), (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | exact GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.InvU.nuT_map_ac <;> assumption)
end

