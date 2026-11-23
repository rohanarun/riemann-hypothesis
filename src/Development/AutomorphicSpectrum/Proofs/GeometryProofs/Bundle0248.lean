module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0219
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0221
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPunctured
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeDegreeBound
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix ComplexOrder

theorem exists_hermMetric_hodge : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (Wb : ChartBundle ℤ (segreCoord y) N ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → SncChart (mCoordIdeal y) n Bd), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB N ⊤ → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsChartOf (segreCoord y) Wb.lat → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → ∃ hm : HermMetric y Wb (mcPts (mCoordIdeal y) \ Bd) χ, ∀ e (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → InFrameDomain y (hm.chart e) (hm.fr e) w → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((hm.b e k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (hm.gram e w) := by
  intro hG E _ _ _ H D Xo l c Y hGl S Ω _ _ K _ J _ y 𝔐 a b N Wb n nc Bd χ hVB hCh hBd
  classical
  obtain ⟨m, ch, fr, bb, hfr, hcov⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_frames_cover_mcPts 𝔐.X Ω 𝔐.ξ K J y _ N Wb _ 𝔐.tie hVB hCh
  have tp := _root_.GlobalTheory.CompanionTheory.Ar.tie_points 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie ℂ
  have hpol : ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → HodgeMetric.PolarisedAt 𝔐.t z :=
    fun z hz => _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l (Xo l) c Y S Ω K J y 𝔐 z hz
  have gfn : ∀ {r : ℕ} (b' : Fin r → 𝔐.Li) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ)
      (Γ : Matrix (Fin r) (Fin r) ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z → 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ →
      HodgeMetric.gramFn 𝔐 b' w = Γ := by
    intro r b' z w Γ hw hi hΓ
    have hex : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ := ⟨Γ, z, hw, hi, hΓ⟩
    unfold HodgeMetric.gramFn
    rw [dite_eq_left hex]
    obtain ⟨z₀, hw₀, hi₀, hΓ₀⟩ := hex.choose_spec
    have hz : z₀ = z := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw₀⟩ ⟨𝔐.all _, hw⟩
    rw [hz] at hΓ₀
    exact _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt E H D l (Xo l) c Y S Ω K J y 𝔐 z r b' _ _ (hpol z hi) hΓ₀ hΓ
  have frameAt : ∀ (i : Fin m) (p : Cpt 𝔐.ξ), InChart 𝔐.ξ (segreCoord y) (ch i) p → unitAt 𝔐.ξ p (fr i) →
      (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt (bb i) p :=
    fun i p h1 h2 => (_root_.GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt 𝔐.X Ω 𝔐.ξ K J y _ N Wb _ 𝔐.tie hVB hCh (ch i) (fr i) (bb i) (hfr i).1 (hfr i).2.1
      (hfr i).2.2.1).1 (hfr i) p h1 h2
  obtain ⟨gr, hgr⟩ : ∃ gr : Fin m → ((Σ k, J k) → ℂ) → Matrix (Fin N) (Fin N) ℂ,
      ∀ i, gr i = HodgeMetric.gramFn 𝔐 (fun k => ((bb i k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) := ⟨_, fun _ => rfl⟩
  have key : ∀ (i : Fin m) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w →
      𝔐.Interior z → InFrameDomain y (ch i) (fr i) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb i k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (gr i w) ∧ (gr i w).PosDef := by
    intro i z w hw hi hd
    have hc := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w (ch i) (fr i) (𝔐.all _) hw hd
    obtain ⟨Γ, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef E H D l (Xo l) c Y S Ω K J y 𝔐 a b N (bb i) z (𝔐.all _) (hpol z hi)
      (frameAt i _ hc.1 hc.2)
    have h3 : gr i w = Γ := (congrFun (hgr i) w).trans (gfn _ z w Γ hw hi h1)
    rw [h3]
    exact ⟨h1, h2⟩
  have pts : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  have intr : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → w ∉ Bd → 𝔐.Interior z :=
    fun z w hz hn => by_contra fun h => hn ((hBd z w hz).2 h)
  have per : ∀ (e : Fin nc) (i : Fin m) (t₀ : Fin n → ℂ), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      InFrameDomain y (ch i) (fr i) ((χ e).γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ)
        (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ),
        HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb i k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (χ e) t₀ (ch i) (fr i) L π ρ U :=
    fun e i t₀ ht hd => _root_.GlobalTheory.CompanionTheory.Ar.FramePeriods.exists_isFramePeriods hG E H D Xo l c Y S Ω K J y 𝔐 hGl a b N (bb i) n Bd (χ e) t₀ (ch i) (fr i) hBd ht
      (frameAt i) hd
  have pg : ∀ (e : Fin nc) (i : Fin m) (t₀ : Fin n → ℂ) {a₀ g : ℕ} {Λ : Type} [AddCommGroup Λ]
      (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ),
      HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb i k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (χ e) t₀ (ch i) (fr i) L π ρ U →
      ∀ u ∈ Flat.punct n a₀ 1, gr i ((χ e).γ (HodgeMetric.recentre t₀ ρ π u)) = HodgeMetric.periodGram L U u := by
    intro e i t₀ a₀ g Λ _ L π ρ U hP u hu
    obtain ⟨hb, hd, hbd, hg⟩ := hP.2.2.2.2.2 u hu.1
    obtain ⟨z, hz⟩ := pts _ ((χ e).mem _ hb)
    have hi := intr z _ hz (hbd.2 hu)
    exact (congrFun (hgr i) _).trans (gfn _ z _ _ hz hi (hg hu z hz))
  have pgt : ∀ (e : Fin nc) (i : Fin m) (t₀ : Fin n → ℂ) {a₀ g : ℕ} {Λ : Type} [AddCommGroup Λ]
      (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ),
      HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb i k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (χ e) t₀ (ch i) (fr i) L π ρ U →
      ∀ t : Fin n → ℂ, HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 →
      ∀ᶠ t' in nhds t, gr i ((χ e).γ t') = HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') := by
    intro e i t₀ a₀ g Λ _ L π ρ U hP t ht
    have hc : Continuous (HodgeMetric.uncentre t₀ ρ π) := (HodgeMetric.contDiff_uncentre t₀ ρ π).continuous
    filter_upwards [hc.continuousAt.eventually ((HodgeMetric.isOpen_punct n a₀ 1).mem_nhds ht)] with t' ht'
    have h := pg e i t₀ L π ρ U hP _ ht'
    rwa [HodgeMetric.recentre_uncentre t₀ hP.1 π t'] at h
  have hcompat : ∀ l₁ l₂, ∀ z ∈ mcPts (mCoordIdeal y) \ Bd, InFrameDomain y (ch l₁) (fr l₁) z →
      InFrameDomain y (ch l₂) (fr l₂) z →
      ∀ T : Matrix (Fin N) (Fin N) Ω, (∀ q, bb l₂ q = ∑ p, T p q • bb l₁ p) →
      ∀ Tz : Matrix (Fin N) (Fin N) ℂ, (∀ p q, IsValueAt y (T p q) z (Tz p q)) →
        gr l₂ z = Tz.conjTranspose * gr l₁ z * Tz := by
    intro l₁ l₂ w hw hd₁ hd₂ T hT Tz hTz
    obtain ⟨z, hz⟩ := pts w hw.1
    have hi := intr z w hz hw.2
    refine GlobalTheory.T.gram_matrix_two_frames E H D l (Xo l) c Y S Ω K J y 𝔐 z N _ _ _ _ T Tz (hpol z hi) (key l₁ z w hz hi hd₁).1
      (key l₂ z w hz hi hd₂).1 (fun q => ?_) (fun p q => ?_)
    · rw [hT q]
      simp
    · exact (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z w (𝔐.all _) hz _ _).2 (hTz p q)
  have htorus : ∀ l₁, ∀ z ∈ mcPts (mCoordIdeal y) \ Bd, InFrameDomain y (ch l₁) (fr l₁) z → ∀ cv : K → ℂ,
      (∀ k, cv k ≠ 0) → gr l₁ (torusSmul cv z) = gr l₁ z := by
    intro i w hw hd cv hc
    obtain ⟨z, hz⟩ := pts w hw.1
    have hi := intr z w hz hw.2
    have hz' : CoordsAt 𝔐.ξ y z (torusSmul cv w) :=
      ((tp.2.2 z w (𝔐.all _) hz).2 _).2 ⟨fun k => Units.mk0 (cv k) (hc k), rfl⟩
    exact (congrFun (hgr i) _).trans (gfn _ z _ _ hz' hi (key i z w hz hi hd).1)
  have hconj : ∀ l₁, ∀ z ∈ mcPts (mCoordIdeal y) \ Bd, InFrameDomain y (ch l₁) (fr l₁) z →
      gr l₁ (conjVec z) = (gr l₁ z).map (starRingEnd ℂ) := by
    intro i w hw hd
    obtain ⟨z, hz⟩ := pts w hw.1
    have hi := intr z w hz hw.2
    have hcc := _root_.GlobalTheory.CompanionTheory.Ar.CoordConj.centre_and_coords_conj 𝔐.X Ω 𝔐.ξ K J y z w
    have hi' : 𝔐.Interior (spMap (starRingEnd ℂ) ≫ z) := by
      show centre _ ∈ _
      rw [hcc.1]
      exact hi
    exact (congrFun (hgr i) _).trans (gfn _ _ _ _ (hcc.2 hz) hi'
      (_root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point E H D l (Xo l) c Y S Ω K J y 𝔐 z N _ _ (key i z w hz hi hd).1))
  have hsmooth : ∀ e l₁, ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, (χ e).γ t ∈ mcPts (mCoordIdeal y) \ Bd →
      InFrameDomain y (ch l₁) (fr l₁) ((χ e).γ t) → ∀ p q,
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => gr l₁ ((χ e).γ t') p q) t := by
    intro e i t ht hX hd p q
    obtain ⟨a₀, g, Λ, _, L, π, ρ, U, hP⟩ := per e i t ht hd
    have h0 : (0 : Fin n → ℂ) ∈ Flat.punct n a₀ 1 := by
      have h := (hP.2.2.2.2.2 0 (Metric.mem_ball_self one_pos)).2.2.1
      rw [HodgeMetric.recentre_zero] at h
      exact h.1 hX.2
    have hu : HodgeMetric.uncentre t ρ π t ∈ Flat.punct n a₀ 1 := by
      rwa [HodgeMetric.uncentre_self]
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt n a₀ g N Λ L U hP.2.2.1 p q _ hu
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t ρ π t') p q) t :=
      h1.comp t (HodgeMetric.contDiff_uncentre t ρ π).contDiffAt
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [pgt e i t L π ρ U hP t hu] with t' ht'
    rw [ht']
  have hlog : ∀ e, ∀ t₀ : Fin n → ℂ, ‖t₀‖ ≤ 1 / 2 →
      ∃ l₁, InFrameDomain y (ch l₁) (fr l₁) ((χ e).γ t₀) ∧
      ∃ ε > (0 : ℝ), ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 →
        (χ e).γ t ∈ mcPts (mCoordIdeal y) \ Bd → InFrameDomain y (ch l₁) (fr l₁) ((χ e).γ t) →
        ((gr l₁ ((χ e).γ t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
        (((C * (χ e).logR t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
          (gr l₁ ((χ e).γ t))⁻¹).PosSemidef ∧
        ∀ p q, ‖fderiv ℝ (fun t' => gr l₁ ((χ e).γ t') p q) t‖ ≤
          C * Real.exp ((χ e).logR t / 2) := by
    intro e t₀ ht₀
    have htb : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff]
      linarith
    obtain ⟨i, hi⟩ := hcov _ ((χ e).mem t₀ htb)
    obtain ⟨a₀, g, Λ, _, L, π, ρ, U, hP⟩ := per e i t₀ htb hi
    obtain ⟨ε, c₀, C, hε, hερ, hc₀, hC, hb⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred n a₀ g N (χ e).a Λ L U t₀ π ρ hP.1 hP.2.1 hP.2.2.1
      hP.2.2.2.1 hP.2.2.2.2.1
    refine ⟨i, hi, ε, hε, c₀, hc₀, C, hC, fun t ht ht1 hX hd => ?_⟩
    have hub := HodgeMetric.uncentre_mem_ball hP.1 π (ht.trans_le hερ)
    have hcl := hP.2.2.2.2.2 _ hub
    rw [HodgeMetric.recentre_uncentre t₀ hP.1 π t] at hcl
    have hu := hcl.2.2.1.1 hX.2
    have hev := pgt e i t₀ L π ρ U hP t hu
    have h1 : gr i ((χ e).γ t) = HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t) := hev.self_of_nhds
    obtain ⟨b1, b2, b3⟩ := hb t ht ht1 hu
    rw [h1]
    refine ⟨b1, b2, fun p q => ?_⟩
    have h2 : (fun t' => gr i ((χ e).γ t') p q) =ᶠ[nhds t]
        fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q := by
      filter_upwards [hev] with t' ht'
      rw [ht']
    rw [h2.fderiv_eq]
    exact b3 p q
  exact ⟨{ m := m, chart := ch, fr := fr, b := bb, isFrame := hfr, gram := gr
           cover := fun w hw => hcov w hw.1
           posDef := fun i w hw hd => by
             obtain ⟨z, hz⟩ := pts w hw.1
             exact (key i z w hz (intr z w hz hw.2) hd).2
           compat := hcompat, torus := htorus, conj := hconj, smooth := hsmooth, logBound := hlog },
    fun e z w hw hi hd => (key e z w hw hi hd).1⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebra
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

noncomputable def baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    pullback (π ≫ p) f ⟶ pullback p f :=
  pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _) (by simp [pullback.condition])

theorem baseMap_snd {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    baseMap π p f ≫ pullback.snd p f = pullback.snd (π ≫ p) f :=
  pullback.lift_snd _ _ _

theorem baseMap_isPullback {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S) :
    IsPullback (baseMap π p f) (pullback.fst (π ≫ p) f) (pullback.fst p f) π := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p f) (h₂₂ := p) (v₁₃ := f) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p f).flip
  rw [baseMap_snd]
  exact (IsPullback.of_hasPullback (π ≫ p) f).flip

theorem isProper_snd_comp {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    [IsProper π] [IsProper (pullback.snd p f)] : IsProper (pullback.snd (π ≫ p) f) := by
  have : IsProper (baseMap π p f) :=
    MorphismProperty.of_isPullback (P := @IsProper) (baseMap_isPullback π p f).flip inferInstance
  rw [← baseMap_snd π p f]
  infer_instance

theorem isProper_snd_of_comp {X S T T' : Scheme.{0}} (q : X ⟶ S) (f : T ⟶ S) (h : T' ⟶ T)
    [IsProper (pullback.snd q f)] : IsProper (pullback.snd q (h ≫ f)) := by
  let g : pullback q (h ≫ f) ⟶ pullback q f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ h) (by simp [pullback.condition])
  have hg : g ≫ pullback.fst q f = pullback.fst q (h ≫ f) :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback g (pullback.snd q (h ≫ f)) (pullback.snd q f) h := by
    refine IsPullback.of_right (h₁₂ := pullback.fst q f) (h₂₂ := f) (v₁₃ := q) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback q f)
    rw [hg]
    exact IsPullback.of_hasPullback q (h ≫ f)
  exact MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance

theorem mem_range_baseMap {Y X S T : Scheme.{0}} (π : Y ⟶ X) (p : X ⟶ S) (f : T ⟶ S)
    (x : ↥(pullback p f)) (h : pullback.fst p f x ∈ Set.range π) :
    x ∈ Set.range (baseMap π p f) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst p f) (g := π) x y hy.symm
  have hpb := baseMap_isPullback π p f
  refine ⟨hpb.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz]

theorem isProper_descends (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V]
    (X : Scheme.{0}) (p : X ⟶ Sp k) (hs : IsSeparated p) (hl : LocallyOfFiniteType p)
    (hq : QuasiCompact p) (hP : IsProper (pullback.snd p (spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  obtain ⟨n, Y, π, hπ, hcov⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.exists_proper_qproj_cover k X p hs hl hq
  have hi : ∀ i, ∃ R : Subalgebra k V, R.FG ∧
      IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := (hπ i).1
    exact GlobalTheory.T.properness_descends_fg_subalgebra k V (Y i) (π i ≫ p) (hπ i).2 (isProper_snd_comp (π i) p _)
  choose Ri hRfg hRp using hi
  let R : Subalgebra k V := Finset.univ.sup Ri
  have hFG : R.FG :=
    Finset.sup_induction (p := Subalgebra.FG) Subalgebra.fg_bot (fun _ h _ h' => h.sup h')
      (fun i _ => hRfg i)
  refine ⟨R, hFG, ?_⟩
  have hle : ∀ i, Ri i ≤ R := fun i => Finset.le_sup (Finset.mem_univ i)
  have hmap : ∀ i, spMap (algebraMap k R) =
      spMap (Subalgebra.inclusion (hle i)).toRingHom ≫ spMap (algebraMap k (Ri i)) := by
    intro i
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hprop : ∀ i, IsProper (pullback.snd (π i ≫ p) (spMap (algebraMap k R))) := by
    intro i
    have := hRp i
    rw [hmap i]
    exact isProper_snd_of_comp _ _ _
  refine GlobalTheory.T.proper_of_proper_cover (pullback p (spMap (algebraMap k R))) (Sp R)
    (pullback.snd p (spMap (algebraMap k R))) n
    (fun i => pullback (π i ≫ p) (spMap (algebraMap k R)))
    (fun i => baseMap (π i) p (spMap (algebraMap k R))) inferInstance inferInstance ?_ ?_
  · intro i
    rw [baseMap_snd]
    exact hprop i
  · intro x
    obtain ⟨i, hi⟩ := hcov (pullback.fst p (spMap (algebraMap k R)) x)
    exact ⟨i, mem_range_baseMap _ _ _ x hi⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

