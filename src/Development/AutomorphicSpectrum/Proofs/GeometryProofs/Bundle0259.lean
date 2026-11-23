module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0257
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0071
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusStableSncCharts
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0221
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataIntersectionSum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0258

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace TopMean

theorem bracket_le (f j' B : ℕ) (rd L : ℝ) (hrd : 2 ≤ rd) (hf : 1 ≤ f) (hj : 1 ≤ j')
    (hB : 2 * f * j' ≤ B) (hB64 : 64 ≤ B) :
    6 + Real.log (2 * (f : ℝ) * rd) + Real.log (2 * (f : ℝ) * j' * rd) ≤
      4 * (Real.log ((B : ℝ) * rd) + |L|) := by
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hj' : (1 : ℝ) ≤ j' := by exact_mod_cast hj
  have hB' : 2 * (f : ℝ) * j' ≤ B := by exact_mod_cast hB
  have hB64' : (64 : ℝ) ≤ B := by exact_mod_cast hB64
  have hrd0 : 0 < rd := by linarith
  have h1 : Real.log (2 * (f : ℝ) * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right _ hrd0.le
    nlinarith
  have h2 : Real.log (2 * (f : ℝ) * j' * rd) ≤ Real.log ((B : ℝ) * rd) := by
    apply Real.log_le_log (by positivity)
    exact mul_le_mul_of_nonneg_right hB' hrd0.le
  have h3 : 3 ≤ Real.log ((B : ℝ) * rd) := by
    have h128 : (128 : ℝ) ≤ (B : ℝ) * rd := by nlinarith
    have hl : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) h128
    have := Real.log_two_gt_d9
    linarith
  have := abs_nonneg L
  linarith

end TopMean


open TopMean in
theorem top_mean_cusp_weight : Top.Given → ∃ Cu : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → MeanU Hd U Cu (hostRd E) (hostLval H) := by
  intro hG
  refine ⟨4, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U _ _ hU
  obtain ⟨Q⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.pieces_nonempty hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨κ, hκ, htr⟩ := GlobalTheory.T.ptsIntegral_eq_sum_ballDens_integrals E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q
  have hw := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet.cuspWeight_torus_and_sheets E H D Xo l c Y II K J Ω W Dc Hd S₀ Or Q U hU
  obtain ⟨hrd, ⟨τ₀⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  intro hj' hN B hB
  have hjN : Dc.j + Dc.j' = Dc.N := by
    have := Dc.j_le; have := Dc.two_le_N
    show Dc.j + (Dc.N - Dc.j) = Dc.N
    omega
  have hball := fun k => _root_.GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW E (CMType H) Dc.j Dc.j' Dc.n Q.g (Q.Λ k) H (Q.F k) (Q.Γ k) (Q.FF k)
    (Q.arith k) (Q.fund k) hj' (by omega)
  set C : ℝ := (Fintype.card (CMType H) : ℝ) * Dc.j' * (6 + Real.log (2 * Fintype.card (CMType H) * hostRd E) +
    Real.log (2 * Fintype.card (CMType H) * Dc.j' * hostRd E)) with hC
  have hdeg : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t := by
    have e1 : GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd =
        ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) (fun _ => 1) := rfl
    rw [e1, htr (fun _ => 1) (fun _ _ => 1) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun k => by simpa using (hball k).1)]
    refine congrArg (κ * ·) (Finset.sum_congr rfl fun k _ => ?_)
    simp
  have hnum : ptsIntegral (e := Dc.n) (mCoordIdeal Dc.y) (fun _ => phMu Hd) U =
      κ * ∑ k, (Q.d k : ℝ) * ∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t :=
    htr U (fun k t => ((Q.F k).R t).cuspW (Q.F k).σ) hw.1 hw.2 (fun k => (hball k).2.2.1)
  have hle : ∀ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t) ≤
      C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) := fun k => by
    have h := mul_le_mul_of_nonneg_left (hball k).2.2.2 (Nat.cast_nonneg (α := ℝ) (Q.d k))
    calc _ ≤ _ := h
      _ = _ := by rw [hC]; ring
  have hDpos : 0 < GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
    rw [hdeg]
    apply mul_pos hκ
    obtain ⟨k0, hk0⟩ := Q.d_pos
    exact Finset.sum_pos' (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hball k).2.1.le)
      ⟨k0, Finset.mem_univ _, mul_pos (by exact_mod_cast hk0) (hball k0).2.1⟩
  have hmean : meanOf Hd U ≤ C := by
    unfold meanOf
    rw [div_le_iff₀ hDpos, hnum]
    calc κ * ∑ k, (Q.d k : ℝ) * (∫ t in Q.FF k, ((Q.F k).R t).cuspW (Q.F k).σ * ballDens (Q.F k).q t)
        ≤ κ * ∑ k, C * ((Q.d k : ℝ) * ∫ t in Q.FF k, ballDens (Q.F k).q t) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) hκ.le
      _ = C * GroundTheory.Heights₂.Heights.LowerBoundFree.degMu Hd := by
          rw [hdeg, ← Finset.mul_sum]; ring
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hfD : Dc.f = Fintype.card (CMType H) := rfl
  have hN4 : 4 ≤ Dc.N := by omega
  have hB64 : 64 ≤ B := by
    have : 4 * 1 * 4 ^ 2 ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]; gcongr
    omega
  have hB2 : 2 * Fintype.card (CMType H) * Dc.j' ≤ B := by
    have hjN' : Dc.j' ≤ Dc.N ^ 2 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have : 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Dc.f * Dc.N ^ 2 := by
      rw [hfD]
      calc 2 * Fintype.card (CMType H) * Dc.j' ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2 := by
            have := Nat.mul_le_mul_left (4 * Fintype.card (CMType H)) hjN'
            nlinarith
        _ = _ := rfl
    omega
  have hbr := bracket_le (Fintype.card (CMType H)) Dc.j' B (hostRd E) (hostLval H) hrd hf hj' hB2 hB64
  have hfj : (0 : ℝ) ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' := by positivity
  calc meanOf Hd U ≤ C := hmean
    _ ≤ (Fintype.card (CMType H) : ℝ) * Dc.j' * (4 * (Real.log ((B : ℝ) * hostRd E) + |hostLval H|)) := by
        rw [hC]; exact mul_le_mul_of_nonneg_left hbr hfj
    _ = 4 * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
        rw [hfD, GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂]; ring

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 :=
  _root_.UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero H

theorem tauIn_rt_eq (τ : E →+* ℂ) (σ : c.F →+* ℂ) :
    σ (tauIn c τ H.rt) = H.rt0 ∨ σ (tauIn c τ H.rt) = -H.rt0 := by
  have h : (σ (tauIn c τ H.rt)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, H.sqrt_neg_disc_sq]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem gram_det_ne_zero {τ : E →+* ℂ} {σ : c.F →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    {y : Sp ℂ ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {Γ : Matrix (Fin D.p) (Fin D.p) ℂ}
    (hf : IsFramed Set.univ τ σ y v w) (hΓ : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ) :
    Γ.det ≠ 0 := by
  have hs : under y ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hf.1, ← Spec.map_comp]; rfl
  obtain ⟨i, P, hP, hu⟩ := FU.onto _ hs
  obtain ⟨V, hV, hli, -⟩ := exists_directions_of_isEigFrame E H D l Xo _ g ty FU i P (under y)
    (σ.comp (tauIn c τ)) (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) D.p v hP hu.symm (fun a => rfl)
    hf.2.2.1
  obtain ⟨Hm, hH, hpos, him⟩ := hP.2.2.2.2
  have hG := (hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hH him (under y) hu.symm D.p v V Γ
    (fun a => (hV a (V a)).2 rfl)).1 hΓ
  let M : Matrix (Fin D.p) (Fin g) ℂ := Matrix.of V
  have hΓM : Γ = (Real.pi : ℂ) • (M * Hm * M.conjTranspose) := by
    ext a b
    rw [hG a b, Matrix.smul_apply, smul_eq_mul]
    congr 1
    simp only [hermForm, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, M,
      Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set z := Matrix.vecMul (star x) M with hz
  have hq : dotProduct (star x) (Γ.mulVec x) = (Real.pi : ℂ) * hermForm Hm z z := by
    rw [hΓM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hermForm, hz, Matrix.star_vecMul, star_star,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [hx, dotProduct_zero] at hq
  have hz0 : z = 0 := by
    by_contra hne
    have := hpos z hne
    have h2 : (hermForm Hm z z) = 0 := by
      rcases mul_eq_zero.1 hq.symm with h | h
      · exact absurd h (by exact_mod_cast Real.pi_ne_zero)
      · exact h
    rw [h2] at this; simp at this
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.2 hli
  have : star x = 0 := hinj (show Matrix.vecMul (star x) M = Matrix.vecMul 0 M by rw [← hz, hz0, Matrix.zero_vecMul])
  exact hx0 (by simpa using this)

theorem exists_infNorm_of_rt (hR : Geo.ResK.ResKStatement) (hG : GagaSections) {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {τ : E →+* ℂ} {φ : FrameFn Xo c}
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hr : 1 ≤ D.p + D.q) (hτ : τ (H.rt : E) = H.rt0) (hZ : Z.IsGeom) (hl : IsLineFn U τ φ)
    (hm : FlatOnModel Z τ φ) (σ : c.F →+* ℂ) (hσ : σ (tauIn c τ H.rt) = H.rt0) :
    ∃ t : ℝ, HasInfNorm U τ φ σ t := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hK : (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
    have e : (IntermediateField.inclusion c.le) (baseKA l).ρ = tauIn c τ H.rt :=
      Subtype.ext (show H.rt0 = τ (H.rt : E) from hτ.symm)
    show σ ((IntermediateField.inclusion c.le) (baseKA l).ρ) = H.rt0
    rw [e, hσ]
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws _root_.GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo _ g ty hr hK hty
  obtain ⟨Φ, hΦ, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.anUnit E H D l Xo c τ (σ.comp (τ.codRestrict c.F.toSubfield (c.conj τ))) σ g ty FU
    hty hσ (fun a => rfl)
  obtain ⟨κ, hκ0, hκ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O β Y U Z τ σ Φ φ hβ hr hτ hσ hZ hΦ hl hm
  refine ⟨Real.log ‖κ‖, fun y v w Γ Δ hf h1 h2 => ?_⟩
  have hf' : IsFramed Set.univ τ σ y v w := ⟨hf.1, Set.subset_univ _, hf.2.2⟩
  have hΓ : ‖Γ.det‖ ≠ 0 := norm_ne_zero_iff.2 (gram_det_ne_zero FU hf' h1)
  have hΦ0 : ‖Φ y v w‖ ≠ 0 := norm_ne_zero_iff.2 (hΦ.ne y v w hf')
  have hn := congrArg Real.log (hΦ.norm y v w Γ Δ hf' h1 h2)
  rw [Real.log_mul (pow_ne_zero 2 hΦ0) hΓ, Real.log_pow] at hn
  rw [hκ y v w hf, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hκ0) hΦ0]
  push_cast at hn
  linarith

theorem flat_first_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → FlatLineGeneratorComponent := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y U Z τ φ hβ hr hτ hZ hl hm
  have key : ∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t := by
    intro s
    rcases tauIn_rt_eq (c := c) (H := H) τ s with h | h
    · exact exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm s h
    · obtain ⟨t, ht⟩ := exists_infNorm_of_rt hR hG Z hβ hr hτ hZ hl hm ((starRingEnd ℂ).comp s)
        (by rw [RingHom.comp_apply, h, map_neg, rt0_conj_neg_ne_zero, neg_neg])
      refine ⟨t, ?_⟩
      have := _root_.GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj E H D l Xo c U τ φ _ t hl ht
      rwa [show (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s from RingHom.ext fun x => by simp] at this
  refine ⟨fun s => ?_, fun g ty FU i hty hmem => ?_⟩
  · obtain ⟨t, ht⟩ := key s
    exact ⟨t, ht, _root_.GlobalTheory.CompanionTheory.Ar.Flat.hasInfNorm_conj E H D l Xo c U τ φ s t hl ht⟩
  · obtain ⟨Φ, hΦ, hfl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.anUnit E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun a => rfl)
    obtain ⟨κ, -, hκ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O β Y U Z τ (algebraMap c.F ℂ) Φ φ hβ hr hτ hτ hZ hΦ hl hm
    obtain ⟨e, ρ, -, he, hρ⟩ := hfl i
    refine ⟨hmem, hl, e, κ * ρ, he, ?_⟩
    intro P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8
    rw [hκ y v w h3, _root_.mul_assoc, hρ P y v w V W C Fm B h1 h2 ⟨h3.1, Set.subset_univ _, h3.2.2⟩ h4 h5 h6 h7 h8]

end GlobalTheory.CompanionTheory.Ar.Flat.FlatFirstTheorem
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_zero_from_resolution_and_gaga : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.Flat.GagaSections → GlobalTheory.CompanionTheory.Ar.Flat.FlatLineGenerator := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | exact GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.A0.flat_zero_of_resolution_gaga <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionGenericBound
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_componentData_origin : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem), IsFullIntersectionSystem II → Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sw : Bool), (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : Algebra ℚ Ω) (W : CMType H → Type) (_ : ∀ τ, AddCommGroup (W τ)) (_ : ∀ τ, Module Ω (W τ)) (Dc : GroundTheory.Heights₂.Heights.LowerBoundFree.ComponentData II (CMType H) K J Ω W) (Hd : GroundTheory.Heights₂.Heights.LowerBoundFree.HodgeData Dc) (Or : CptOrigin Y S₀ Dc Hd), genPt Or.𝔐.ξ₀ = genPt ξ₀ ∧ Dc.S = S₁ ∧ Dc.j = (if sw then D.q else D.p) ∧ Or.bg = (if sw then Sum.inr else Sum.inl) ∧ Or.𝔐.OmVB ∧ ∀ p ∈ S₀ ∪ S₁, HT.HTFree Or.𝔐 p := by
  intro hG hW E _ _ _ H D Xo l c Y II hII hgl hp hq Ω₀ _ ξ₀ hξ S₀ S₁ sw hS₀ hS₁ hd hdisc
  obtain ⟨bg, sm, j, r, hbg, hj, hsmc, hr, hside, hne, hbgj, rfl, hj1, hj2⟩ :
      ∃ (bg sm : CMType H → CMType H ⊕ CMType H) (j r : ℕ),
        bg = (if sw then Sum.inr else Sum.inl) ∧ j = (if sw then D.q else D.p) ∧
        (sm = Sum.inl ∨ sm = Sum.inr) ∧ (∀ τ, labelRk D (sm τ) = r) ∧
        ((bg = Sum.inl ∧ sm = Sum.inr ∧ j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ j = D.q)) ∧
        (∀ τ, bg τ ≠ sm τ) ∧ (∀ τ, labelRk D (bg τ) = j) ∧ r = D.p + D.q - j ∧ 1 ≤ j ∧
        j ≤ D.p + D.q - 1 := by
    cases sw
    · refine ⟨Sum.inl, Sum.inr, D.p, D.q, by simp, by simp, Or.inr rfl, fun _ => rfl,
        Or.inl ⟨rfl, rfl, rfl⟩, fun _ => by simp, fun _ => rfl, by omega, hp, by omega⟩
    · refine ⟨Sum.inr, Sum.inl, D.q, D.p, by simp, by simp, Or.inl rfl, fun _ => rfl,
        Or.inr ⟨rfl, rfl, rfl⟩, fun _ => by simp, fun _ => rfl, by omega, hq, by omega⟩
  have hchart := _root_.GlobalTheory.CompanionTheory.Ar.GeoModel.exists_geo hG hW E H D Xo l c Y hgl hp hq Ω₀ ξ₀ hξ S₀ S₁ sm (D.p + D.q - j) hsmc hr hS₀ hS₁ hd hdisc
  obtain ⟨K, _, J, _, Ω, _, _, y, 𝔐, deg, bd, vdeg, vnum, vden, s, aMu, e₀, hK, hgen, hcov, hom, hfree,
    htr, hsnc, hbd, hR, htors, hvb, hvert, hvert2, hli, hspan, hdeg⟩ :=
    hchart
  have hn : D.dim = Fintype.card (CMType H) * j * (D.p + D.q - j) := by
    have h2 := (_root_.GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H).2.2
    have hmul : j * (D.p + D.q - j) = D.p * D.q := by
      rcases hside with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · rw [Nat.add_sub_cancel_left]
      · rw [Nat.add_sub_cancel, Nat.mul_comm]
    rw [Datum.dim, ← h2, Nat.mul_div_cancel_left _ (by norm_num), _root_.mul_assoc, _root_.mul_assoc, hmul]
  rw [hn] at htr hsnc
  have htie : CoordTie ℤ 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) := 𝔐.tie
  haveI := hK
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ htie htr
  obtain ⟨hcl, htor, hconj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BdSym.boundary_closed_torus_conj 𝔐.X Ω 𝔐.ξ K J y (abLocus 𝔐.t.G) bd htie hbd
  obtain ⟨nc, χ, hcov'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncCpt.exists_sncCharts K J Ω y _ bd hsnc harith htor
  obtain ⟨A, hAa, hApos, hAconj, hAh⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line II K J (mCoordIdeal y) hII
  have hLvb : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p)
      (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype).IsVB (D.p + D.q) ⊤ := fun τ => by
    have e : labelRk D (bg τ) + labelRk D (sm τ) = D.p + D.q := by
      rw [hbgj, hr]; omega
    simpa only [e] using _root_.GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup E H D l (Xo l) c Y S₀ Ω K J y 𝔐 (bg τ) (sm τ) (hne τ)
  have hWb := fun τ => _root_.GlobalTheory.CompanionTheory.Ar.exists_chartBundle_of_isVB 𝔐.X Ω 𝔐.ξ _ _ (segreCoord y) _ (D.p + D.q) htie (hLvb τ)
  choose Wb hWb using hWb
  have hbd' : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w →
      (w ∈ mcPts (mCoordIdeal y) ∩ mcPts bd ↔ ¬ 𝔐.Interior z) := fun z w h =>
    ⟨fun hw => (hbd z w h).1 hw.2,
      fun hz => ⟨(_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt 𝔐.X Ω 𝔐.ξ K J y htie w).2 ⟨z, 𝔐.all _, h⟩, (hbd z w h).2 hz⟩⟩
  have hm := fun τ => _root_.GlobalTheory.CompanionTheory.Ar.exists_hermMetric_hodge hG E H D Xo l c Y hgl S₀ Ω K J y 𝔐 (bg τ) (sm τ) (D.p + D.q) (Wb τ) _ nc _ χ
    (hLvb τ) (hWb τ) hbd'
  choose hm hgram using hm
  let Dc : ComponentData II (CMType H) K J Ω (fun τ => ↥(𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ))) :=
    { N := D.p + D.q
      j := j
      two_le_N := by omega
      one_le_j := hj1
      j_le := hj2
      F' := c.F
      finiteDimensional := c.fin
      const := 𝔐.cst
      y := y
      const_mem := fun cc hc r => _root_.GlobalTheory.CompanionTheory.Ar.CstChart.cst_mem_chart E H D l (Xo l) c Y S₀ Ω K J y 𝔐 cc hc r
      arith := harith
      birational := hbir
      smoothGeneric := GlobalTheory.T.smooth_generic_fibre_of_snc K J Ω y _ bd hsnc
      Bd := mcPts (mCoordIdeal y) ∩ mcPts bd
      bd_subset := Set.inter_subset_left
      bd_closed := hcl
      bd_torus := htor
      bd_conj := hconj
      nCharts := nc
      chart := χ
      chart_cover := hcov'
      W := Wb
      h := hm
      S := S₁
      S_prime := hS₁
      vdeg := vdeg
      vnum := vnum
      vden := vden
      vertical := hvert
      a' := fun _ => 1
      a'_pos := fun _ => one_pos
      A' := A
      A'_deg := funext hAa
      A'_pos := hApos
      A'_conj := hAconj
      KA := 0
      heights := fun W hW _ => by simpa using hAh W hW }
  obtain ⟨Hd, hF⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BigBlock.main E H D l (Xo l) c Y II K J Ω _ Dc S₀ 𝔐 bg sm
    (fun τ => (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype) s aMu e₀ (fun τ => Subtype.val_injective)
    (fun τ => Submodule.range_subtype _) hne hbgj hr hLvb hWb hli hspan hdeg
  refine ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, _, inferInstance, inferInstance, Dc, Hd,
    { 𝔐 := 𝔐
      deg := deg
      cover := hcov
      bg := bg
      sm := sm
      side := hside
      N_eq := rfl
      i := fun τ => (𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)).subtype
      i_inj := fun τ => Subtype.val_injective
      i_range := fun τ => Submodule.range_subtype _
      F_eq := hF
      lat := hWb
      bd := hbd'
      metric := fun τ e z w h1 h2 h3 => hgram τ e z w h1 h2 h3
      S_disj := hd
      R_ge := hR
      tors := htors
      ht_vb := hvb
      vert := hvert2 }, hgen, rfl, hj, hbg, hom, hfree⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_intersection_relay : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) := by
  exact @GlobalTheory.CompanionTheory.Relay.good_origin_intersection_relay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameDegreeBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_degree_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SS) → ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → (∀ (k : RM.K) (i j : RM.ι k), RM.y ⟨k, j⟩ ≠ 0 → RM.y ⟨k, i⟩ / RM.y ⟨k, j⟩ ∈ A) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → Small.ReadsRootsFin Or z (FinRd.tOf p la T e t) (Small.latExp E SS p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.reads_roots <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFiniteStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_good_primes_finite : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 :=
  @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_cover
end

