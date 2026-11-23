module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalHermitianFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricHeightBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0198
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0181
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0245
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0030
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0059
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0055
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0053
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeUnif

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

theorem exists_compare {S S₁ : Scheme.{0}} {f : S₁ ⟶ S} {A A' : Over S₁} {C : Over S} [GrpObj A] [GrpObj A'] [GrpObj C]
    {a : A.left ⟶ C.left} {a' : A'.left ⟶ C.left} (hA : IsGrpPullback A C f a) (hA' : IsGrpPullback A' C f a') :
    ∃ w : A.left ⟶ A'.left, w ≫ a' = a ∧ w ≫ A'.hom = A.hom ∧ IsGrpPullback A A' (𝟙 S₁) w := by
  refine ⟨hA'.1.lift a A.hom hA.1.w, hA'.1.lift_fst _ _ _, hA'.1.lift_snd _ _ _, ?_⟩
  refine IsGrpPullback.cancel hA' ?_ ?_
  · rw [hA'.1.lift_fst, Category.id_comp]; exact hA
  · rw [hA'.1.lift_snd, Category.comp_id]

theorem slope_unif : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  intro hN hP hR hH hS E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨K₀, hK₀, hQ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.QuotUnif.main hR E H D l Xo c Y S Ω K J y 𝔐 h hpq
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨C₁, hC₁, hT⟩ := GlobalTheory.T.semiabelian_lie_metric_height hH 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.t.semi 𝔐.Li 𝔐.M h
  obtain ⟨C₀, hC₀, hSl⟩ := hS
  obtain ⟨Cc, hCc1, hCcK, hCc₁, hCc₀⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ K₀ ≤ Cc ∧ C₁ ≤ Cc ∧ C₀ ≤ Cc :=
    ⟨max (max K₀ C₁) (max C₀ 1), by simp, by simp, by simp, by simp⟩
  obtain ⟨C', hC', hPB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PtBoundary.slopeMax_le_log (Module.finrank Ω 𝔐.Li) Cc hCc1
  refine ⟨C', hC', fun L₀ _ _ z₀ => ?_⟩
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.abPart_exists E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (_root_.GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m'⟩, ⟨mP⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SabModel.exists_sab_model hN hP E H L₁ P₁.tB hpr
    (_root_.GlobalTheory.CompanionTheory.Ar.AbPartConst.lieMult_constant_along_cmType E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  have hprK : IsPrincipal tK := (_root_.GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field E H L₁ L e₂ P₁.tB tK mP).2 hpr
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, fun B MB hB => ?_⟩
  have hz : spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀) =
      spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  obtain ⟨B', MB', hB'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeFibre.exists_hermitianBundle E H L t' tK m' hprK
  have hslope := hSl E H L t' tK m' hprK B' MB' hB'
  obtain ⟨P₂, mK2, mB2, c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
  obtain ⟨w, hw, hw', hwp⟩ := exists_compare mB2.cart mP.cart
  letI := P₂.τ.addCommGroup
  letI := P₂.τ.grpB
  haveI := P₂.e_hom
  have hφ' : IsGrpPullback P₂.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P₂.e.hom.left ≫ w ≫ m'.φ) := by
    have := (isGrpPullback_iso P₂.e).comp (hwp.comp m'.cart)
    simpa using this
  obtain ⟨MT, hMT⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus (Sp L) P₂.τ.X L (𝟙 _)
  have hcart : IsGrpPullback P₂.tK.G 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀)) P₂.m.φ := by
    rw [hz]; exact P₂.m.cart
  obtain ⟨r, bs, hbs⟩ := hT L _ P₂.tK.G P₂.m.φ P₂.τ hcart
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension 𝔐.X 𝔐.t.G 𝔐.t.semi L _ P₂.tK.G P₂.m.φ P₂.τ t'.G _ t'.semi hcart hφ'
    MT hMT B.carrier B'.carrier MB MB' r bs
  have hbd := hbs MT hMT B MB hB ε hε
  have hnb := _root_.GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le E H 𝔐.X 𝔐.t L₁ L e₂ _ _ hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h K₀
    (fun zc P v v₀ c => (hQ zc P).2 v v₀ c) B B' MB MB' hB hB' f hf
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hrk := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finrank_eq 𝔐.X Ω 𝔐.ξ 𝔐.all 𝔐.t.G 𝔐.Li 𝔐.M L _ B.carrier MB
  have hC₁0 : (0 : ℝ) < C₁ := by linarith
  have hCc0 : (0 : ℝ) < Cc := by linarith
  refine hPB L B B' r ε f hrk hli hker hsur ?_ ?_ ?_
  · intro σ u
    have hs : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    obtain ⟨h₁, h₂⟩ := hbd σ u
    refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ hs) h₁, h₂.trans (mul_le_mul_of_nonneg_right hCc₁ hs)⟩
    exact inv_anti₀ hC₁0 hCc₁
  · intro σ x
    have h0 : 0 ≤ sqAt B σ x := by
      have := (B.metric.form σ).re_inner_nonneg x
      simpa [sqAt] using this
    exact (hnb σ x).trans (mul_le_mul_of_nonneg_right hCcK h0)
  · refine hslope.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hCc₀ (Real.log_nonneg ?_)))
    have : (0 : ℝ) ≤ max (-B'.normDegree ⊤) 0 := le_max_right _ _
    have h' : (0 : ℝ) ≤ Module.finrank (𝓞 L) B'.carrier := Nat.cast_nonneg _
    linarith

end GlobalTheory.CompanionTheory.Ar.SlopeUnif
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeIPOfFibreLatVec
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric

theorem isPsh_half {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (h : IsPsh U f) :
    IsPsh U (fun z => f z / 2) := by
  refine ⟨fun z hz y hy => ?_, fun z w hd => ?_⟩
  · have h1 : ∀ᶠ x in 𝓝[U] z, f x < 2 * y := h.1 z hz (2 * y) (by simp only at hy; linarith)
    filter_upwards [h1] with x hx
    linarith
  · obtain ⟨h1, h2⟩ := h.2 z w hd
    have e : Real.circleAverage (fun ζ : ℂ => f (z + ζ • w) / 2) 0 1 =
        Real.circleAverage (fun ζ : ℂ => f (z + ζ • w)) 0 1 / 2 := by
      have := Real.circleAverage_fun_smul (c := 0) (R := 1) (a := (1 / 2 : ℝ)) (f := fun ζ : ℂ => f (z + ζ • w))
      simp only [smul_eq_mul] at this
      rw [show (fun ζ : ℂ => f (z + ζ • w) / 2) = fun ζ : ℂ => 1 / 2 * f (z + ζ • w) by
        funext ζ; ring, this]
      ring
    refine ⟨?_, ?_⟩
    · have : CircleIntegrable ((1 / 2 : ℝ) • fun ζ : ℂ => f (z + ζ • w)) 0 1 := h1.const_smul
      refine (circleIntegrable_congr (fun ζ _ => ?_)).1 this
      simp [div_eq_inv_mul]
    · rw [e]; linarith

def aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def affInv {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  ((ρ : ℂ)⁻¹ • (t - t₀)) ∘ π.symm

theorem aff_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    aff t₀ ρ π (affInv t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [aff, affInv, Function.comp, h]

theorem norm_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) {t : Fin n → ℂ}
    (ht : t ∈ ball t₀ ρ) : affInv t₀ ρ π t ∈ ball 0 1 := by
  rw [mem_ball, dist_eq_norm, sub_eq_add_neg] at ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖(t - t₀) (π.symm i)‖ < ρ := by
    have : ‖t + -t₀‖ < ρ := ht
    rw [pi_norm_lt_iff hρ] at this
    simpa [sub_eq_add_neg] using this (π.symm i)
  simp only [affInv, Function.comp, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ]
  rw [inv_mul_lt_iff₀ hρ]
  simpa using h1

theorem affInv_add {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (z w : Fin n → ℂ) (ζ : ℂ) :
    affInv t₀ ρ π (z + ζ • w) = affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) := by
  funext i
  simp [affInv, Function.comp]
  ring

theorem isPsh_comp_affInv {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    {ψ : (Fin n → ℂ) → ℝ} (h : IsPsh (ball 0 1) ψ) : IsPsh (ball t₀ ρ) (fun t => ψ (affInv t₀ ρ π t)) := by
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  refine ⟨h.1.comp (g := affInv t₀ ρ π) hc.continuousOn (fun t ht => norm_affInv t₀ hρ π ht), fun z w hd => ?_⟩
  have hd' : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm) ∈ ball 0 1 := by
    intro ζ hζ
    rw [← affInv_add]
    exact norm_affInv t₀ hρ π (hd ζ hζ)
  have e : (fun ζ : ℂ => ψ (affInv t₀ ρ π (z + ζ • w))) =
      fun ζ : ℂ => ψ (affInv t₀ ρ π z + ζ • (((ρ : ℂ)⁻¹ • w) ∘ π.symm)) := by
    funext ζ; rw [affInv_add]
  simp only [e]
  exact h.2 _ _ hd'

theorem exists_log_norm {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀) (h0 : F t₀ ≠ 0) :
    ∃ r > (0 : ℝ), ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ball t₀ r) ∧
      ∀ t ∈ ball t₀ r, Real.log ‖F t‖ = (G t).re + Real.log ‖F t₀‖ := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have h1 : ∀ᶠ t in 𝓝 t₀, F t / F t₀ ∈ Complex.slitPlane := by
    have : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
    exact hH.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds this)
  have h2 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ (fun t => F t / F t₀) t := hH.eventually_analyticAt
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨r, hr, fun t => Complex.log (F t / F t₀), fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hb t ht).2.differentiableAt.clog (hb t ht).1).differentiableWithinAt
  · have hne : F t / F t₀ ≠ 0 := Complex.slitPlane_ne_zero (hb t ht).1
    have hFt : F t ≠ 0 := fun h => hne (by simp [h])
    rw [Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hFt) (norm_ne_zero_iff.2 h0)]
    ring

theorem analyticAt_eval {A : Type} {n : ℕ} {q : (Fin n → ℂ) → A → ℂ} {t₀ : Fin n → ℂ}
    (hq : ∀ i, AnalyticAt ℂ (fun t => q t i) t₀) (p : MvPolynomial A ℤ) :
    AnalyticAt ℂ (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) t₀ := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p r hp hr =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p + r))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) +
          fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) r) := by
      funext t; simp
    rw [e]; exact hp.add hr
  | mul_X p i hp =>
    have e : (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) (p * MvPolynomial.X i))) =
        (fun t => MvPolynomial.eval (q t) (MvPolynomial.map (Int.castRingHom ℂ) p)) * fun t => q t i := by
      funext t; simp
    rw [e]; exact hp.mul (hq i)


open scoped ComplexOrder in
theorem gram_det_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) (hu : LinearIndependent ℂ u) :
    0 < (R.gram u).det.re := by
  have hH : (R.Hmᵀ).IsHermitian := by
    ext i j
    exact R.herm.apply j i
  have hM : (R.Hmᵀ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    have h1 := R.pos x hx
    have e : star x ⬝ᵥ (R.Hmᵀ *ᵥ x) = x ⬝ᵥ R.Hm *ᵥ star x := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    have him : (star x ⬝ᵥ (R.Hmᵀ *ᵥ x)).im = 0 := hH.im_star_dotProduct_mulVec_self x
    rw [Complex.pos_iff]
    exact ⟨by rw [e]; exact h1, him.symm⟩
  let C : Matrix (Fin g) (Fin m) ℂ := (Matrix.of u)ᵀ
  have hC : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hu
  have e : R.gram u = Cᴴ * R.Hmᵀ * C := by
    ext a b
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.conjTranspose_apply, Matrix.transpose_apply, Pi.star_apply, C]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hp := (hM.conjTranspose_mul_mul_same hC).det_pos
  rw [← e] at hp
  exact (Complex.pos_iff.1 hp).1

theorem hodgeInnerProduct_of_fibreLatticeVector {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem isOpen_offBd (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts) : IsOpen (offBd D a) := by
  have e : offBd D a = ball 0 1 ∩ ⋂ i : Fin (Fintype.card Ψ * D.j * (D.N - D.j)),
      {t | (i : ℕ) < (D.chart a).a → t i ≠ 0} := by
    ext t
    simp only [offBd, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun ht => ?_
    rw [(D.chart a).boundary t ht]
    push_neg
    rfl
  rw [e]
  refine isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : (i : ℕ) < (D.chart a).a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

end Free

end GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HtatLinkOf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem htat_link_of (h758 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.ChartEx.htChartExists) (h576 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.HT.hasTestPoints_of_tate) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)), ∃ (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc ∧ ∀ (s : {s : ∀ k, J k // mseg y s ≠ 0}) (κ : chartRing o (mseg y) s.1), PointHT → IsCp p (κ : Ω) → (Dc s).HasTestPoints κ := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS hpq o _ _ ho
  obtain ⟨h0, hN, hprop, hT, hrk, -, hch⟩ := Hcptgen.hcpt_generic E H D l Xo c O β Y S Ω K J y 𝔐 p hpS o ho
  have hp := (Fact.out : p.Prime)
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.ne_zero
  obtain ⟨ev, ζ₀, hev⟩ := exists_isParam D 𝔐.t 𝔐.ξ level_param (p ^ 𝔐.R p) (Nat.pos_of_ne_zero hn) hpq hprop
    (𝔐.tors p hpS) hT
  obtain ⟨u, hu⟩ := pol_lattice E H D p
  obtain ⟨π, e, hπ, he, hdec, hsurj, hker, halt, hadj, hes, hei⟩ :=
    exists_levPairing (cmConj E) p (𝔐.R p) D.EF u hu
  have key : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0},
      ∃ Dc : HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li), Dc.e = e ∧
      (∀ a w, Dc.ρΩ a w = w ∘ₗ 𝔐.ρ (H.bar a)) ∧
      (∀ w, w ∈ Dc.om ↔ ∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q →
        𝔐.M.omLat q = Submodule.span (regAt 𝔐.ξ q) (Dc.om : Set (Module.Dual Ω 𝔐.Li))) ∧
      (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → OverZp 𝔐 p q → ∀ z w',
        𝔐.M.IsHTAt 𝔐.t.PP.L (p ^ 𝔐.R p) (ev (∑ k, z k • u k)) q w' ↔
          ∃ v ∈ 𝔐.M.omLat q, w' = Dc.h z + (p ^ 𝔐.R p) • v) ∧
      ∀ κ : chartRing o (mseg y) s.1, PointHT → IsCp p (κ : Ω) → Dc.HasTestPoints κ := by
    intro s
    obtain ⟨_, _, _, x, hx, hr⟩ := hch s.1 s.2
    obtain ⟨Dc, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.CompanionTheory.HtLink.exists_chart Twhopf.sec_inj Twexists.exists_torsion' h758 h576 D 𝔐.t 𝔐.ξ 𝔐.tie.gen 𝔐.all 𝔐.M 𝔐.ρ 𝔐.act
      p (𝔐.R p) hev hprop (𝔐.tors p hpS) hrk u hu π e hπ he hsurj hker halt hadj hes hei (chartRing o (mseg y) s.1) x hx
      (fun q hq => chart_le_regAt 𝔐 p o ho s.1 q ((hr q).1 hq).1 ((hr q).1 hq).2)
    exact ⟨Dc, h1, h2, fun w => (h3 w).trans ⟨fun h q a b => h q ((hr q).2 ⟨a, b⟩),
      fun h q hq => h q ((hr q).1 hq).1 ((hr q).1 hq).2⟩, fun q a b => h4 q ((hr q).2 ⟨a, b⟩),
      fun q a b => h5 q ((hr q).2 ⟨a, b⟩), h6⟩
  choose Dc h1 h2 h3 h4 h5 h6 using key
  refine ⟨Dc, ⟨h2, fun s t => (h1 s).trans (h1 t).symm, h3, h4, fun s q hs hq => ?_, fun s t q hs ht hq z => ?_⟩, h6⟩
  · have hz := ModelTest.overZp_of_inFibre 𝔐 hp q hq
    have hpow : ∀ w : Module.Dual Ω 𝔐.Li, ((p : chartRing o (mseg y) s.1) ^ 𝔐.R p) • w = (p ^ 𝔐.R p) • w := fun w => by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    have hsub := chart_le_regAt 𝔐 p o ho s.1 q hs hz
    have hmem : ∀ z, ∀ v ∈ 𝔐.M.omLat q, (Dc s).h z + (p ^ 𝔐.R p) • v ∈ omP 𝔐 p q := fun z v hv =>
      Submodule.subset_span ⟨_, (hev.onto _).2 ⟨_, rfl⟩, (h5 s q hs hz z _).2 ⟨v, hv, rfl⟩⟩
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨g, hg, hw⟩
      obtain ⟨a, rfl⟩ := (hev.onto g).1 hg
      obtain ⟨z, b, rfl⟩ := hdec a
      rw [hev.add, (hev.ker _).2 ⟨b, rfl⟩, _root_.mul_one] at hw
      obtain ⟨v, hv, rfl⟩ := (h5 s q hs hz z w).1 hw
      refine add_mem (Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨z, rfl⟩))) ?_
      rw [h4 s q hs hz] at hv
      clear hw
      induction hv using Submodule.span_induction with
      | mem v hv => exact Submodule.subset_span (Submodule.mem_sup_right ⟨v, hv, hpow v⟩)
      | zero => simp
      | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
      | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
    · obtain ⟨w₁, hw₁, _, ⟨w₂, hw₂, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
      refine add_mem ?_ ?_
      · clear hw
        induction hw₁ using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨z, rfl⟩ := hv
          simpa using hmem z 0 (zero_mem _)
        | zero => exact zero_mem _
        | add v v' _ _ h h' => exact add_mem h h'
        | smul r v _ h => exact Submodule.smul_mem (omP 𝔐 p q) ⟨_, hsub r⟩ h
      · have := hmem 0 w₂ (((h3 s w₂).1 hw₂) q hs hz)
        rw [map_zero, zero_add, ← hpow] at this
        exact this
  · exact (h5 t q ht hq z _).1 ((h5 s q hs hq z _).2 ⟨0, zero_mem _, by simp⟩)

end GlobalTheory.CompanionTheory.HtLink
end
end

