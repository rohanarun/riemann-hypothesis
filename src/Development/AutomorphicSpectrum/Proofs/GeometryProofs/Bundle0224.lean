module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModelOfIsLieBasis
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0223
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBdryChartOfHol
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GlobalTheory.CompanionTheory.Ar.Flat.BdryModel

namespace HolChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem card_eq {κ : Type} [Field κ] {G : Over (Sp κ)} [GrpObj G] [IsCommMonObj G] {n m : ℕ}
    (v : Fin n → (epsR κ ⟶ G)) (hv : IsLieBasis v) (w : Fin m → (epsR κ ⟶ G)) (hw : IsLieBasis w) : n = m := by
  obtain ⟨M⟩ := lieModel_of_isLieBasis w hw
  obtain ⟨φ⟩ := basis_of_isLieBasis v hv M
  simpa using φ.finrank_eq

theorem smoothDim_of_fibres {R : Type} [CommRing R] (t : SAB H (Sp R)) (n : ℕ)
    (hb : ∀ (κ : Type) [Field κ] (f : R →+* κ) (t₀ : SAB H (Sp κ)), SABMap t₀ t (spMap f) →
      ∃ v : Fin n → (epsR κ ⟶ t₀.G), IsLieBasis v) :
    SmoothOfRelativeDimension n t.G.hom := by
  classical
  have := t.semi.smooth
  have key : ∀ x : t.G.left, ∃ W : t.G.left.Opens, x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ t.G.hom) := by
    intro x
    obtain ⟨d, W, hx, hd⟩ := H1.exists_dim t.G.hom x
    let p : PrimeSpectrum R := t.G.hom x
    let f : R →+* p.asIdeal.ResidueField := algebraMap R _
    obtain ⟨t₀, ⟨m⟩⟩ := exists_sab (spMap f) t
    have := t₀.semi.smooth
    have := t₀.semi.geomConnected
    have : ConnectedSpace t₀.G.left := GeometricallyConnected.connectedSpace t₀.G.hom t₀.G.hom.isOpenMap
    obtain ⟨e, he⟩ := exists_dim_of_preconnected t₀.G.hom (Classical.arbitrary _)
    obtain ⟨v, hv⟩ := hb _ f t₀ m
    obtain ⟨w, hw⟩ := GlobalTheory.KeyPow.exists_isLieBasis t₀.G he
    have hne : n = e := card_eq v hv w hw
    have hpt : t.G.hom x = spMap f (default : PrimeSpectrum p.asIdeal.ResidueField) := by
      apply PrimeSpectrum.ext
      change p.asIdeal = Ideal.comap f _
      rw [show (default : PrimeSpectrum p.asIdeal.ResidueField).asIdeal = ⊥ from Ideal.eq_bot_of_prime _]
      exact (Ideal.ker_algebraMap_residueField p.asIdeal).symm
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x _ hpt
    have hax : m.cm.F (m.cart.1.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, m.cart.1.isoPullback_inv_fst, hz₁]
    have hdn := H1.dim_base m.cart.1 hd he (m.cart.1.isoPullback.inv z) (by rw [hax]; exact hx)
    exact ⟨W, hx, by rw [hne, ← hdn]; exact hd⟩
  choose W hW hd using key
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end HolChart

theorem exists_bdryChart_of_hol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (Z : Scheme.{0}) (t : SAB H Z) (U : Scheme.{0}) (j : U ⟶ Z) (k : U ⟶ Xo.X) (tU : SAB H U) (n a : ℕ) (y : (Fin n → ℂ) → (Sp ℂ ⟶ Z)), a ≤ n → IsOpenImmersion j → Nonempty (SABMap tU t j) → Nonempty (SABMap tU Xo.univ.t k) → IsHolTo (Metric.ball 0 1) y → (∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ U, p ≫ j = y z ∧ p ≫ k ≫ Xo.s = spMap σ) → ∃ (ρ : ℝ) (C : BdryChart Xo σ n a) (i : Sp C.R ⟶ Z) (e : C.V ⟶ U), 0 < ρ ∧ ρ ≤ 1 ∧ IsOpenImmersion i ∧ Nonempty (SABMap C.t t i) ∧ e ≫ j = C.j ≫ i ∧ e ≫ k = C.k ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ i = y ((ρ : ℂ) • z) := by
  intro E _ _ _ H D l Xo σ Z T U₀ j₀ k₀ To n a y han hj ⟨n₁⟩ ⟨n₂⟩ hy hp
  classical
  have := T.semi.smooth
  obtain ⟨U, hU, hx, -, n', v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Z T.G
    (y 0 (default : PrimeSpectrum ℂ)) ⊤ trivial
  have h0 : ⊤ ≤ y 0 ⁻¹ᵁ U := fun p _ => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]; exact hx
  obtain ⟨ρ₀, hρ₀, hB₀⟩ := Metric.isOpen_iff.1 (hy U 0).1 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρ, hρ1, hB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      Metric.ball (0 : Fin n → ℂ) ρ ⊆ {b ∈ Metric.ball 0 1 | ⊤ ≤ y b ⁻¹ᵁ U} :=
    ⟨min ρ₀ 1, lt_min hρ₀ one_pos, min_le_right _ _, (Metric.ball_subset_ball (min_le_left _ _)).trans hB₀⟩
  have hin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_lt_of_lt_one_right hρ hz
  obtain ⟨t, ⟨m⟩⟩ := exists_sab hU.fromSpec T
  have hdim : SmoothOfRelativeDimension n' t.G.hom := HolChart.smoothDim_of_fibres t n' fun κ _ f t₀ m₀ => by
    obtain ⟨q, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m m₀
    obtain ⟨v', -, hv'⟩ := hv₀ κ f t₀.G _ q.cart
    exact ⟨v', hv'⟩
  obtain ⟨v', -, hv'⟩ := hv₀ Γ(Z, U) (RingHom.id _) t.G m.cm.F (by
    have : spMap (RingHom.id Γ(Z, U)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]; exact m.cart)
  obtain ⟨M⟩ := lieModel_of_isLieBasis v' hv'
  let ψ : (Fin n → ℂ) → (Γ(Z, U) →+* ℂ) := fun z =>
    if h : ⊤ ≤ y ((ρ : ℂ) • z) ⁻¹ᵁ U then evalHom _ U h else evalHom _ U h0
  have hψ : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hU.fromSpec = y ((ρ : ℂ) • z) := fun z hz => by
    simp only [ψ, dif_pos (hB (hin z hz)).2]
    exact spMap_evalHom _ _ _ _
  obtain ⟨tV, ⟨q⟩⟩ := exists_sab (pullback.snd hU.fromSpec j₀) To
  obtain ⟨m₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ q
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ q
  rw [← pullback.condition] at q₁
  obtain ⟨m₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hpt : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ pullback hU.fromSpec j₀,
      p ≫ pullback.fst _ _ = spMap (ψ z) ∧ p ≫ (pullback.snd _ _ ≫ k₀) ≫ Xo.s = spMap σ := fun z hz => by
    obtain ⟨p, hp₁, hp₂⟩ := hp ((ρ : ℂ) • z) ⟨(hB (hin z hz.1)).1, fun i hi => by
      simpa using ⟨hρ.ne', hz.2 i hi⟩⟩
    refine ⟨pullback.lift (spMap (ψ z)) p ((hψ z hz.1).trans hp₁.symm), pullback.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, pullback.lift_snd_assoc, hp₂]
  obtain ⟨p₀, -⟩ := hpt _ (half_mem_punct n a)
  have : Nonempty (Sp ℂ ⟶ pullback hU.fromSpec j₀) := ⟨p₀⟩
  choose! pt hpt using hpt
  refine ⟨ρ, { a_le := han, R := Γ(Z, U), t := t, g := n', dim := hdim
               M := M, ψ := ψ, hol := ⟨Metric.isOpen_ball, fun r => ?_⟩
               V := pullback hU.fromSpec j₀, j := pullback.fst _ _, j_open := inferInstance
               k := pullback.snd _ _ ≫ k₀, tV := tV, m₁ := m₁, m₂ := m₂, pt := pt, pt_eq := hpt },
    hU.fromSpec, pullback.snd _ _, hρ, hρ1, inferInstance, ⟨m⟩, pullback.condition.symm, rfl, hψ⟩
  refine (((hy U r).2.comp (f := fun z => (ρ : ℂ) • z) (by fun_prop) (fun z hz => hB (hin z hz)))).congr
    fun z hz => ?_
  simp only [ψ, Function.comp, valAt', dif_pos (hB (hin z hz)).2]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscInAffineOpen
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HolFac

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

private theorem spMap_appLE_comp_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W)
    (x : Sp ℂ ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ W) :
    spMap ((x.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom) ≫ hW.fromSpec = x := by
  have key := IsAffineOpen.SpecMap_appLE_fromSpec x hW
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at key
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, key]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_ringMaps_of_hol : ∀ (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ⊤ ≤ p 0 ⁻¹ᵁ W →
    ∃ (ρ : ℝ) (ψ : (Fin n → ℂ) → (Γ(X, W) →+* ℂ)), 0 < ρ ∧ ρ ≤ 1 ∧ Flat.IsHolPts (Metric.ball 0 1) ψ ∧
      ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hW.fromSpec = p ((ρ : ℂ) • z) := by
  intro X W hW n p hp h0
  classical
  obtain ⟨hSo, -⟩ := hp W 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρpos, hρ1, hρε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ρ ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  have hmaps : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈
      {b | b ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ⊤ ≤ (TopologicalSpace.Opens.map (p b).base).obj W} := by
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρpos.le]
    calc ρ * ‖z‖ < ρ * 1 := mul_lt_mul_of_pos_left hz hρpos
      _ = ρ := mul_one ρ
      _ ≤ ε := hρε
  let φ : ∀ x : Sp ℂ ⟶ X, ⊤ ≤ x ⁻¹ᵁ W → (Γ(X, W) →+* ℂ) := fun x hx =>
    (x.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
  refine ⟨ρ, fun z => if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0,
    hρpos, hρ1, ⟨Metric.isOpen_ball, ?_⟩, ?_⟩
  · intro r
    have hlin : DifferentiableOn ℂ (fun b : Fin n → ℂ => (ρ : ℂ) • b) (Metric.ball 0 1) :=
      differentiableOn_id.const_smul (ρ : ℂ)
    have hd := (hp W r).2.comp hlin hmaps
    refine hd.congr ?_
    intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) r = valR (p ((ρ : ℂ) • z)) W r
    rw [dite_eq_left hzS]
    unfold valR
    rw [dite_eq_left hzS]
    rfl
  · intro z hz
    have hzS : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W := (hmaps z hz).2
    show spMap (if hz : ⊤ ≤ p ((ρ : ℂ) • z) ⁻¹ᵁ W then φ _ hz else φ _ h0) ≫ hW.fromSpec = _
    rw [dite_eq_left hzS]
    exact spMap_appLE_comp_fromSpec hW _ hzS

end GlobalTheory.CompanionTheory.Ar.HolFac
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemWeightRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem phMu_eq_log_small_blocks_abelian : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  intro hG E _ _ _ _
  exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E

end GlobalTheory.CompanionTheory.Ar.Cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.RootHt.LieFun GlobalTheory.CompanionTheory.Ar.Flat.BdryModel
open scoped CategoryTheory.Obj

theorem exists_coords_of_isLieBasis {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : IsLieBasis v) {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 _) E) :
    ∃ e : Fin n → E, (∀ i, (M.pt (e i)).left = (v i).left) ∧ ∀ x, ∃ c : Fin n → R, x = ∑ i, c i • e i := by
  have h1 : ∀ i, ∃ e, (iota R).hom ≫ M.pt e = v i := fun i => by
    obtain ⟨e, he⟩ := M.onto ((iota R).inv ≫ v i) ((tan_iff _).1 (by simpa using hv.1 i))
    exact ⟨e, by simp [he]⟩
  choose e he using h1
  let F : Multiplicative E →* (epsR R ⟶ G) := MonoidHom.mk' (fun x => (iota R).hom ≫ M.pt x.toAdd)
    (fun a b => by simp [M.add, MonObj.comp_mul])
  have hs : ∀ c : Fin n → R, (iota R).hom ≫ M.pt (∑ i, c i • e i) =
      (List.ofFn fun i => (iota R).hom ≫ M.pt (c i • e i)).prod := fun c => by
    change F (Multiplicative.ofAdd (∑ i, c i • e i)) = _
    rw [ofAdd_sum, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hl : ∀ (c : R) i, ((iota R).hom ≫ M.pt (c • e i)).left = spMap (epsScaleR c) ≫ (v i).left := fun c i => by
    rw [iota_left, M.smul, ← he, iota_left]; rfl
  refine ⟨e, fun i => ?_, fun x => ?_⟩
  · rw [← he, iota_left]
  · obtain ⟨c, ⟨u, hu, hx⟩, -⟩ := hv.2 _ ((tan_iff _).2 (M.tan x))
    refine ⟨c, ?_⟩
    have : u = fun i => (iota R).hom ≫ M.pt (c i • e i) := by
      funext i; ext1; rw [hu, hl]
    rw [this, ← hs] at hx
    exact M.inj ((cancel_epi (iota R).hom).1 hx)

section Base

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] {x : Sp R ⟶ S} {x' : Sp R' ⟶ S}
  {G : Over S} [GrpObj G] {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

theorem pt_smul_eq (M : LieModel G x E) (c : R) (e : E) : M.pt (c • e) = epsScale x c ≫ M.pt e :=
  Over.OverMorphism.ext (M.smul c e)

theorem pt_sum_base (φ : R →+* R') (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (M : LieModel G x E)
    (M' : LieModel G x' E') {I : Type} (s : Finset I) (d : I → R) (e : I → E) (e' : I → E')
    (h : ∀ i, M'.pt (e' i) = epsBase φ hφ ≫ M.pt (e i)) :
    M'.pt (∑ i ∈ s, φ (d i) • e' i) = epsBase φ hφ ≫ M.pt (∑ i ∈ s, d i • e i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [LieModel.pt_zero, LieModel.pt_zero, MonObj.comp_one]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, M'.add, M.add, MonObj.comp_mul, ih, pt_smul_eq, pt_smul_eq, h,
      ← Category.assoc, ← Category.assoc, base_scale]

end Base

theorem exists_frame {X : Scheme.{0}} {G : Over X} [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ}
    (v₀ : Fin n → (Sp (DualNumber Γ(X, U)) ⟶ G.left))
    (hv₀ : ∀ (R' : Type) [CommRing R'] (f : Γ(X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left),
      IsGrpPullback G' G (spMap f ≫ hU.fromSpec) φ →
        ∃ v' : Fin n → (epsR R' ⟶ G'),
          (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
    {R : Type} [CommRing R] (f : Γ(X, U) →+* R) {x : Sp R ⟶ X} (hx : spMap f ≫ hU.fromSpec = x)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∃ e : Fin n → E, (∀ j, (M.pt (e j)).left = spMap (dualMap f) ≫ v₀ j) ∧
      ∀ y, ∃ c : Fin n → R, y = ∑ j, c j • e j := by
  have hz : 𝟙 (Sp R) ≫ (spMap f ≫ hU.fromSpec) = x := by rw [Category.id_comp, hx]
  subst hz
  have hφ := isGrpPullback_pullback G (spMap f ≫ hU.fromSpec)
  obtain ⟨v', hv1, hv2⟩ := hv₀ R f _ _ hφ
  obtain ⟨M', hM'⟩ := (LieMove.models_correspond (x := 𝟙 (Sp R)) hφ E).1 M
  obtain ⟨e, he1, he2⟩ := exists_coords_of_isLieBasis v' hv2 M'
  refine ⟨e, fun j => ?_, he2⟩
  rw [← hM' (e j), he1 j, hv1 j]
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f = dualMap f := by
    ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]

theorem fromSpec_ringHom_ext {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {R : Type} [CommRing R]
    {a a' : Γ(X, W) →+* R} (h : spMap a ≫ hW.fromSpec = spMap a' ≫ hW.fromSpec) : a = a' := by
  have h1 := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
  exact congrArg CommRingCat.Hom.hom h1

theorem spec_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (φ' : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap φ')) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom (dualMap (φ'.comp φ))) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem germ_fromSpec {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) {p : X} (hp : p ∈ W) :
    Spec.map (CommRingCat.ofHom (X.presheaf.germ W p hp).hom) ≫ hW.fromSpec = X.fromSpecStalk p :=
  hW.fromSpecStalk_eq_fromSpecStalk hp

theorem exists_affine_frame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (q : Cpt ξ) (N : ℕ) (b : Fin N → Li), IsCptGen ξ → (∀ k, b k ∈ M.lat q) → ∃ (W : X.Opens) (hW : IsAffineOpen W) (v : Fin N → (epsAt (R := Γ(X, W)) hW.fromSpec ⟶ G)), q.1 ∈ W ∧ (∀ k, IsTanAt G hW.fromSpec (v k)) ∧ ∀ (ψ : Γ(X, W) →+* ℂ) (z : Sp ℂ ⟶ X), spMap ψ ≫ hW.fromSpec = z → genPt ξ ⤳ centre z → ∀ k, ∃ w : epsAt z ⟶ G, M.ValAt z (b k) w ∧ w.left = spMap (dualMap ψ) ≫ (v k).left := by
  intro X G _ _ _ Ω _ ξ Li _ _ M q N b hξ hb
  obtain ⟨W₀, hW₀, hq, -, n, v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange X G q.1 ⊤ trivial
  let f : Γ(X, W₀) →+* X.presheaf.stalk q.1 := (X.presheaf.germ W₀ q.1 hq).hom
  obtain ⟨e, he1, he2⟩ := exists_frame hW₀ v₀ hv₀ f (germ_fromSpec hW₀ hq) (stalkLie hξ M q)
  have hc := fun k => he2 (⟨b k, hb k⟩ : Stalk M q)
  choose c hc using hc

  letI : Algebra Γ(X, W₀) (X.presheaf.stalk q.1) := f.toAlgebra
  haveI := hW₀.isLocalization_stalk ⟨q.1, hq⟩
  obtain ⟨⟨s, hs⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl (fun p : Fin N × Fin n => c p.1 p.2)
  choose a ha using hint
  have hunit : IsUnit (f s) :=
    IsLocalization.map_units (M := (hW₀.primeIdealOf ⟨q.1, hq⟩).asIdeal.primeCompl) (X.presheaf.stalk q.1) ⟨s, hs⟩
  have hqW : q.1 ∈ X.basicOpen s := (X.mem_basicOpen s q.1 hq).2 hunit
  have hW : IsAffineOpen (X.basicOpen s) := hW₀.basicOpen s
  let g : Γ(X, W₀) →+* Γ(X, X.basicOpen s) := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  have hg : spMap g ≫ hW₀.fromSpec = hW.fromSpec := IsAffineOpen.map_fromSpec hW₀ hW (homOfLE (X.basicOpen_le s)).op
  obtain ⟨u, hu⟩ : IsUnit (g s) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace s
  obtain ⟨E', _, _, ⟨M'⟩⟩ := lieModel_exists X G Γ(X, X.basicOpen s) hW.fromSpec
  obtain ⟨e', he'1, -⟩ := exists_frame hW₀ v₀ hv₀ g hg M'
  let d : Fin N → Fin n → Γ(X, X.basicOpen s) := fun k j => g (a (k, j)) * (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)
  let v : Fin N → (epsAt (R := Γ(X, X.basicOpen s)) hW.fromSpec ⟶ G) := fun k => M'.pt (∑ j, d k j • e' j)
  let θ : Γ(X, X.basicOpen s) →+* X.presheaf.stalk q.1 := (X.presheaf.germ _ q.1 hqW).hom
  have hθ : Spec.map (CommRingCat.ofHom θ) ≫ hW.fromSpec = X.fromSpecStalk q.1 := germ_fromSpec hW hqW
  have hθg : θ.comp g = f := by
    refine RingHom.ext fun t => ?_
    exact congrArg (fun m => m.hom t) (X.presheaf.germ_res (homOfLE (X.basicOpen_le s)) q.1 hqW)
  have hθa : ∀ t, θ (g t) = f t := fun t => congrArg (fun m => m t) hθg
  have key : ∀ k, (stalkLie hξ M q).pt ⟨b k, hb k⟩ = epsBase θ hθ ≫ v k := by
    intro k
    have hd : ∀ j, θ (d k j) = c k j := fun j => by
      have h1 : f (a (k, j)) = f s * c k j := ha (k, j)
      have h2 : θ (g s) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) = 1 := by
        rw [← map_mul, ← hu, Units.mul_inv, map_one]
      rw [hθa] at h2
      calc θ (d k j) = f (a (k, j)) * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ) := by rw [map_mul, hθa]
        _ = (f s * θ (↑u⁻¹ : Γ(X, X.basicOpen s)ˣ)) * c k j := by rw [h1]; ring
        _ = c k j := by rw [h2, _root_.one_mul]
    have := pt_sum_base θ hθ M' (stalkLie hξ M q) Finset.univ (d k) e' e (fun j => Over.OverMorphism.ext (by
      rw [he1 j]
      change _ = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M'.pt (e' j)).left
      rw [he'1 j, ← Category.assoc, spec_dual_comp, hθg]))
    rw [hc k]
    simpa only [hd] using this
  refine ⟨X.basicOpen s, hW, v, hqW, fun k => M'.tan _, ?_⟩
  intro ψ z hz h k
  subst hz
  have hp : centre (spMap ψ ≫ hW.fromSpec) ∈ X.basicOpen s := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨(spMap ψ) (IsLocalRing.closedPoint ℂ), rfl⟩
  let θp : Γ(X, X.basicOpen s) →+* X.presheaf.stalk (centre (spMap ψ ≫ hW.fromSpec)) :=
    (X.presheaf.germ _ _ hp).hom
  have hθp : Spec.map (CommRingCat.ofHom θp) ≫ hW.fromSpec = X.fromSpecStalk _ := germ_fromSpec hW hp
  have e1 : (genMap ξ q).comp θ = (genMap ξ ⟨_, h⟩).comp θp := fromSpec_ringHom_ext hW (by
    change Spec.map (CommRingCat.ofHom _) ≫ _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, ← spec_comp, Category.assoc, Category.assoc, hθ, hθp, spec_genMap, spec_genMap])
  have e2 : ψ = (Scheme.stalkClosedPointTo (spMap ψ ≫ hW.fromSpec)).hom.comp θp := fromSpec_ringHom_ext hW (by
    change _ = Spec.map (CommRingCat.ofHom _) ≫ _
    rw [← spec_comp, Category.assoc, hθp]
    exact (spec_centre _).symm)
  refine ⟨epsBase ψ rfl ≫ v k, ⟨h, epsBase θp hθp ≫ v k, ⟨isTanAt_base _ _ (M'.tan _), ?_⟩, ?_⟩, rfl⟩
  · have t : (M.pt (b k)).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ q))) ≫
        ((stalkLie hξ M q).pt ⟨b k, hb k⟩).left := (Stalk.tan_spec (⟨b k, hb k⟩ : Stalk M q)).2
    rw [t, key k]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, ← Category.assoc, spec_dual_comp, spec_dual_comp, e1]
  · change Spec.map (CommRingCat.ofHom (dualMap ψ)) ≫ (v k).left =
      Spec.map _ ≫ Spec.map (CommRingCat.ofHom (dualMap θp)) ≫ (v k).left
    rw [← Category.assoc, spec_dual_comp, ← e2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelMapsHeckePointsOfPos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem levelMaps_heckePoints_of_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun E _ _ _ H D h => GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionModuleFieldExtMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_module_field_ext_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D'), ∃ P : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))) → SecMod D'.t.G.hom (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), (∀ (a : 𝓞 L) s, P (a • s) = algebraMap (𝓞 L) (𝓞 L') a • P s) ∧ ∀ (s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (b' : Sp (𝓞 L')) (y : D.t.G.left), D.t.G.hom y = spMap (algebraMap (𝓞 L) (𝓞 L')) b' → y ∈ Out.nonzeroLocus (M := (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) s → ∃ y' : D'.t.G.left, D'.t.G.hom y' = b' ∧ y' ∈ Out.nonzeroLocus (M := (LB.LinComb D'.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ)))) (P s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.exists_pull_sec <;> assumption)
end

