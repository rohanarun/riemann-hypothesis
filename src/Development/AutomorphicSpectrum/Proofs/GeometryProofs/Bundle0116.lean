module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0049

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConjugateLogPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods

open GroundTheory.Heights₂.Heights.Regular

theorem star_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) :
    star w ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simpa using hw.1 i
  · simpa using hw.2 k hk

theorem expCover_star {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : expCover a (star w) = star (expCover a w) := by
  funext k
  simp only [expCover, Pi.star_apply]
  split_ifs
  · exact Complex.exp_conj _
  · rfl

theorem isOpen_logCover {n a : ℕ} (h : a ≤ n) : IsOpen (logCover h) := by
  have : logCover h = (⋂ i : Fin a, {w : Fin n → ℂ | (w (Fin.castLE h i)).re < 0}) ∩
      ⋂ k : Fin n, {w : Fin n → ℂ | a ≤ k.val → ‖w k‖ < 1} := by
    ext w; simp [logCover]
  rw [this]
  refine (isOpen_iInter_of_finite fun i => ?_).inter (isOpen_iInter_of_finite fun k => ?_)
  · exact isOpen_lt (Complex.continuous_re.comp (continuous_apply _)) continuous_const
  · by_cases hk : a ≤ k.val
    · simpa [hk] using isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
    · simp [hk]

theorem star_mem_ball {n : ℕ} {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    star z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
  intro i
  simpa using hz i

theorem differentiableOn_conj {n g : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hst : ∀ w ∈ S, star w ∈ S)
    {f : (Fin n → ℂ) → Fin g → ℂ} (hf : DifferentiableOn ℂ f S) :
    DifferentiableOn ℂ (fun w => star (f (star w))) S := by
  intro w hw
  have h1 : DifferentiableAt ℂ f (star w) := hf.differentiableAt (hS.mem_nhds (hst w hw))
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.differentiableWithinAt

theorem dot_map_conj {g : ℕ} (x y : Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ) :
    x ⬝ᵥ M.map (starRingEnd ℂ) *ᵥ y = star (star x ⬝ᵥ M *ᵥ star y) := by
  simp [dotProduct, Matrix.mulVec, star_sum]

theorem isHermitian_map_conj {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) :
    (M.map (starRingEnd ℂ)).IsHermitian := by
  ext i j
  have := hM.apply i j
  simp [Matrix.conjTranspose_apply, ← this]

theorem star_single {n : ℕ} (c : Fin n) :
    star (Pi.single c (2 * Real.pi * Complex.I) : Fin n → ℂ) = -Pi.single c (2 * Real.pi * Complex.I) := by
  funext k
  by_cases hk : k = c
  · subst hk
    simp
  · simp [hk]

theorem sub_single_mem_logCover {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ logCover h) (i : Fin a) :
    w - Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · by_cases hj : Fin.castLE h j = Fin.castLE h i
    · simpa [hj, Pi.single_apply] using (by simpa [hj] using hw.1 j)
    · simpa [Pi.single_apply, hj] using hw.1 j
  · have hki : k ≠ Fin.castLE h i := by
      rintro rfl
      simp at hk
      omega
    simpa [Pi.single_apply, hki] using hw.2 k hk

def conj {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (hT : ∀ i, Function.Bijective (L.T i)) : Flat.LogPeriods n a g Λ where
  a_le := L.a_le
  free := L.free
  fin := L.fin
  rank := L.rank
  E := -L.E
  alt x := by simp [L.alt x]
  unimod := by
    constructor
    · intro x y hxy
      exact L.unimod.1 (neg_injective hxy)
    · intro f
      obtain ⟨x, hx⟩ := L.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  P w := AddMonoidHom.mk' (fun x => star (L.P (star w) x)) (fun x y => by simp)
  hol x := differentiableOn_conj (isOpen_logCover L.a_le) (fun w hw => star_mem_logCover L.a_le hw) (L.hol x)
  H z := (L.H (star z)).map (starRingEnd ℂ)
  herm w hw := by
    rw [← expCover_star]
    exact isHermitian_map_conj (L.herm _ (star_mem_logCover L.a_le hw))
  pos w hw z hz := by
    rw [← expCover_star, dot_map_conj]
    have h := L.pos _ (star_mem_logCover L.a_le hw) (star z) (by simpa using hz)
    simpa using h
  im w hw x y := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, dot_map_conj]
    have h := L.im _ (star_mem_logCover L.a_le hw) x y
    simp [h]
  T i := ((LinearEquiv.ofBijective (L.T i) (hT i)).symm : Λ ≃ₗ[ℤ] Λ).toLinearMap
  mono i w hw x := by
    set e : Fin _ → ℂ := Pi.single (Fin.castLE L.a_le i) (2 * Real.pi * Complex.I) with he
    have hw₁ : star w - e ∈ logCover L.a_le :=
      sub_single_mem_logCover L.a_le (star_mem_logCover L.a_le hw) i
    have hm := L.mono i _ hw₁ ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x)
    have hTT : L.T i ((LinearEquiv.ofBijective (L.T i) (hT i)).symm x) = x :=
      (LinearEquiv.ofBijective (L.T i) (hT i)).apply_symm_apply x
    rw [hTT, ← he, sub_add_cancel] at hm
    have hs : star (w + e) = star w - e := by
      rw [star_add, he, star_single, sub_eq_add_neg]
    simp only [AddMonoidHom.mk'_apply, LinearEquiv.coe_coe]
    rw [hs, hm]
  W := L.W
  coiso x hx := L.coiso x fun y hy => by simpa using hx y hy
  s x z := star (L.s x (star z))
  s_hol x := differentiableOn_conj Metric.isOpen_ball (fun _ hz => star_mem_ball hz) (L.s_hol x)
  s_eq x w hw := by
    simp only [AddMonoidHom.mk'_apply]
    rw [← expCover_star, L.s_eq x _ (star_mem_logCover L.a_le hw)]
  span := by
    rw [eq_top_iff]
    intro v _
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun x => L.s x 0),
        star y ∈ Submodule.span ℂ (Set.range fun x => star (L.s x (star (0 : Fin _ → ℂ)))) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact Submodule.subset_span ⟨x, by simp⟩
      | zero => simp
      | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [star_smul]
        exact Submodule.smul_mem _ _ hy
    have := key (star v) (by rw [L.span]; trivial)
    simpa using this

theorem exists_conj_periodGram : ∀ (n a g r : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ), (∀ i, Function.Bijective (L.T i)) →
    ∃ L' : Flat.LogPeriods n a g Λ, ∀ u ∈ Flat.punct n a 1,
      HodgeMetric.periodGram L' (fun k u' => star (U k (star u'))) u =
        (HodgeMetric.periodGram L U (star u)).map (starRingEnd ℂ) := by
  intro n a g r Λ _ L U hT
  refine ⟨conj L hT, fun u _ => ?_⟩
  ext i j
  simp only [HodgeMetric.periodGram, Matrix.of_apply, Matrix.map_apply]
  change _ * (_ ⬝ᵥ ((L.H (star u)).map (starRingEnd ℂ)) *ᵥ _) = _
  rw [dot_map_conj, map_mul, Complex.conj_ofReal]
  simp

end GlobalTheory.CompanionTheory.Ar.Flat.ConjPeriods
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSegreChartFrames
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq {U : X.Opens} (g : Γ(X, U)) (p q : Cpt ξ) (hp : p.1 ∈ U) (hq : q.1 ∈ U) :
    genMap ξ p (X.presheaf.germ U p.1 hp g) = genMap ξ q (X.presheaf.germ U q.1 hq g) := by
  have key : ∀ (r : Cpt ξ) (hr : r.1 ∈ U), genMap ξ r (X.presheaf.germ U r.1 hr g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) (r.2.mem_open U.2 hr) g) := by
    intro r hr
    show (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.stalkSpecializes r.2 (X.presheaf.germ U r.1 hr g)) = _
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hr r.2 g)
  rw [key p hp, key q hq]

theorem unitAt_of_isUnit {p : Cpt ξ} {s : X.presheaf.stalk p.1} (hs : IsUnit s) :
    unitAt ξ p (genMap ξ p s) := by
  have hu : IsUnit (genMap ξ p s) := hs.map (genMap ξ p)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hu.ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, Units.inv_mul, map_one]

theorem isUnit_of_unitAt (hξ : IsCptGen ξ) {p : Cpt ξ} {s : X.presheaf.stalk p.1}
    (h : unitAt ξ p (genMap ξ p s)) : IsUnit s := by
  obtain ⟨h0, _, t, ht⟩ := h
  refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
  rw [map_mul, ht, map_one, mul_inv_cancel₀ h0]

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem inFrameDomain_of_unitAt (hT : CoordTie ℤ ξ (segreCoord y)) {z : Spec (CommRingCat.of ℂ) ⟶ X}
    {w : (Σ k, J k) → ℂ} (hz : CoordsAt ξ y z w) (h : genPt ξ ⤳ centre z) {c : (k : K) → J k} {f : Ω}
    (hc : InChart ξ (segreCoord y) c ⟨centre z, h⟩) (hf : unitAt ξ ⟨centre z, h⟩ f) :
    InFrameDomain y c f w := by
  let gv : X.presheaf.stalk (centre z) →+* Ω := genMap ξ ⟨centre z, h⟩
  let ev : X.presheaf.stalk (centre z) →+* ℂ := (Scheme.stalkClosedPointTo z).hom
  have hinj : Function.Injective gv := hT.gen.inj ⟨centre z, h⟩
  constructor
  · choose d hd using hz.1
    have key : ∀ k, ∃ (r : ℂ) (s : X.presheaf.stalk (centre z)),
        gv s = y ⟨k, c k⟩ / y ⟨k, d k⟩ ∧ ev s = r ∧ w ⟨k, c k⟩ = r * w ⟨k, d k⟩ := by
      intro k
      obtain ⟨r, ⟨_, s, hs, hv⟩, hw⟩ := (hz.2 k (d k) (hd k)).2 (c k)
      exact ⟨r, s, hs, hv, hw⟩
    choose r s hs hv hw using key
    obtain ⟨t, ht⟩ : ∃ t, gv t = segreCoord y d / segreCoord y c := hc.2 d
    have hxd : segreCoord y d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => (hz.2 k (d k) (hd k)).1
    have hxc : segreCoord y c ≠ 0 := hc.1
    have hone : t * ∏ k, s k = 1 := by
      refine hinj ?_
      rw [map_mul, map_prod, ht, map_one]
      simp only [hs]
      rw [Finset.prod_div_distrib]
      change segreCoord y d / segreCoord y c * (segreCoord y c / segreCoord y d) = 1
      field_simp
    have hval := congrArg ev hone
    rw [map_mul, map_prod, map_one] at hval
    simp only [hv] at hval
    have hr : ∏ k, r k ≠ 0 := right_ne_zero_of_mul_eq_one hval
    intro k
    rw [hw k]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.1 hr k (Finset.mem_univ k)) (hd k).ne_zero
  · obtain ⟨s, hs⟩ : ∃ s, gv s = f := hf.2.1
    obtain ⟨t, ht⟩ : ∃ t, gv t = f⁻¹ := hf.2.2
    have hone : s * t = 1 := by
      refine hinj ?_
      rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf.1]
    have hval := congrArg ev hone
    rw [map_mul, map_one] at hval
    exact ⟨ev s, (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords X Ω ξ K J y hT z w h hz f _).1 ⟨h, s, hs, rfl⟩,
      left_ne_zero_of_mul_eq_one hval⟩

variable {F : Type} [AddCommGroup F] [Module Ω F] {r : ℕ} {W : ChartBundle ℤ (segreCoord y) r F} {L : Lat ξ F}

theorem exists_frames_on_chart (hT : CoordTie ℤ ξ (segreCoord y)) (hV : L.IsVB r ⊤)
    (hC : L.IsChartOf (segreCoord y) W.lat) (c : (k : K) → J k) (hc : segreCoord y c ≠ 0) :
    ∃ S : Set (Ω × (Fin r → F)), S.Finite ∧ (∀ a ∈ S, IsFrameOver y W c a.1 a.2) ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → ∃ a ∈ S, unitAt ξ p a.1 := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have loc : ∀ q : U, ∃ (g : Γ(X, U)) (b : Fin r → F), q.1 ∈ X.basicOpen g ∧
      ∀ p : Cpt ξ, p.1 ∈ X.basicOpen g → L.IsFrameAt b p := by
    intro q
    obtain ⟨h, -⟩ := (hmem q.1).1 q.2
    obtain ⟨V, hqV, b, -, hb⟩ := hV ⟨q.1, h⟩ (Set.mem_univ _)
    obtain ⟨g, hgV, hqg⟩ := hU.exists_basicOpen_le (V := V) ⟨q.1, hqV⟩ q.2
    exact ⟨g, b, hqg, fun p hp => hb p (Set.mem_univ _) (hgV hp)⟩
  choose g b hq hfr using loc
  have hsp : ∀ q : U, genPt ξ ⤳ q.1 := fun q => ((hmem q.1).1 q.2).1
  have hpU : ∀ p : Cpt ξ, InChart ξ (segreCoord y) c p → p.1 ∈ U :=
    fun p hp => (hmem p.1).2 ⟨p.2, hp⟩
  let v : U → Ω := fun q => genMap ξ ⟨q.1, hsp q⟩ (X.presheaf.germ U q.1 q.2 (g q))
  have hv : ∀ (q : U) (p : Cpt ξ) (hp : p.1 ∈ U), v q = genMap ξ p (X.presheaf.germ U p.1 hp (g q)) :=
    fun q p hp => genMap_germ_eq (g q) ⟨q.1, hsp q⟩ p q.2 hp
  have hunit : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → p.1 ∈ X.basicOpen (g q) → unitAt ξ p (v q) := by
    intro q p hp hb
    rw [hv q p hp]
    exact unitAt_of_isUnit ((Scheme.mem_basicOpen _ _ _ hp).1 hb)
  have hbasic : ∀ (q : U) (p : Cpt ξ), p.1 ∈ U → unitAt ξ p (v q) → p.1 ∈ X.basicOpen (g q) := by
    intro q p hp hu
    rw [hv q p hp] at hu
    exact (Scheme.mem_basicOpen _ _ _ hp).2 (isUnit_of_unitAt hT.gen hu)
  have hcov : (U : Set X) ⊆ ⋃ q : U, (X.basicOpen (g q) : Set X) :=
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hq _⟩
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover _ (fun q => (X.basicOpen (g q)).isOpen) hcov
  refine ⟨(fun q => (v q, b q)) '' (↑t : Set _), t.finite_toSet.image _, ?_, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    have hne : v q ≠ 0 := (hunit q ⟨q.1, hsp q⟩ q.2 (hq q)).1
    have hring : v q ∈ chartRing ℤ (segreCoord y) c :=
      (hT.ring c hc (v q)).2 fun p hp => ⟨_, (hv q p (hpU p hp)).symm⟩
    exact (_root_.GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt X Ω ξ K J y F r W L hT hV hC c (v q) (b q) hc hring hne).2
      fun p hp hu => hfr q p (hbasic q p (hpU p hp) hu)
  · intro p hp
    obtain ⟨q, hqt, hqp⟩ := Set.mem_iUnion₂.1 (ht (hpU p hp))
    exact ⟨_, ⟨q, hqt, rfl⟩, hunit q p (hpU p hp) hqp⟩

end GlobalTheory.CompanionTheory.Ar.ChartFrames

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem exists_frames_cover_mcPts : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F : Type) [AddCommGroup F] [Module Ω F] (r : ℕ) (W : ChartBundle ℤ (segreCoord y) r F) (L : Lat ξ F), CoordTie ℤ ξ (segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (segreCoord y) W.lat → ∃ (m : ℕ) (ch : Fin m → (k : K) → J k) (fr : Fin m → Ω) (b : Fin m → Fin r → F), (∀ i, IsFrameOver y W (ch i) (fr i) (b i)) ∧ ∀ w ∈ mcPts (mCoordIdeal y), ∃ i, InFrameDomain y (ch i) (fr i) w := by
  classical
  intro X Ω _ ξ K _ J _ y F _ _ r W L hT hV hC
  have hloc := fun c : {c : (k : K) → J k // segreCoord y c ≠ 0} =>
    ChartFrames.exists_frames_on_chart (W := W) (L := L) hT hV hC c.1 c.2
  choose S hfin hframe hcov using hloc
  let T : Set (((k : K) → J k) × Ω × (Fin r → F)) :=
    ⋃ c, (fun a : Ω × (Fin r → F) => (c.1, a.1, a.2)) '' S c
  have hTfin : T.Finite := Set.finite_iUnion fun c => (hfin c).image _
  haveI := hTfin.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  refine ⟨m, fun i => (e.symm i).1.1, fun i => (e.symm i).1.2.1, fun i => (e.symm i).1.2.2, ?_, ?_⟩
  · have hall : ∀ t ∈ T, IsFrameOver y W t.1 t.2.1 t.2.2 := by
      intro t ht
      obtain ⟨c, a, ha, rfl⟩ := Set.mem_iUnion.1 ht
      exact hframe c a ha
    exact fun i => hall _ (e.symm i).2
  · intro w hw
    obtain ⟨z, h, hz⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt X Ω ξ K J y hT w).1 hw
    obtain ⟨c, hc⟩ := hT.cover ⟨centre z, h⟩
    obtain ⟨a, ha, hu⟩ := hcov ⟨c, hc.1⟩ ⟨centre z, h⟩ hc
    have hmem : (c, a.1, a.2) ∈ T := Set.mem_iUnion.2 ⟨⟨c, hc.1⟩, a, ha, rfl⟩
    refine ⟨e ⟨_, hmem⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ChartFrames.inFrameDomain_of_unitAt hT hz h hc hu

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformisationLocalPeriod
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_index_of_isPreconnected : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → IsPreconnected B → B.Nonempty → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∃ i : Fin FU.n, ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b := by
  intro E _ _ _ H D l Xo σ g ty FU m B y hB hpre hne hs hy
  let S : Fin FU.n → Set (Fin m → ℂ) := fun i => {b₀ | ∃ (B' : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      IsHolPeriods (FU.Di i) ty B' P ∧ ∀ b ∈ B', FU.u i (P b) = y b}
  have hopen : ∀ i, IsOpen (S i) := by
    intro i
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro b₀ ⟨B', P, hB', hb₀, hsub, hP, hu⟩
    exact ⟨B', fun b hb => ⟨B', P, hB', hb, hsub, hP, hu⟩, hB', hb₀⟩
  have hcover : ∀ b ∈ B, ∃ i, b ∈ S i := by
    intro b hb
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := FU.lift m B y hB hs hy b hb
    exact ⟨i, B', P, hB', hb', hsub, hP, hu⟩
  have hdisj : ∀ i j b, b ∈ S i → b ∈ S j → i = j := by
    rintro i j b ⟨B₁, P₁, -, hb₁, -, hP₁, hu₁⟩ ⟨B₂, P₂, -, hb₂, -, hP₂, hu₂⟩
    exact FU.disj i j (P₁ b) (P₂ b) (hP₁.1 b hb₁) (hP₂.1 b hb₂) ((hu₁ b hb₁).trans (hu₂ b hb₂).symm)
  obtain ⟨b₁, hb₁⟩ := hne
  obtain ⟨i, hi⟩ := hcover b₁ hb₁
  have hsub : B ⊆ S i := by
    refine IsPreconnected.subset_left_of_subset_union (v := ⋃ j ∈ {j | j ≠ i}, S j) (hopen i)
      (isOpen_biUnion fun j _ => hopen j) ?_ ?_ ⟨b₁, hb₁, hi⟩ hpre
    · refine Set.disjoint_left.2 fun b hbi hbT => ?_
      obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.1 hbT
      exact hj (hdisj i j b hbi hbj).symm
    · intro b hb
      obtain ⟨j, hj⟩ := hcover b hb
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hj⟩)
  exact ⟨i, fun b₀ hb₀ => hsub hb₀⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem inChart_unitAt_of_inFrameDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segreCoord y) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f : Ω) (h : genPt ξ ⤳ centre z), CoordsAt ξ y z w → InFrameDomain y cc f w → InChart ξ (segreCoord y) cc ⟨centre z, h⟩ ∧ unitAt ξ ⟨centre z, h⟩ f := by
  intro X Ω _ ξ K _ J _ y hT z w cc f h hw hd
  have hu : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hd.1 k)
  have hy : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hw.2 k (cc k) (hu k)).1
  have reg : ∀ {a : Ω} {r : ℂ}, ValAt ξ z a r → a ∈ regAt ξ ⟨centre z, h⟩ := by
    rintro a r ⟨_, s, hs, -⟩
    exact ⟨s, hs⟩
  refine ⟨⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩, ?_⟩
  · choose r hr _ using fun k => (hw.2 k (cc k) (hu k)).2 (c' k)
    have hp : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, y ⟨k, c' k⟩ / y ⟨k, cc k⟩) (∏ k ∈ s, r k) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using CxVal.one h
      | insert k s hk ih =>
        rw [Finset.prod_insert hk, Finset.prod_insert hk]
        exact CxVal.mul (hr k) ih
    have e : segreCoord y c' / segreCoord y cc = ∏ k, y ⟨k, c' k⟩ / y ⟨k, cc k⟩ := by
      simp only [segreCoord, Finset.prod_div_distrib]
    rw [e]
    exact reg (hp Finset.univ)
  · obtain ⟨v, hv, hv0⟩ := hd.2
    have hf : ValAt ξ z f v := (_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords X Ω ξ K J y hT z w h hw f v).2 hv
    refine ⟨?_, reg hf, reg (CxVal.inv hf hv0)⟩
    obtain ⟨_, s, hs, hsv⟩ := hf
    have hs0 : (Scheme.stalkClosedPointTo z).hom s ≠ 0 := by rw [hsv]; exact hv0
    have := (CxVal.isUnit s hs0).map (genMap ξ ⟨centre z, h⟩)
    rw [hs] at this
    exact this.ne_zero

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsGoodStatement
section
namespace GlobalTheory.CompanionTheory.Ggeo

theorem blockProjection_genericPoints_good : GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GlobalTheory.CompanionTheory.Ar.PB.BaseCount.generic_points_good_for_intersection

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicCoordsOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PeriodsHol

theorem isHolTo_of_coordsAt_family : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → ∀ (n : ℕ) (B : Set (Fin n → ℂ)) (w : (Fin n → ℂ) → (Σ k, J k) → ℂ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → DifferentiableOn ℂ w B → (∀ u ∈ B, CoordsAt ξ y (p u) (w u)) → IsHolTo B p := by
  intro X Ω _ ξ K _ J _ y htie hall n B w p hB hw hco
  exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.ChartHol.isHolTo_of_coordsAt htie hall hB
    (fun q => (differentiableOn_pi.1 hw) q) hco

end GlobalTheory.CompanionTheory.Ar.PeriodsHol
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieProj

theorem lie_finite_projective_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L), Module.Finite R L ∧ Module.Projective R L ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (L' : Type) [AddCommGroup L'] [Module R' L'] [Module R L'] [IsScalarTower R R' L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x) L') (β : L →ₗ[R] L'), (∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R R'))) ≫ (M.pt e).left) → IsBaseChange R' β :=
  @PositivityTheory.HtPt.Htat.lie_proj

end GlobalTheory.CompanionTheory.Ar.LieProj
end

