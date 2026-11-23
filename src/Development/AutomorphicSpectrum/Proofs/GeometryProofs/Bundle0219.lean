module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0215
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductAdjoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFourth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree


open LieTangent in
theorem valAt_diff {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] {M : LieModel G ξ L}
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f]
    {A : L →ₗ[Ω] L} (hA : M.IsDiffOf f A) {e : L} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨h1, v, hv, hw⟩ := h
  refine ⟨h1, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · change _ ≫ (v ≫ f).left = _
    simp only [Over.comp_left]
    rw [← Category.assoc, hv.1]
    exact congrArg CommaMorphism.left (one_comp f)
  · change (M.pt (A e)).left = _ ≫ (v ≫ f).left
    rw [hA e]
    simp only [Over.comp_left, ← Category.assoc, hv.2]
  · change (w ≫ f).left = _ ≫ (v ≫ f).left
    simp only [Over.comp_left, ← Category.assoc, hw]

theorem conj_ne_of_sq {x : ℂ} {d : ℕ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) : starRingEnd ℂ x ≠ x := by
  intro h
  have him : x.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re hx
  have : x = (x.re : ℂ) := Complex.ext rfl (by simpa using him)
  rw [this] at hre
  norm_cast at hre
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp at hre
  nlinarith [sq_nonneg x.re]

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq]
  simp

theorem val_eig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
    {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hξ : IsCptGen 𝔐.ξ) (hg : genPt 𝔐.ξ ⤳ centre z)
    (s : CMType H ⊕ CMType H) (a : 𝓞 E) (t : 𝔐.X.presheaf.stalk (centre z))
    (ht : genMap 𝔐.ξ ⟨centre z, hg⟩ t = 𝔐.emb s a) {e : 𝔐.Li} (he : e ∈ 𝔐.Vgen s)
    {v : epsAt z ⟶ 𝔐.t.G} (hv : 𝔐.M.ValAt z e v) :
    v ≫ 𝔐.t.act.act a = LieTangent.epsScale z ((Scheme.stalkClosedPointTo z).hom t) ≫ v := by
  haveI := 𝔐.t.act.hom a
  have h1 := valAt_diff (𝔐.act a) hv
  have h2 := hv.smul hg t
  have e1 : 𝔐.ρ a e = genMap 𝔐.ξ ⟨centre z, hg⟩ t • e := by
    have h3 := (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h3
    rw [ht]
    simpa [sub_eq_zero] using h3
  rw [e1] at h1
  exact h1.unique hξ h2

theorem hodgeInnerProduct_blocks_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (e e' : Or.𝔐.Li) (v v' : epsAt z ⟶ Or.𝔐.t.G) (a : ℂ), Or.𝔐.Interior z → e ∈ Or.𝔐.Vgen (Or.bg τ) → e' ∈ Or.𝔐.Vgen (Or.sm τ) → Or.𝔐.M.ValAt z e v → Or.𝔐.M.ValAt z e' v' → HodgeIP Or.𝔐.t.G Or.𝔐.t.PP.L z v v' a → a = 0 := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ e e' v v' a hz he he' hv hv' hI
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, hc0, -, -, -, -, hreg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S₀ Ω K J Dc.y Or.𝔐 hβ
  haveI := hc0
  have hP := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hz
  have hg : genPt Or.𝔐.ξ ⤳ centre z := Or.𝔐.all _
  have hξ : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists Or.𝔐.X Or.𝔐.t.G ℂ z
  obtain ⟨h, hHI, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H Or.𝔐.X Or.𝔐.t z Vz MR hP
  obtain ⟨g, hgen⟩ := hreg (Sum.inl τ) H.rt ⟨centre z, hg⟩
  set x : ℂ := (Scheme.stalkClosedPointTo z).hom g with hx
  have hsq : g ^ 2 = -(H.d : Or.𝔐.X.presheaf.stalk (centre z)) := by
    apply hξ.inj ⟨centre z, hg⟩
    rw [map_pow, hgen, map_neg, map_natCast, ← map_pow, H.rt_sq, map_neg, map_natCast]
  have hx2 : x ^ 2 = -(H.d : ℂ) := by
    rw [hx, ← map_pow, hsq, map_neg, map_natCast]
  have hne : starRingEnd ℂ x ≠ x := conj_ne_of_sq H.d_prime.pos hx2
  have hin : ∀ b, Or.𝔐.emb (Sum.inr τ) b = Or.𝔐.emb (Sum.inl τ) (H.bar b) := fun _ => rfl
  have key : ∃ b, v ≫ Or.𝔐.t.act.act b = LieTangent.epsScale z x ≫ v ∧
      v' ≫ Or.𝔐.t.act.act (H.bar b) = LieTangent.epsScale z x ≫ v' := by
    rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.rt, val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he hv,
        val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he' hv'⟩
      rw [hin, bar_bar, hgen]
    · rw [hb] at he
      rw [hs] at he'
      refine ⟨H.bar H.rt, val_eig Or.𝔐 hξ hg (Sum.inr τ) _ g ?_ he hv, ?_⟩
      · rw [hin, bar_bar, hgen]
      · rw [bar_bar]
        exact val_eig Or.𝔐 hξ hg (Sum.inl τ) _ g hgen he' hv'
  obtain ⟨b, A1, A2⟩ := key
  obtain ⟨p, rfl⟩ := MR.onto v hv.isTanAt
  obtain ⟨p', rfl⟩ := MR.onto v' hv'.isTanAt
  have ha : a = h p p' := (hHI _ _ _).1 hI
  have hadj := _root_.GlobalTheory.CompanionTheory.Ar.hodgeInnerProduct_act_adjoint E H Or.𝔐.X Or.𝔐.t z (MR.pt p) (MR.pt p') b (h (x • p) p') hP (MR.tan p) (MR.tan p')
  rw [A1, A2, ← MR.pt_smul, ← MR.pt_smul] at hadj
  have e1 : h (x • p) p' = h p (x • p') := (hHI _ _ _).1 (hadj.1 ((hHI _ _ _).2 rfl))
  rw [map_smulₛₗ, map_smul] at e1
  simp only [LinearMap.smul_apply, smul_eq_mul] at e1
  rw [ha]
  have e2 : (starRingEnd ℂ x - x) * h p p' = 0 := by
    rw [sub_mul, e1, sub_self]
  exact (mul_eq_zero.1 e2).resolve_left (sub_ne_zero.2 hne)

end GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeThird
section
namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter _root_.Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem gramAt_posDef_of_isFrameAt_blocks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z τ b h hi hf
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hmem : ∀ w, Or.i τ w ∈ Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ) := fun w => by
    rw [← Or.i_range τ]
    exact LinearMap.mem_range_self _ w
  let φ : W τ →ₗ[Ω] ↥(Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)) := (Or.i τ).codRestrict _ hmem
  have hφi : Function.Injective φ := fun x y hxy => Or.i_inj τ (congrArg Subtype.val hxy)
  have hφs : Function.Surjective φ := fun x => by
    have hx : (x : Or.𝔐.Li) ∈ LinearMap.range (Or.i τ) := by
      rw [Or.i_range τ]
      exact x.2
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, Subtype.ext hw⟩
  have hpol := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hi
  have hframe : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p)
      (Or.𝔐.Vgen (Or.bg τ) ⊔ Or.𝔐.Vgen (Or.sm τ)).subtype).IsFrameAt (fun k => φ (b k)) ⟨centre z, h⟩ := by
    refine ⟨hf.1.map' φ (LinearMap.ker_eq_bot.2 hφi), ?_⟩
    have hs := hf.2
    ext x
    obtain ⟨w, rfl⟩ := hφs x
    have hrange : Set.range (fun k => φ (b k)) = φ '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    have hspan : Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range (fun k => φ (b k))) =
        (Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range b)).map
          (φ.restrictScalars (regAt Or.𝔐.ξ ⟨centre z, h⟩)) := by
      rw [hrange, Submodule.map_span]
      rfl
    rw [hspan, ← hs]
    constructor
    · intro hx
      exact ⟨w, hx, rfl⟩
    · rintro ⟨w', hw', e⟩
      have : w' = w := hφi e
      subst this
      exact hw'
  obtain ⟨G, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) Dc.N
    (fun k => φ (b k)) z h hpol hframe
  exact ⟨G, h1, h2⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFramesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_two_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ' → (∀ q, b' q = ∑ p, T p q • b p) → (∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) → Γ' = Tz.conjTranspose * Γ * Tz := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFifth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open GlobalTheory.CompanionTheory.Ar.HodgeCpt (rootIdx rootSgn)

theorem isHodgeLine_pull_tensor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx hv r a a₀ e e₀ A₀ T
    hβ hcz hy hGen hNorm hVal hCoord hInt he hA hT hR hH z w hw hI t ν hg
  haveI := hcz
  subst hA
  have hsp : genPt 𝔐₀.ξ ⤳ centre (z ≫ h) := 𝔐₀.all _
  have hw₀ := hCoord z w hw
  have hI₀ := hInt z hI

  obtain ⟨t₀, ht₀⟩ := Flag.gr_gen_of_isFlagVBOn (Fl₀.sub (rootIdx D r).1)
    (p := ⟨centre (z ≫ h), 𝔐₀.all _⟩) (Set.mem_univ _) (rootIdx D r).2
  obtain ⟨ν₀, -, hn₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm E H D l Xo c O β Y S₀ Ω₀ K₀ J₀ y₀ 𝔐₀ Fl₀ hβ (z ≫ h) hI₀ _ _ t₀ ht₀
  have hgr₀ := (hn₀ t₀ ν₀).2 ⟨1, one_ne_zero, by rw [div_self ht₀.1]; exact CxVal.one hsp, by simp⟩

  have ecp : pushCpt hd ⟨centre z, 𝔐.all _⟩ = ⟨centre (z ≫ h), 𝔐₀.all _⟩ := Subtype.ext (by
    show h (z _) = (z ≫ h) _
    exact (Scheme.Hom.comp_apply z h _).symm)
  have hgen := hGen ⟨centre z, 𝔐.all _⟩ (fun p hp => not_inFibre 𝔐.ξ z (𝔐.all _) hp) _ _ t₀ (ecp ▸ ht₀)
  obtain ⟨ν₁, -, hn₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.GrNorm.exists_norm E H D l Xo c O β Y S Ω K J y 𝔐 Fl hβ z hI _ _ (i t₀) hgen
  have hit : i t₀ ≠ 0 := hgen.1
  obtain ⟨u', -, hu', e'⟩ := (hn₁ _ _).1 (hNorm z _ _ t₀ ν₀ hgr₀)
  have hu1 : u' = 1 := CxVal.unique hu' (by rw [div_self hit]; exact CxVal.one (𝔐.all _))
  obtain ⟨u₁, hu₁0, hu₁, eν⟩ := (hn₁ _ _).1 hg
  rw [hu1, norm_one, _root_.one_mul] at e'
  subst e'

  have hsec := hH (z ≫ h) _ hw₀ hI₀ t₀ ν₀ hgr₀
  choose c₀ hc₀ using hw₀.1
  choose c hc using hw.1
  have hc₀' : ∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0 := fun k => (hc₀ k).ne_zero
  have hc' : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  obtain ⟨u₀, hu₀, en₀⟩ := hsec.2.2 c₀ hc₀'
  obtain ⟨u, -, hu, eT⟩ := hR z w hw c c₀ hc' hc₀'
  have ha : ((pullHerm hv A₀).tensor T).a = a := by
    show pullDeg bk A₀.a + T.a = a
    rw [hT]
    abel
  have hM₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k (c₀ k) (hc₀ k)).1
  have hM : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c k) (hc k)).1
  have hm₀ : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) ≠ 0 :=
    (map_ne_zero i).2 (mul_ne_zero hM₀ hsec.1)
  refine (secNorm_iff_chart he hw c hc').2 ⟨u₁ ^ rootSgn D r * u₀ * u, ?_, ?_⟩
  · rw [ha]
    convert CxVal.mul (CxVal.mul (CxVal.zpow hu₁ hu₁0 (rootSgn D r)) (hVal z _ _ hu₀)) hu using 1
    rw [map_div₀, map_zpow₀, div_zpow]
    generalize i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ A₀.a k) * e₀) = m at hm₀
    generalize (∏ k, y ⟨k, c k⟩ ^ a k) * e = n
    have hz : i t₀ ^ rootSgn D r ≠ 0 := zpow_ne_zero _ hit
    field_simp
  · rw [ha, eν]
    show (‖u₁‖ * ν₀) ^ rootSgn D r * (A₀.h (fun p => w (blkV bk bx p)) * T.h w) = _
    rw [mul_zpow, norm_mul, norm_mul, norm_zpow]
    linear_combination (‖u₁‖ ^ rootSgn D r * T.h w) * en₀ + (‖u₁‖ ^ rootSgn D r * ‖u₀‖) * eT

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGeneratedSumSpecializationFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PeriodIndep

section Dual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem disjoint_sup_biSup {α I : Type} [CompleteLattice α] [IsModularLattice α] {t : I → α} (hind : iSupIndep t)
    (a b : I) : Disjoint (t a ⊔ t b) (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) := by
  by_cases hab : a = b
  · subst hab
    rw [sup_idem]
    exact hind.disjoint_biSup fun h => h.1 rfl
  · refine Disjoint.disjoint_sup_left_of_disjoint_sup_right (hind.disjoint_biSup fun h => h.2 rfl) ?_
    have h1 : t b ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) b (fun h => hab h.symm) le_rfl
    have h2 : (⨆ s ∈ {s | s ≠ a ∧ s ≠ b}, t s) ≤ ⨆ j, ⨆ (_ : j ≠ a), t j :=
      iSup₂_le fun s hs => le_iSup₂_of_le (f := fun j (_ : j ≠ a) => t j) s hs.1 le_rfl
    exact (hind a).mono_right (sup_le h1 h2)

theorem exists_dual_sup (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li, (∀ j l, π j (bb l : 𝔐.Li) = if j = l then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hsp⟩ := hfr
  obtain ⟨W, hW, hc⟩ := (disjoint_sup_biSup hind a b).symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.projectionOnto _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ x : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (x : 𝔐.Li) = x := fun x =>
    Submodule.projectionOnto_apply_left hc.symm x
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases e : s' = a ∨ s' = b
      · have hxs : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases e with rfl | rfl
          · exact Submodule.mem_sup_left ((hV _).symm ▸ hx)
          · exact Submodule.mem_sup_right ((hV _).symm ▸ hx)
        have hm : (⟨x, hxs⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype q := hxV
        rw [hsp] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show pr x = ⟨x, hxs⟩ from hpr ⟨x, hxs⟩, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        refine sum_mem fun k _ => ?_
        rw [smul_eq_mul]
        refine mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxW : x ∈ W := by
          push Not at e
          exact hW (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem e hx.2))
        have : pr x = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hxW
        simp [this]
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy

end Dual

theorem values_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel 𝔐.t.G z Vz) (e : Fin N → Vz), (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → (∀ k, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt (e k))) → LinearIndependent ℂ e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z h Vz _ _ MR e hfr hval
  classical
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, h⟩
    fun r hr => GrNorm.not_inFibre hξ h hr
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sup 𝔐 hind ⟨centre z, h⟩ hV hlat a b bb hfr
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (e k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z h Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg (bb k : 𝔐.Li) _ _ (hval k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact RootHt.ArchB.val_one h
    · exact RootHt.ArchB.val_zero h
  choose g hg using hg
  refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
  have := congrArg (g j) hw
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, hg, Finset.sum_ite_eq] using this

end GlobalTheory.CompanionTheory.Ar.PeriodIndep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ConstEmbedding

theorem exists_spMap {A : Type} [CommRing A] (x : Sp ℂ ⟶ Sp A) : ∃ ψ : A →+* ℂ, spMap ψ = x :=
  ⟨(Spec.preimage x).hom, by
    show Spec.map (CommRingCat.ofHom (Spec.preimage x).hom) = x
    simp⟩

theorem exists_extend (F : Type) [Field F] [NumberField F] (ψ : 𝓞 F →+* ℂ) :
    ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = ψ := by
  have hinj : Function.Injective ψ :=
    GlobalTheory.CompanionTheory.Ar.GrNorm.injective_of_algebraic (algebraMap (𝓞 F) F)
      (IsFractionRing.injective (𝓞 F) F) ψ
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun a => ?_⟩
  simp

theorem exists_embedding (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ)
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)) (hol : IsHolTo (Metric.ball 0 1) p) :
    ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  choose ψ hψ using fun u => exists_spMap (p u ≫ q)
  choose κ hκ using fun u => exists_extend F (ψ u)
  have hd : ∀ a : 𝓞 F, DifferentiableOn ℂ (fun b => κ b (a : F)) (Metric.ball 0 1) := by
    intro a
    have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hol q
    have h3 := (h2 ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv a)).2
    have hset : Metric.ball (0 : Fin n → ℂ) 1 ⊆ {b ∈ Metric.ball (0 : Fin n → ℂ) 1 | ⊤ ≤ (p b ≫ q) ⁻¹ᵁ ⊤} :=
      fun b hb => ⟨hb, le_top⟩
    refine (h3.mono hset).congr fun b _ => ?_
    show κ b (a : F) = valAt' (p b ≫ q) ⊤ _
    rw [← hψ b, ← hκ b]
    exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_spMap ((κ b).comp (algebraMap (𝓞 F) F)) a).symm
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  refine ⟨κ 0, fun u hu => ?_⟩
  have hc := GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.embedding_const_preconnected (convex_ball (0 : Fin n → ℂ) 1).isPreconnected κ hd hu h0
  rw [← hc, hκ u, hψ u]

end GlobalTheory.CompanionTheory.Ar.ConstEmbedding
end

