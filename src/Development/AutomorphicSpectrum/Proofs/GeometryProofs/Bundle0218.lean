module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0215
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeFreeEveryStalk
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FnFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_add_lattice_eq_of_isFn : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → ∀ (l : a.u.Λ) (w : Fin g → ℂ), θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | exact GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Fac.fn_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermSystemHeightFree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hfree_at_component_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r :=
  PositivityTheory.Xgn.hodge_free_every_stalk

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrame
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem gramAt_unique_of_polarisedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ Γ' : Matrix (Fin r) (Fin r) ℂ), HodgeMetric.PolarisedAt 𝔐.t z → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z b Γ' → Γ = Γ' := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ Γ' hP h1 h2
  obtain ⟨v, hv, hΓ⟩ := h1
  obtain ⟨v', hv', hΓ'⟩ := h2
  have hgen : GlobalTheory.CompanionTheory.Ar.IsCptGen 𝔐.ξ := 𝔐.tie.gen
  have hvv : v = v' := funext fun i => GlobalTheory.CompanionTheory.Ar.LieModel.ValAt.unique hgen (hv i) (hv' i)
  subst hvv
  obtain ⟨V, _, _, ⟨M'⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H 𝔐.X 𝔐.t z V M' hP
  have hpre : ∀ i, ∃ e, M'.pt e = v i := by
    intro i
    have hT : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G z (v i) := by
      obtain ⟨-, hT, -⟩ := hΓ i i
      exact hT
    exact M'.onto (v i) hT
  ext p q
  obtain ⟨e, he⟩ := hpre p
  obtain ⟨f, hf⟩ := hpre q
  have k1 := (hh e f (Γ p q)).1 (by rw [he, hf]; exact hΓ p q)
  have k2 := (hh e f (Γ' p q)).1 (by rw [he, hf]; exact hΓ' p q)
  rw [k1, k2]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixTwoFrames
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem valAt_sum_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Type} [AddCommGroup L] [Module Ω L] (M : LieModel G ξ L)
    {z : Spec (CommRingCat.of ℂ) ⟶ X} {V : Type} [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
    (hz : genPt ξ ⤳ centre z) {I : Type} (s : Finset I) (b : I → L) (x : I → V)
    (hx : ∀ p, M.ValAt z (b p) (Mz.pt (x p))) (a : I → Ω) (c : I → ℂ) (hc : ∀ p, ValAt ξ z (a p) (c p)) :
    M.ValAt z (∑ p ∈ s, a p • b p) (Mz.pt (∑ p ∈ s, c p • x p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa [Mz.pt_zero] using M.valAt_zero hz
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, Finset.sum_insert hp, Mz.add]
    refine LieModel.ValAt.add ?_ ih
    obtain ⟨h1, g, hg, hg'⟩ := hc p
    have := (hx p).smul h1 g
    rw [hg, hg', ← Mz.pt_smul] at this
    exact this

theorem gramAt_change (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b b' : Fin r → 𝔐.Li)
    (Γ Γ' : Matrix (Fin r) (Fin r) ℂ) (T : Matrix (Fin r) (Fin r) Ω) (Tz : Matrix (Fin r) (Fin r) ℂ)
    (hP : HodgeMetric.PolarisedAt 𝔐.t z) (hG : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) (hG' : 𝔐.M.GramAt 𝔐.t.PP.L z b' Γ')
    (hb : ∀ q, b' q = ∑ p, T p q • b p) (hT : ∀ p q, ValAt 𝔐.ξ z (T p q) (Tz p q)) :
    Γ' = Tz.conjTranspose * Γ * Tz := by
  obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H 𝔐.X 𝔐.t z V Mz hP
  obtain ⟨v, hv, hΓ⟩ := hG
  obtain ⟨v', hv', hΓ'⟩ := hG'
  choose x hx using fun p => Mz.onto (v p) (hv p).isTanAt
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have key : ∀ q, Mz.pt (∑ p, Tz p q • x p) = v' q := fun q => by
    have h1 := valAt_sum_smul 𝔐.M Mz hz Finset.univ b x (fun p => by rw [hx]; exact hv p)
      (fun p => T p q) (fun p => Tz p q) (fun p => hT p q)
    rw [← hb q] at h1
    exact h1.unique 𝔐.tie.gen (hv' q)
  have e1 : ∀ p q, Γ p q = h (x p) (x q) := fun p q =>
    (hh _ _ _).1 (by rw [hx, hx]; exact hΓ p q)
  have e2 : ∀ p q, Γ' p q = h (∑ i, Tz i p • x i) (∑ j, Tz j q • x j) := fun p q =>
    (hh _ _ _).1 (by rw [key, key]; exact hΓ' p q)
  ext p q
  rw [e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, e1, map_sum, LinearMap.sum_apply, map_smul,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroCoordsOfNonzeroVectorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_coords_of_nonzero_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.len σ x ^ 2 = Real.pi * (a.herm c c).re → x ≠ 0 → c ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.FrameZero.coord_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx

theorem not_inFibre_centre {Ω : Type} [Field Ω] [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) :
    ¬ InFibre ξ p ⟨centre z, hz⟩ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hs : (Scheme.stalkClosedPointTo z).hom (p : X.presheaf.stalk (centre z)) ≠ 0 := fun h0 =>
    hp0 ((map_natCast (Scheme.stalkClosedPointTo z).hom p).symm.trans h0)
  obtain ⟨u, hu⟩ := CxVal.isUnit _ hs
  have hg : genMap ξ ⟨centre z, hz⟩ (p : X.presheaf.stalk (centre z)) = (p : Ω) := map_natCast _ _
  intro h
  refine h ⟨Nat.cast_ne_zero.2 hp.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  have h1 : genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = (p : Ω) := by rw [hu, hg]
  have h2 : genMap ξ ⟨centre z, hz⟩ ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)) *
      genMap ξ ⟨centre z, hz⟩ (u : X.presheaf.stalk (centre z)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem posDef_of_dual {V : Type} [AddCommGroup V] [Module ℂ V] (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) {N : ℕ} (x : Fin N → V)
    (g : Fin N → V →ₗ[ℂ] ℂ) (hg : ∀ j k, g j (x k) = if j = k then 1 else 0) :
    (Matrix.of fun p q => h (x p) (x q)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨Matrix.IsHermitian.ext fun p q => ?_, fun c hc => ?_⟩
  · simp only [Matrix.of_apply]
    rw [hh (x p) (x q)]
    simp
  · set u : V := ∑ k, c k • x k with hu
    have e : star c ⬝ᵥ (Matrix.of fun p q => h (x p) (x q)).mulVec c = h u u := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hu, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, dotProduct, Matrix.mulVec,
        Matrix.of_apply, Finset.mul_sum, Pi.star_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [RCLike.star_def]
      ring
    have hu0 : u ≠ 0 := fun h0 => hc (funext fun j => by
      have := congrArg (g j) h0
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [hu, map_sum, hg, Finset.sum_ite_eq] using this)
    rw [e, Complex.pos_iff]
    refine ⟨hp u hu0, ?_⟩
    have := (Complex.conj_eq_iff_im.1 (hh u u).symm)
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_dual_sum (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hV : ∀ s, 𝔐.V s q = 𝔐.dR s q) (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (a b : CMType H ⊕ CMType H) {N : ℕ}
    (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b))
    (hfr : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb q) :
    ∃ π : Fin N → Module.Dual Ω 𝔐.Li,
      (∀ j k, π j ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) = if j = k then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨hli, hspan⟩ := hfr
  have hdis : Disjoint (𝔐.Vgen a ⊔ 𝔐.Vgen b) (⨆ s ∈ ({a, b} : Set (CMType H ⊕ CMType H))ᶜ, 𝔐.Vgen s) :=
    (hind.disjoint_biSup_biSup (s := {a, b}) (t := {a, b}ᶜ) disjoint_compl_right).mono_left
      (sup_le (le_biSup 𝔐.Vgen (by simp)) (le_biSup 𝔐.Vgen (by simp)))
  obtain ⟨C, hC, hc⟩ := hdis.symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := Submodule.projectionOnto _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω bb) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (bb l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hpr : ∀ w : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b), pr (w : 𝔐.Li) = w := fun w =>
    Submodule.projectionOnto_apply_left hc.symm w
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp pr), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, hpr, hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases hs : s' ∈ ({a, b} : Set (CMType H ⊕ CMType H))
      · have hxW : x ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
          rcases hs with rfl | rfl
          · exact Submodule.mem_sup_left hx.2
          · exact Submodule.mem_sup_right hx.2
        have hxV : x ∈ 𝔐.V a q ⊔ 𝔐.V b q := by
          rcases hs with rfl | rfl
          · rw [hV s']; exact Submodule.mem_sup_left hx
          · rw [hV s']; exact Submodule.mem_sup_right hx
        have hm : (⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) ∈
            (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) q := hxV
        rw [hspan] at hm
        obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
        have e1 : ∀ k, (c' k • bb k) = ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := fun _ => rfl
        have e2 : pr x = ∑ k, ((c' k : regAt 𝔐.ξ q) : Ω) • bb k := by
          rw [show x = ((⟨x, hxW⟩ : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) from rfl, hpr, ← hc']
          exact Finset.sum_congr rfl fun k _ => e1 k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [LinearMap.comp_apply, e2, map_sum, map_smul, hgb, LinearMap.proj_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        refine sum_mem fun k _ => mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxC : x ∈ C := hC (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem hs hx.2))
        have : pr x = 0 := Submodule.projectionOnto_apply_of_mem_right hc.symm hxC
        simp [this]
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy

theorem exists_gramAt_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre z), HodgeMetric.PolarisedAt 𝔐.t z → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre z, h⟩ → ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) Γ ∧ Γ.PosDef := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 a b N bb z hgen hpol hfr
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_centre hgen hr
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨f, hHI, hh, hp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H 𝔐.X 𝔐.t z Vz MR hpol
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sum 𝔐 hind ⟨centre z, hgen⟩ hV hlat a b bb hfr
  have hbL : ∀ k, ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.M.lat ⟨centre z, hgen⟩ := fun k => by
    have hm : bb k ∈ (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype) ⟨centre z, hgen⟩ := by
      rw [hfr.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    have hm' : ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) ∈ 𝔐.V a ⟨centre z, hgen⟩ ⊔ 𝔐.V b ⟨centre z, hgen⟩ := hm
    rw [hV, hV] at hm'
    refine (sup_le ?_ ?_ : 𝔐.dR a ⟨centre z, hgen⟩ ⊔ 𝔐.dR b ⟨centre z, hgen⟩ ≤ 𝔐.M.lat ⟨centre z, hgen⟩) hm'
    · exact fun x hx => hx.1
    · exact fun x hx => hx.1
  have hval : ∀ k, ∃ x : Vz, 𝔐.M.ValAt z ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li) (MR.pt x) := fun k => by
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff z _).2 ⟨hgen, hbL k⟩
    obtain ⟨x, rfl⟩ := MR.onto w hw.isTanAt
    exact ⟨x, hw⟩
  choose x hx using hval
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (x k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg _ _ _ (hx k) ?_⟩
    rw [hπ j k]
    split_ifs
    · exact CxVal.one hgen
    · exact ⟨hgen, 0, map_zero _, map_zero _⟩
  choose g hg using hg
  exact ⟨Matrix.of fun p q => f (x p) (x q), ⟨fun k => MR.pt (x k), hx, fun p q => (hHI _ _ _).2 rfl⟩,
    posDef_of_dual f hh hp x g hg⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx
end
end

