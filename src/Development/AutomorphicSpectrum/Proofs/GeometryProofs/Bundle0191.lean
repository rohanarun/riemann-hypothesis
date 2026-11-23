module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0186
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0187
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImageStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | exact GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image | (intros; apply GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameArchimedeanStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ s : CMType H ⊕ CMType H, ∃ σ : 𝓞 E →+* T.V, (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) ∧ ∀ a, algebraMap T.V T.Fr (σ a) = io (labelEmb c s a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.sigma_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameLocalBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_local_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)), ∃ w : EC, FinRd.Roots.IsFrameVec Or io zT MC w s i ∧ Or.𝔐.M.ValAt (FinRd.Roots.gen T zV) (Or.Fl.b s i) (MC.pt w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.frame_value <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameNonarchimedeanStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_nonarchimedean : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → InFibre Or.𝔐.ξ p ⟨centre zV, Or.𝔐.all _⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.inFibre_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameFinal
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

set_option backward.isDefEq.respectTransparency false

theorem exists_factor' {O' R Ω C : Type} [CommRing O'] [CommRing R] [CommRing Ω] [CommRing C] (g : O' →+* Ω)
    (cl : O' →+* C) (hg : Function.Injective g) (φ : R →+* Ω) (ψ : R →+* C)
    (h : ∀ r, ∃ s, g s = φ r ∧ cl s = ψ r) : ∃ θ : R →+* O', g.comp θ = φ ∧ cl.comp θ = ψ := by
  choose θ h1 h2 using h
  exact ⟨{ toFun := θ
           map_one' := hg (by simp [h1])
           map_mul' := fun a b => hg (by simp [h1])
           map_zero' := hg (by simp [h1])
           map_add' := fun a b => hg (by simp [h1]) }, RingHom.ext h1, RingHom.ext h2⟩

theorem pts_eq' {O' Ω R₀ : Type} [CommRing O'] [Field Ω] [CommRing R₀] (g : O' →+* Ω) (hg : Function.Injective g)
    {B : Scheme.{0}} (s : B ⟶ Sp R₀) [IsSeparated s] {a b : Sp O' ⟶ B} (h : spMap g ≫ a = spMap g ≫ b) : a = b := by
  haveI : IsDomain O' := hg.isDomain g
  haveI : IsDominant (spMap g) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot g).1 hg]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated s ?_ (spMap g) h
  refine ext_of_isDominant (spMap g) ?_
  rw [← Category.assoc, h, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.PtEq

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots


open PtEq in
set_option maxHeartbeats 600000 in
theorem ptY_eq_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → (letI := io.toAlgebra; Small.ptY Y zT = FinRd.Roots.gen T zV ≫ Or.𝔐.f) := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hv hG la T io e y evT zT t hI zV hR
  letI := io.toAlgebra
  letI := Small.cstAlg Or
  obtain ⟨-, -, -, -, -, -, ⟨q, φ, ψ, yq, hφ, hψ, hr⟩, -⟩ := hI
  have hgen : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  let P : Cpt Or.𝔐.ξ := ⟨centre (gen T zV), hgen⟩
  have hinj : Function.Injective (genMap Or.𝔐.ξ P) := Or.𝔐.tie.gen.inj P
  have hreg : ∀ r, ∃ s', genMap Or.𝔐.ξ P s' = φ.toRingHom r ∧
      (Scheme.stalkClosedPointTo (gen T zV)).hom s' = ψ.toRingHom r := fun r => by
    obtain ⟨h, e'⟩ := hr r
    obtain ⟨h', s', hs, hs'⟩ := hR ⟨φ r, h⟩
    exact ⟨s', hs, hs'.trans e'.symm⟩
  obtain ⟨θ, hθ1, hθ2⟩ := exists_factor' _ _ hinj φ.toRingHom ψ.toRingHom hreg
  have hsep : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have he : Or.𝔐.X.fromSpecStalk P.1 ≫ Or.𝔐.f = spMap θ ≫ Small.ptY Y yq := by
    refine pts_eq' (genMap Or.𝔐.ξ P) hinj Y.s ?_
    rw [← Category.assoc, ← Category.assoc]
    have e1 : spMap (genMap Or.𝔐.ξ P) ≫ Or.𝔐.X.fromSpecStalk P.1 = Or.𝔐.ξ := LieTangent.spec_genMap _ _
    rw [e1, ← Fr.pt_eq, Small.ptY_map Y hφ, ← hθ1, LieTangent.spec_comp]
  have e2 : spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ Or.𝔐.X.fromSpecStalk P.1 = gen T zV :=
    LieTangent.spec_centre (gen T zV)
  rw [Small.ptY_map Y hψ]
  have e3 : ψ.toRingHom = (Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ := hθ2.symm
  have e4 : spMap ((Scheme.stalkClosedPointTo (gen T zV)).hom.comp θ) =
      spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ spMap θ := (LieTangent.spec_comp θ _).symm
  rw [e3, e4, Category.assoc]
  exact (congrArg (fun u => spMap (Scheme.stalkClosedPointTo (gen T zV)).hom ≫ u) he.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun u => u ≫ Or.𝔐.f) e2))

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianExtensionOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem spMap_dualMap_comp_alg (V K : Type) [CommRing V] [Field K] [Algebra V K] :
    spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) =
      spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) := by
  have e : (dualMap (algebraMap V K)).comp (algebraMap V (DualNumber V)) =
      (algebraMap K (DualNumber K)).comp (algebraMap V K) := by
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]

theorem tan_iff_of_generic : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] (T : Over (Sp V)) [GrpObj T] [IsCommMonObj T]
    (GK : Over (Sp K)) [GrpObj GK] (z : Sp V ⟶ X) (φ₀ : GK.left ⟶ T.left) (φ₁ : GK.left ⟶ Gx.left),
    IsSemiAbelian Gx → IsSemiAbelian T → IsGrpPullback GK T (spMap (algebraMap V K)) φ₀ →
    IsGrpPullback GK Gx (spMap (algebraMap V K) ≫ z) φ₁ → ∀ u : epsAt (𝟙 (Sp K)) ⟶ GK, IsTanAt GK (𝟙 _) u →
    ((∃ a : epsAt (𝟙 (Sp V)) ⟶ T, IsTanAt T (𝟙 _) a ∧ u.left ≫ φ₀ = spMap (dualMap (algebraMap V K)) ≫ a.left) ↔
      ∃ a : epsAt z ⟶ Gx, IsTanAt Gx z a ∧ u.left ≫ φ₁ = spMap (dualMap (algebraMap V K)) ≫ a.left) := by
  intro V K _ _ _ _ _ _ X Gx _ _ T _ _ GK _ z φ₀ φ₁ hG hT h₀ h₁ u hu
  have hp := isGrpPullback_pullback Gx z
  have hS : IsSemiAbelian ((Over.pullback z).obj Gx) := IsSemiAbelian.pullback z Gx hG
  have wφ : φ₁ ≫ Gx.hom = (GK.hom ≫ spMap (algebraMap V K)) ≫ z := by
    rw [h₁.1.w, Category.assoc]
  let φ' : GK.left ⟶ ((Over.pullback z).obj Gx).left := hp.1.lift φ₁ (GK.hom ≫ spMap (algebraMap V K)) wφ
  have eφ : φ' ≫ pullback.fst Gx.hom z = φ₁ := hp.1.lift_fst _ _ _
  have eσ : φ' ≫ ((Over.pullback z).obj Gx).hom = GK.hom ≫ spMap (algebraMap V K) := hp.1.lift_snd _ _ _
  have hn : IsGrpPullback GK ((Over.pullback z).obj Gx) (spMap (algebraMap V K)) φ' :=
    IsGrpPullback.cancel hp (h₁.congr rfl eφ.symm) eσ
  obtain ⟨ET, _, _, ⟨MT⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_exists (Sp V) T V (𝟙 _)
  obtain ⟨EG, _, _, ⟨MG⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_exists X Gx V z
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main V X z Gx ((Over.pullback z).obj Gx) _ EG hp).1 MG
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie V K T ((Over.pullback z).obj Gx) GK GK φ₀ φ' hT hS h₀ hn (𝟙 GK) ET EG MT M₀
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie V K ((Over.pullback z).obj Gx) T GK GK φ' φ₀ hS hT hn h₀ (𝟙 GK) EG ET M₀ MT
  constructor
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MT.onto a ha
    have l := hf x u e
    refine ⟨MG.pt (f x), MG.tan _, ?_⟩
    have l' : u.left ≫ φ' = spMap (dualMap (algebraMap V K)) ≫ (M₀.pt (f x)).left := by
      simpa using l
    rw [← eφ, ← Category.assoc, l', Category.assoc, hM₀]
  · rintro ⟨a, ha, e⟩
    obtain ⟨x, rfl⟩ := MG.onto a ha
    have l : u.left ≫ φ' = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap V K)) ≫ (M₀.pt x).left := by
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, eφ, e, Category.assoc, hM₀]
      · rw [Category.assoc, eσ, ← Category.assoc, Over.w u, Category.assoc, Over.w (M₀.pt x)]
        show (spMap (algebraMap K (DualNumber K)) ≫ 𝟙 _) ≫ spMap (algebraMap V K) =
          spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _
        rw [Category.comp_id, Category.comp_id, spMap_dualMap_comp_alg]
    have l₂ := hg x u l
    refine ⟨MT.pt (g x), MT.tan _, ?_⟩
    simpa using l₂

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeEq
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.DvrExtension

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem spMap_genMap_comp (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h : spMap (genMap ξ p) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) := by
    rw [← Spec.map_comp]
    rfl
  have h₁ : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 = X.fromSpecStalk (genPt ξ) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk p.2
  rw [h, Category.assoc]
  exact (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h₁).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem isFractionRing_genMap (h : IsCptGen ξ) (p : Cpt ξ) :
    letI := (genMap ξ p).toAlgebra
    IsFractionRing (X.presheaf.stalk p.1) Ω := by
  letI := (genMap ξ p).toAlgebra
  haveI : FaithfulSMul (X.presheaf.stalk p.1) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (h.inj p)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨⟨_, a, rfl⟩, ⟨_, b, rfl⟩, e⟩ := RegAtRing.exists_div h p z
  exact ⟨a, b, e⟩

theorem spec_dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (k : R →+* R') :
    Spec.map (CommRingCat.ofHom (dualMap k)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫ Spec.map (CommRingCat.ofHom k) := by
  have e : (dualMap k).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp k := by
    ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]

section Move

variable {R : Type} [CommRing R] {x : Sp R ⟶ X} {k : R →+* Ω} {G G' : Over X} [GrpObj G] [GrpObj G']
  {GΩ : Over (Sp Ω)} [GrpObj GΩ] {φ : GΩ.left ⟶ G.left} {φ' : GΩ.left ⟶ G'.left}
  {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} {ψ' : G₀.left ⟶ G'.left} {κ : GΩ.left ⟶ G₀.left}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem tangent_transport_dvr (hψ : IsGrpPullback G₀ G x ψ) (hψ' : IsGrpPullback G₀ G' x ψ')
    (hκ : κ ≫ G₀.hom = GΩ.hom ≫ spMap k) (e₁ : κ ≫ ψ = φ) (e₂ : κ ≫ ψ' = φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E) (e : E)
    (tie : ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (y : Sp R ⟶ X) (hy : 𝟙 _ ≫ x = y) (v : epsAt y ⟶ G) (hv : IsTanAt G y v)
    (hve : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) :
    ∃ v' : epsAt y ⟶ G', IsTanAt G' y v' ∧
      (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v'.left := by
  subst hy
  obtain ⟨w, hw, hw'⟩ := tie
  let v₀ : epsAt (𝟙 (Sp R)) ⟶ G₀ := LieMove.liftEps hψ v
  have hv₀ : v₀.left ≫ ψ = v.left := LieMove.liftEps_left hψ v
  have t₀ : IsTanAt G₀ (𝟙 _) v₀ := (LieMove.tan_iff hψ v₀).2 (by
    rw [show LieMove.pushEps hψ v₀ = v from LieMove.push_lift hψ v]; exact hv)
  have key : Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v₀.left = w.left ≫ κ := by
    refine hψ.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hv₀, e₁, hw, hve]
    · have a := Over.w v₀
      have b := Over.w w
      dsimp at a b
      rw [Category.assoc, Category.assoc, a, hκ, ← Category.assoc (Over.Hom.left w), b]
      simp only [Category.comp_id]
      exact spec_dualMap_alg k
  refine ⟨LieMove.pushEps hψ' v₀, (LieMove.tan_iff hψ' v₀).1 t₀, ?_⟩
  rw [LieMove.pushEps_left, ← Category.assoc, key, Category.assoc, e₂, hw']

theorem tan_move_of_dvr [IsDomain R] [IsDiscreteValuationRing R]
    (hk : letI := k.toAlgebra; IsFractionRing R Ω) (hx : spMap k ≫ x = ξ) (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E) (e : E)
    (tie : ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (v : epsAt x ⟶ G) (hv : IsTanAt G x v)
    (hve : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left) :
    ∃ v' : epsAt x ⟶ G', IsTanAt G' x v' ∧
      (M'.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v'.left := by
  subst hx
  letI := k.toAlgebra
  haveI : IsFractionRing R Ω := hk
  obtain ⟨G₀, _, ψ, ψ', κ, hψ, hψ', hκ, e₁, e₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.semiAbelian_commonModel R Ω X X x x G G' GΩ φ φ' hG hG' hφ hφ'
  exact tangent_transport_dvr hψ hψ' hκ.1.w e₁ e₂ M M' e tie x (Category.id_comp x) v hv hve

theorem extends_move (hξ : IsCptGen ξ) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hφ : IsGrpPullback GΩ G ξ φ) (hφ' : IsGrpPullback GΩ G' ξ φ')
    (M : LieModel G ξ E) (M' : LieModel G' ξ E)
    (tie : ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left)
    (p : Cpt ξ) [IsDomain (X.presheaf.stalk p.1)] [IsDiscreteValuationRing (X.presheaf.stalk p.1)]
    (e : E) (h : ∃ v, M.Extends p e v) : ∃ v, M'.Extends p e v := by
  obtain ⟨v, hv, hve⟩ := h
  exact tan_move_of_dvr (isFractionRing_genMap hξ p) (spMap_genMap_comp p) hG hG' hφ hφ' M M' e (tie e) v hv hve

end Move

theorem lat_eq_of_dvr : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → ∀ p : Cpt ξ, (∃ _ : IsDomain (X.presheaf.stalk p.1), IsDiscreteValuationRing (X.presheaf.stalk p.1)) → M.lat p = M'.lat p := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hG hG' hφ hφ' E _ _ M M' tie p hp
  obtain ⟨_, _⟩ := hp
  have e : {e | ∃ v, M.Extends p e v} = {e | ∃ v, M'.Extends p e v} := Set.ext fun e =>
    ⟨extends_move hξ hG hG' hφ hφ' M M' tie p e,
      extends_move hξ hG' hG hφ' hφ M' M (fun e => by
        obtain ⟨v, a, b⟩ := tie e
        exact ⟨v, b, a⟩) p e⟩
  simp only [LieModel.lat]
  rw [e]

end GlobalTheory.CompanionTheory.Ar.DvrExtension
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianPullbackTangentMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_cart_to_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)),
    ∃ φ₁ : tK.G.left ⟶ Y.t.G.left, IsGrpPullback tK.G Y.t.G (y ≫ Y.j) φ₁ ∧
      ∀ (u : epsAt (𝟙 (Sp K)) ⟶ tK.G) (v : epsAt (under y) ⟶ Xo.univ.t.G) (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G),
        SameVec Y y v v' → u.left ≫ m.φ = v.left → u.left ≫ φ₁ = v'.left := by
  intro E _ _ _ H D l Xo c O _ β Y K _ y tK m
  have hp : IsPullback Y.m0.toSABMap.φ Y.oF.t.G.hom Xo.univ.t.G.hom (pullback.fst _ _) := Y.m0.cart.1
  have hw : m.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc]; exact m.cart.1.w
  let φ' : tK.G.left ⟶ Y.oF.t.G.left := hp.lift m.φ (tK.G.hom ≫ y) hw
  have h1 : φ' ≫ Y.m0.toSABMap.φ = m.φ := hp.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = tK.G.hom ≫ y := hp.lift_snd _ _ _
  have hn : IsGrpPullback tK.G Xo.univ.t.G (y ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) :=
    by rw [h1]; exact m.cart
  have hc : IsGrpPullback tK.G Y.oF.t.G y φ' := IsGrpPullback.cancel Y.m0.toSABMap.cart hn h2
  refine ⟨φ' ≫ Y.m.φ, IsGrpPullback.comp hc Y.m.cart, ?_⟩
  rintro u v v' ⟨u', a, b, e⟩ huv
  have hu : u.left ≫ φ' = u' := by
    apply hp.hom_ext
    · rw [Category.assoc, h1, huv, b]
    · have wu : u.left ≫ tK.G.hom = spMap (algebraMap K (DualNumber K)) ≫ 𝟙 (Sp K) := Over.w u
      rw [Category.assoc, h2, ← Category.assoc, wu, a, Category.comp_id]
  rw [← Category.assoc, hu, e]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLieModelLift
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open _root_.CategoryTheory.Limits MonObj

theorem exists_val_of_isTan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (Ψ : G.G.left ⟶ tX.G.left), IsGrpPullback G.G tX.G zV Ψ → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] (MC : LieModel tX.G (FinRd.Roots.gen T zV) EC) (v : epsOver T.V T.V ⟶ G.G), IsTan v → ∃ w : EC, (MC.pt w).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ := by
  intro E _ _ _ H X tX T zV G Ψ hΨ EC _ _ MC v hv
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ (epsOver T.V T.V).hom =
      Spec.map (CommRingCat.ofHom (algebraMap T.Fr (DualNumber T.Fr))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [LieTangent.spec_comp, LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hover : (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ) ≫ tX.G.hom =
      (epsAt (FinRd.Roots.gen T zV)).hom := by
    have hw : v.left ≫ G.G.hom = (epsOver T.V T.V).hom := Over.w v
    rw [Category.assoc, Category.assoc, hΨ.1.w, ← Category.assoc v.left, hw, ← Category.assoc, hbase,
      Category.assoc]
    rfl
  let vt : epsAt (FinRd.Roots.gen T zV) ⟶ tX.G := Over.homMk _ hover
  have ht : GlobalTheory.CompanionTheory.Ar.IsTanAt tX.G (FinRd.Roots.gen T zV) vt := by
    have hv' : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.V T.V T.V).toRingHom) ≫ v.left =
        (1 : ptOver T.V T.V ⟶ G.G).left := hv
    have h1 := FrameValue.one_left_grp hΨ (Spec.map (CommRingCat.ofHom (algebraMap T.V T.V))) _ rfl
    have hp : Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T.V T.V)) ≫ zV = FinRd.Roots.gen T zV := by
      rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    have h2 := FrameValue.one_left_pull (G := tX.G) (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) _ _ hp
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom T.Fr T.Fr T.Fr).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap T.V T.Fr))) ≫ v.left ≫ Ψ = _
    rw [← Category.assoc, LieTangent.spec_fst_dual, Category.assoc, ← Category.assoc _ v.left Ψ, hv']
    exact (congrArg (fun u => Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ u) h1).trans h2
  obtain ⟨w, hw⟩ := MC.onto vt ht
  exact ⟨w, congrArg (fun u => u.left) hw⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

