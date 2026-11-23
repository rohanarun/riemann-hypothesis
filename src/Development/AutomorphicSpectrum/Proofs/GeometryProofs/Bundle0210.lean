module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolution
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0112
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesTelescope
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.POmNPoly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TopMixedLimitOfResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AnalyticTypeDefinition

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_section_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StokesLimitIffPosOfResK
section
noncomputable section

namespace GlobalTheory.CompanionTheory.StokesCompare

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter _root_.Topology MeasureTheory
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Clauses

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

end Clauses

section Mass

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem degMu_nonneg (X : ComponentSetting D O Lt) : 0 ≤ degMu X.H := by
  classical
  have hN := MuHomDensityNonneg.proof (MuSheetLeviNonneg.proof SheetChartHolo.proof RefAlongSheet.proof)
  have hdeg : degMu X.H = ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) (fun _ => 1) := rfl
  rw [hdeg]
  unfold ptsIntegral
  split_ifs with hΨ
  · refine integral_nonneg_of_ae ?_
    filter_upwards [hN II Ψ K ι Ω E D O Lt X _ hΨ.choose_spec] with y hy
    exact finsum_nonneg fun w => finsum_nonneg fun _ => hy w
  · exact le_rfl

end Mass

end GlobalTheory.CompanionTheory.StokesCompare
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem anDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ), (∀ i, LinearIndependent (𝓞 E) (e i)) → ∃ Φ : CFn Xo c, ∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i) :=
  @PositivityTheory.Xgn.analytic_type_definition

end GlobalTheory.CompanionTheory.Ar.Flat
end

