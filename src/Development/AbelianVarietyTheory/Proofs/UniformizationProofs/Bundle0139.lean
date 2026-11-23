module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0138
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pelUnif_of_cdvr_unconditional :
    ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (t : SAB H (Sp V)) (A : PolAV (Sp (FractionRing V))) (gen : (Over.pullback (jK V)).obj t.G ≅ A.A), IsMonHom gen.hom → (∃ w : LB.Iso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen) → (∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)), S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj t.G)) → ∃ P : PELUnif (maximalIdeal V) t, P.A = A ∧ HEq P.U.gen gen ∧ P.TorsionIso :=
  _root_.GlobalTheory.UU.exists_pelUnif_of_cdvr _root_.GlobalTheory.UU.exists_degData_unif_unconditional _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.allSixLaws.2.2.1
    _root_.GlobalTheory.allSixLaws.2.2.2.1 _root_.GlobalTheory.allSixLaws.2.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateUnif

theorem rank_add_dim {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    Module.finrank ℤ D.toPre.X + D.toPre.P.g = A.g := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  have := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hR D A G U.toUnifPre 2 one_le_two
    (U.expand 2 one_le_two)
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    one_le_two).2
  exact Nat.pow_right_injective le_rfl (h₂.symm.trans h₁)

end GlobalTheory.TateUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem uniformisation_total_closed : USt :=
  _root_.GlobalTheory.LN.uniformisation_dvr _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.allSixLaws.2.2.1 _root_.GlobalTheory.allSixLaws.2.2.2.1
    _root_.GlobalTheory.allSixLaws.2.2.2.2.1

end GlobalTheory
end

