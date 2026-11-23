module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyEquivPiOfWeights
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.FromCube

abbrev CubeGen : Prop :=
  ∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB →
    ∃ t : LB.Gen (Theta P.A M), t.IsGen

theorem cube (h : CubeGen) : CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen _root_.GlobalTheory.laws_without_cohomology.1 h

theorem square (h : CubeGen) : SquareSt :=
  (GlobalTheory.AbSquare.square_of_cube h).2

theorem mulPull (h : CubeGen) : MulPullSt :=
  (GlobalTheory.MulPull.mulPull_of_cube_of_symm h (GlobalTheory.exists_gen_negLB _root_.GlobalTheory.laws_without_cohomology.1)).2

theorem kerPow (h : CubeGen) : KerPowSt :=
  (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.1

theorem weil (h : CubeGen) : WeilSt :=
  have g := _root_.GlobalTheory.laws_without_cohomology.1
  have lift := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.2
  have w₁ := GlobalTheory.CommutatorPairing.existsUnique_weilIs g lift
  GlobalTheory.weilSt_of_parts w₁ (GlobalTheory.weilIs_mul_left g)
    (GlobalTheory.weilIs_alternating_skew_natural g lift) (GlobalTheory.PairingLevels.weilIs_mul_iff g h lift w₁)

theorem symLift (h : CubeGen) : SymLiftSt :=
  (_root_.GlobalTheory.symLift_odd _root_.GlobalTheory.laws_without_cohomology.1 (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.2
    (GlobalTheory.exists_gen_negLB _root_.GlobalTheory.laws_without_cohomology.1)).2

theorem mulA_props (h : CubeGen) :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left) :=
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  GlobalTheory.AbLaw.MulN.mulA_finite_flat_surjective_etale
    (GlobalTheory.MulFinite.isFinite_mulA
      (GlobalTheory.MulPull.mulPull_of_cube_of_symm h (GlobalTheory.exists_gen_negLB _root_.GlobalTheory.laws_without_cohomology.1)).1
      _root_.GlobalTheory.laws_without_cohomology.2.2.1 gi)
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi)
    GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres GlobalTheory.T.formallyUnramified_mul_invertible_integer

theorem weilNondeg (h : CubeGen) : WeilNondegSt :=
  have g := _root_.GlobalTheory.laws_without_cohomology.1
  have lift := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.2
  GlobalTheory.weilNondeg_of_descent (GlobalTheory.torsion_invariant_descends (mulA_props h))
    (GlobalTheory.DescentPairing.exists_gen_transl_eq_pairing g (cube h)
      (GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lift
        (_root_.GlobalTheory.symLift_odd g lift (GlobalTheory.exists_gen_negLB g)).1) (weil h))

theorem charPair (h : CubeGen) : CharPairSt :=
  GlobalTheory.charPair_of_weil (weil h)
    (GlobalTheory.weilIs_alternating_skew_natural _root_.GlobalTheory.laws_without_cohomology.1
      (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.2)
    (weilNondeg h) (mulA_props h)

theorem sec_split (h : CubeGen) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) :=
  have g := _root_.GlobalTheory.laws_without_cohomology.1
  have lift := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube h).1).2.2
  GlobalTheory.sections_mulPull_split (GlobalTheory.MulPull.mulPull_of_cube_of_symm h (GlobalTheory.exists_gen_negLB g)).1
    (mulA_props h) (GlobalTheory.torsion_invariant_descends (mulA_props h))
    (GlobalTheory.DescentPairing.exists_gen_transl_eq_pairing g (cube h)
      (GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton g lift
        (_root_.GlobalTheory.symLift_odd g lift (GlobalTheory.exists_gen_negLB g)).1) (weil h))
    (charPair h) (weil h) (GlobalTheory.weilIs_alternating_skew_natural g lift)
    (GlobalTheory.twisted_pow_translate (GlobalTheory.AbSquare.square_of_cube h).1 (mulA_props h))

theorem all_of_cubeGen :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → CubeSt ∧ SquareSt ∧ MulPullSt ∧ KerPowSt ∧ WeilSt ∧ SymLiftSt ∧ WeilNondegSt ∧ CharPairSt ∧ (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) :=
  fun h => ⟨cube h, square h, mulPull h, kerPow h, weil h, symLift h, weilNondeg h, charPair h,
    mulA_props h, sec_split h⟩

end GlobalTheory.AbLaw.FromCube
