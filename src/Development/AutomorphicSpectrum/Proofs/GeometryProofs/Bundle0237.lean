module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0235
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MkChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeTorsion
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts

theorem chartRing_over_place_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ :=
  @PositivityTheory.Xgn.torsion_packing_facts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualLatticeBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dual_baseChange_fractionField : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) :=
  @PositivityTheory.Xgn.exists_dual_base_change

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEqStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_map_eq_of_thickenings_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y), (∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | exact GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionInjectiveSubalgebra
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem torsionAlong_of_fullTorsion : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i :=
  @PositivityTheory.Xgn.full_torsion_packing

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTLift

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_char_units {R Ω T : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field Ω]
    (κ : FractionRing R ≃+* Ω) [CommGroup T] {n : ℕ} (hn : 1 ≤ n) (c : T →* Ωˣ) (hc : ∀ t, c t ^ n = 1) :
    ∃ χ : T →* Rˣ, ∀ t, κ (algebraMap R (FractionRing R) (χ t : R)) = (c t : Ω) := by
  have hex : ∀ t, ∃ r : R, algebraMap R (FractionRing R) r = κ.symm (c t : Ω) := by
    intro t
    refine IsIntegrallyClosed.isIntegral_iff.1 ?_
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    have h1 : ((c t : Ω)) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one]
    rw [← map_pow, h1]
    simp
  choose r hr using hex
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective _ _
  let f : T →* R :=
    { toFun := r
      map_one' := hinj (by rw [hr]; simp)
      map_mul' := fun s t => hinj (by rw [map_mul, hr, hr, hr]; simp) }
  refine ⟨f.toHomUnits, fun t => ?_⟩
  have : ((f.toHomUnits t : Rˣ) : R) = r t := rfl
  rw [this, hr]
  simp

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsDomain R]

abbrev Tors (G : Over X) [GrpObj G] [IsCommMonObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) :
    Subgroup (Over.mk ξ ⟶ G) :=
  (powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker

theorem tors_pow {G : Over X} [GrpObj G] [IsCommMonObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    (t : Tors G ξ n) : t.1 ^ n = 1 := t.2

theorem exists_tors [CharZero Ω] [IsNoetherianRing R] (G : Over X) [GrpObj G] [IsCommMonObj G]
    (hS : IsSemiAbelian G) (κ : FractionRing R ≃+* Ω) (x : Spec (CommRingCat.of R) ⟶ X) {n : ℕ} (hn : 1 ≤ n)
    (hF : FullTorsion G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n) :
    ∃ (Γ : BT.QFGroup R (Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n)) (i : Γ.G.left ⟶ G.left),
      Γ.IsTorsionAlong G x n i ∧ ∀ (t : Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n)
        (g : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G),
        spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → g = t.1 := by
  have : CharZero R := (κ.toRingHom.comp (algebraMap R (FractionRing R))).charZero
  have e1 : spMap κ.symm.toRingHom ≫ spMap (κ.toRingHom.comp (algebraMap R _)) =
      spMap (algebraMap R (FractionRing R)) := by
    rw [spMap_comp_spMap]
    congr 1
    ext r
    simp
  have e2 : spMap κ.toRingHom ≫ spMap κ.symm.toRingHom = 𝟙 _ := by
    rw [spMap_comp_spMap]
    have : κ.toRingHom.comp κ.symm.toRingHom = RingHom.id Ω := by
      ext r
      simp
    rw [this]
    simp [spMap]
  set ξ := spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x with hξ
  have e3 : spMap κ.symm.toRingHom ≫ ξ = (BT.genPt R).hom ≫ x := by
    rw [hξ, ← Category.assoc, e1]
    rfl
  have e4 : spMap κ.toRingHom ≫ (BT.genPt R).hom ≫ x = ξ := by
    rw [← e3, ← Category.assoc, e2, Category.id_comp]
  let a : Over.mk ((BT.genPt R).hom ≫ x) ⟶ Over.mk ξ := Over.homMk (spMap κ.symm.toRingHom) e3
  let b : Over.mk ξ ⟶ Over.mk ((BT.genPt R).hom ≫ x) := Over.homMk (spMap κ.toRingHom) e4
  have hba : b ≫ a = 𝟙 _ := Over.OverMorphism.ext e2
  let τ : Tors G ξ n →* (Over.mk ((BT.genPt R).hom ≫ x) ⟶ G) :=
    { toFun := fun t => a ≫ t.1
      map_one' := MonObj.comp_one a
      map_mul' := fun s t => MonObj.comp_mul a s.1 t.1 }
  have hinj : Function.Injective τ := by
    intro s t h
    have h' : a ≫ s.1 = a ≫ t.1 := h
    have h2 := congrArg (b ≫ ·) h'
    simp only [← Category.assoc, hba, Category.id_comp] at h2
    exact Subtype.ext h2
  have hpow : ∀ t, τ t ^ n = 1 := by
    intro t
    show (a ≫ t.1) ^ n = 1
    rw [← MonObj.comp_pow, tors_pow, MonObj.comp_one]
  have hgeo : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (α : FractionRing R →+* Ω')
      (g : Over.mk (Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x) ⟶ G), g ^ n = 1 →
      ∃ t, g.left = Spec.map (CommRingCat.ofHom α) ≫ (τ t).left := by
    intro Ω' _ _ α g hg
    have e5 : spMap (α.comp κ.symm.toRingHom) = spMap α ≫ spMap κ.symm.toRingHom :=
      (spMap_comp_spMap _ _).symm
    have e6 : spMap (α.comp κ.symm.toRingHom) ≫ ξ = Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x := by
      rw [e5, Category.assoc, e3]
    let c : Over.mk (spMap (α.comp κ.symm.toRingHom) ≫ ξ) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x) :=
      Over.homMk (𝟙 _) (by simpa using e6.symm)
    have hg' : (c ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    obtain ⟨y, hy⟩ := hF Ω' (α.comp κ.symm.toRingHom) (c ≫ g) hg'
    let ψ : Over.mk (spMap (α.comp κ.symm.toRingHom) ≫ ξ) ⟶ Over.mk ξ :=
      Over.homMk (spMap (α.comp κ.symm.toRingHom)) rfl
    have hψ : ψ ≫ y = c ≫ g := Over.OverMorphism.ext hy.symm
    have hepi : Epi (spMap (α.comp κ.symm.toRingHom)) := by
      have : Flat (spMap (α.comp κ.symm.toRingHom)) := by
        rw [spMap, Flat.SpecMap_iff]
        exact RingHom.Flat.of_isField (Field.toIsField Ω) _
      have : Surjective (spMap (α.comp κ.symm.toRingHom)) := ⟨Function.surjective_to_subsingleton _⟩
      exact Flat.epi_of_flat_of_surjective _
    have hy1 : y ^ n = 1 := by
      have h3 : ψ ≫ y ^ n = ψ ≫ 1 := by rw [MonObj.comp_pow, hψ, hg', MonObj.comp_one]
      refine Over.OverMorphism.ext ?_
      exact (cancel_epi (spMap (α.comp κ.symm.toRingHom))).1 (congrArg (·.left) h3)
    refine ⟨⟨y, hy1⟩, ?_⟩
    have h4 : g.left = spMap (α.comp κ.symm.toRingHom) ≫ y.left := by
      have : (c ≫ g).left = g.left := Category.id_comp _
      rw [← this, hy]
    rw [h4, e5, Category.assoc]
    rfl
  obtain ⟨Γ, i, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion R (Tors G ξ n) X G hS x n hn τ hinj hpow hgeo
  refine ⟨Γ, i, h1, fun t g h => Over.OverMorphism.ext ?_⟩
  rw [← h, h2 t]
  show spMap κ.toRingHom ≫ spMap κ.symm.toRingHom ≫ t.1.left = _
  rw [← Category.assoc, e2, Category.id_comp]

theorem exists_form [IsIntegrallyClosed R] [IsNoetherianRing R] (G : Over X) [GrpObj G] [IsCommMonObj G]
    (hsm : Smooth G.hom) (κ : FractionRing R ≃+* Ω) (x : Spec (CommRingCat.of R) ⟶ X)
    {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) E)
    {T : Type} [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left) {n : ℕ}
    (hi : Γ.IsTorsionAlong G x n i) (χ : T →* Rˣ) :
    ∃ (L₀ : Type) (_ : AddCommGroup L₀) (_ : Module R L₀) (M₀ : LieModel G x L₀) (j : L₀ → E)
      (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E),
      (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) ∧
        Γ.IsHT i M₀ n χ w₀ ∧ ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)) := by
  obtain ⟨L₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R x
  obtain ⟨w₀, hw₀⟩ := _root_.PositivityTheory.UnitarySelfGeneration.ht_exists R T Γ X G x n i hi hsm L₀ M₀ χ
  letI : Algebra R Ω := (κ.toRingHom.comp (algebraMap R (FractionRing R))).toAlgebra
  letI : Module R E := Module.compHom E (algebraMap R Ω)
  have : IsScalarTower R Ω E := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj, hjs, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_baseChange X G R Ω x L₀ E M₀ M
  let β : L₀ →ₗ[R] E :=
    { toFun := j
      map_add' := map_add j
      map_smul' := fun a v => hjs a v }
  obtain ⟨-, -, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange X G R x L₀ M₀
  have hb : IsBaseChange Ω β := hbc Ω E M β hj
  refine ⟨L₀, _, _, M₀, j, w₀, hb.lift ((Algebra.linearMap R Ω) ∘ₗ w₀), hj, hw₀, fun v => ?_⟩
  exact hb.lift_eq ((Algebra.linearMap R Ω) ∘ₗ w₀) v

end GlobalTheory.CompanionTheory.Ar.HTLift

namespace GlobalTheory.CompanionTheory.Ar


open GlobalTheory.CompanionTheory.Ar.HTLift in
theorem htLat_exists_lifts : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ), (∃ U : X.Opens, q.1 ∈ U ∧ ∃ w : (Over.mk ξ ⟶ G) → Module.Dual Ω E, ∀ y, y ^ n = 1 → ∀ q' : Cpt ξ, q'.1 ∈ U → M.IsHTAt L n y q' (w y)) ∧ ∀ (y : Over.mk ξ ⟶ G) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  intro X _ Ω _ _ ξ hg hN G _ hS L n hn hF e hW E _ _ M q
  refine ⟨?_, fun y w w' hy hw => _root_.GlobalTheory.CompanionTheory.Ar.HtUniq.isHTAt_iff X Ω ξ hg hN G hS L n hn hF e hW E M y q w w' hy hw⟩
  obtain ⟨R, _, _, x, κ, hR, hI, hO, hq, -, hx⟩ := _root_.PositivityTheory.HtPt.Mk.ht_lat_chart X Ω ξ hg hN q
  have hc : IsCommMonObj G := hS.comm
  subst hx
  have key : ∀ y : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G, y ^ n = 1 →
      ∃ w : Module.Dual Ω E, ∀ q' : Cpt (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x),
        q'.1 ∈ Set.range x → M.IsHTAt L n y q' w := by
    intro y hy
    have hfin : Finite (Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n) := by
      have := hW.finite
      exact Finite.of_injective
        (fun t => (⟨t.1, tors_pow t⟩ : {z : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G // z ^ n = 1}))
        (fun s t h => Subtype.ext (congrArg Subtype.val h))
    obtain ⟨Γ, i, hi, ht⟩ := exists_tors G hS κ x hn hF
    let c : Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n →* Ωˣ :=
      MonoidHom.mk' (fun t => e y t.1) (fun s t => hW.mul_right y s.1 t.1 hy (tors_pow s) (tors_pow t))
    have hc1 : ∀ t, c t ^ n = 1 := by
      intro t
      rw [← map_pow]
      have : t ^ n = 1 := Subtype.ext (tors_pow t)
      rw [this, map_one]
    obtain ⟨χ, hχ⟩ := exists_char_units κ hn c hc1
    obtain ⟨L₀, _, _, M₀, j, w₀, w, hj, hH, hw⟩ := exists_form G hS.smooth κ x M Γ i hi χ
    refine ⟨w, fun q' hq' => _root_.GlobalTheory.CompanionTheory.Ar.HTChart.isHTAt_of_isHT X Ω _ hg hN G hS L n hn hF e hW E M R x κ rfl _ Γ i hi L₀ M₀ j hj y χ
      w₀ w hy ?_ hH hw q' hq'⟩
    intro t g h
    rw [ht t g h]
    exact hχ t
  choose! w hw using key
  exact ⟨x.opensRange, hq, w, fun y hy q' hq' => hw y hy q' hq'⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsHTAtIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie

theorem isHTAt_iff (h455 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange) (h876 : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.BT.section_eq_zero_of_val_generic)
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (L : LB G.left) {n : ℕ} (hn : n ≠ 0)
    (hfull : FullTorsion G ξ n) {E : Type} [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E)
    {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω)
    (hx : Spec.map (CommRingCat.ofHom (κ.toRingHom.comp (algebraMap R (FractionRing R)))) ≫ x = ξ)
    {T : Type} [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left) (htor : Γ.IsTorsionAlong G x n i)
    {L₀ : Type} [AddCommGroup L₀] [Module R L₀] (M₀ : LieModel G x L₀) (j : L₀ → E)
    (hj : ∀ v, (M.pt (j v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (κ.toRingHom.comp (algebraMap R (FractionRing R))))) ≫ (M₀.pt v).left)
    (y : Over.mk ξ ⟶ G) (χ : T →* Rˣ) (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E)
    (hW : ∀ (t : T) (k : Type) [Field k] [IsAlgClosed k] (a : Ω →+* k) (xk gk : Over.mk (spMap a ≫ ξ) ⟶ G) (c : kˣ),
      xk.left = spMap a ≫ y.left → gk.left = spMap a ≫ ptG κ.toRingHom i t →
        (Out.WeilIs G L n xk gk (unitOn c) ↔ (c : k) = a (κ (algebraMap R _ (χ t : R)))))
    (hHT : Γ.IsHT i M₀ n χ w₀) (hwj : ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)))
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a : R, κ (algebraMap R _ a) ∈ regAt ξ q)
    (w' : Module.Dual Ω E) : M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum R, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ (κ.toRingHom.comp (algebraMap R (FractionRing R)))
    (κ.injective.comp (IsFractionRing.injective R _)) x hx p q hp hsub
  obtain ⟨s, hs, hv⟩ := hHT
  have hcore := fun W f hval (e' : E) (v : epsAt (X.fromSpecStalk q.1) ⟶ G) (hv' : M.Extends q e' v) =>
    core_tan h455 M p.asIdeal.primeCompl Γ i x hzs (genMap ξ q) _ hg M₀ j hj n w₀ w hwj s hv W f hval e' v hv'.1 hv'.2
  obtain ⟨W₀, f₀, hW₀, hf₀⟩ := lift_sec G Γ x n i htor q.1 _ hzs s
  have hval₀ : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
      y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
        ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W₀, valAt (y ≫ i) W₀ h f₀ = valAt y ⊤ le_top s :=
    fun y b hb h => hf₀ y (Spec.map (CommRingCat.ofHom b)) (hb.trans (spec_comp _ _)) h
  have hlat := (lieLat_carrier X G Ω ξ E M q).1
  have hw : w ∈ M.omLat q := fun e' he' => by
    obtain ⟨v, hv'⟩ := (hlat e').1 he'
    obtain ⟨c, hc, -⟩ := hcore W₀ f₀ hval₀ e' v hv'
    exact ⟨c, hc.symm⟩
  have hn' : (n : Ω) ≠ 0 := Nat.cast_ne_zero.2 hn
  constructor
  · rintro ⟨-, W, f, hWm, hf, hd⟩
    have hsec : (i.app W).hom f - Γ.G.left.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ W ≤ ⊤)).op s = 0 := by
      refine h876 R T Γ (i ⁻¹ᵁ W) _ fun t h => ?_
      rw [valAt_sub, sub_eq_zero]
      refine Eq.trans ?_ (valAt_res _ _ ⊤ le_top h le_top s).symm
      rw [hs t]
      refine (valAt_comp (Γ.pt t).left i W h f).symm.trans ?_
      let k := AlgebraicClosure Ω
      let a : Ω →+* k := algebraMap Ω k
      let ψ : Over.mk (spMap a ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap a) rfl
      obtain ⟨g, hg1, hg2⟩ := tors_ex κ.toRingHom htor hx t
      let c : kˣ := Units.map ((a.comp κ.toRingHom).comp (algebraMap R (FractionRing R))).toMonoidHom (χ t)
      have e0 : (ψ ≫ g).left = spMap a ≫ ptG κ.toRingHom i t := by rw [← hg2]; rfl
      have e1 : (ψ ≫ g).left = Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i := by
        rw [e0, spec_comp, Category.assoc]
      have h1 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left ≫ i) ⁻¹ᵁ W :=
        fun z _ => h (by trivial)
      have h2 := hf k a (ψ ≫ y) (ψ ≫ g) c (by rw [e1]; exact h1) rfl (by rw [← comp_pow', hg1, MonObj.comp_one])
        ((hW t k a (ψ ≫ y) (ψ ≫ g) c rfl e0).2 rfl)
      apply (a.comp κ.toRingHom).injective
      exact (valAt_spec (a.comp κ.toRingHom) _ W h h1 f).symm.trans ((valAt_congr e1 W _ h1 f).symm.trans h2)
    have hval : ∀ {B : Type} [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (b : X.presheaf.stalk q.1 →+* B),
        y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R (X.presheaf.stalk q.1)))) →
          ∀ h : ⊤ ≤ (y ≫ i) ⁻¹ᵁ W, valAt (y ≫ i) W h f = valAt y ⊤ le_top s := by
      intro B _ y _ _ h
      refine (valAt_comp y i W h f).trans ?_
      rw [sub_eq_zero.1 hsec]
      exact valAt_res y (i ⁻¹ᵁ W) ⊤ le_top h le_top s
    refine ⟨(n : Ω)⁻¹ • (w' - w), fun e' he' => ?_, ?_⟩
    · obtain ⟨v, hv'⟩ := (hlat e').1 he'
      have hm : ⊤ ≤ v.left ⁻¹ᵁ W := HtUniq.tan_le v hv'.1 hWm
      obtain ⟨c, hc, hr⟩ := hcore W f hval e' v hv'
      obtain ⟨r, hr⟩ := hr hm
      obtain ⟨r', hr', he⟩ := hd e' v hv' hm
      have : ((n : Ω)⁻¹ • (w' - w)) e' = r' - genMap ξ q r := by
        have he' : w' e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * r' := he
        have hc' : w e' = genMap ξ q (BT.valAt v.left W hm f).snd + n * genMap ξ q r := by
          rw [hc, hr, map_add (f := _), map_mul, map_natCast]
          rfl
        rw [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hn', mul_sub, he', hc',
          add_sub_add_left_eq_sub]
      rw [this]
      exact sub_mem hr' ⟨r, rfl⟩
    · rw [← Nat.cast_smul_eq_nsmul Ω, smul_smul, mul_inv_cancel₀ hn', one_smul, add_sub_cancel]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨add_mem hw (nsmul_mem hu n), W₀, f₀, hW₀, ?_, ?_⟩
    · intro K _ _ a xk g' c h hxk hg' hweil
      obtain ⟨g₀, hg₀⟩ := hfull K a g' hg'
      have hg0 : g₀ ^ n = 1 := pow_descend a hg₀ hg'
      obtain ⟨t, ht⟩ := tors_pt κ.toRingHom htor hx g₀ hg0
      have hc₁ := (hW t K a xk g' c hxk (by rw [hg₀, ht])).1 hweil
      have e1 : g'.left = (Spec.map (CommRingCat.ofHom (a.comp κ.toRingHom)) ≫ (Γ.pt t).left) ≫ i := by
        rw [hg₀, ht, spec_comp]; simp only [ptG, Category.assoc]
      refine (valAt_congr e1 W₀ h (by rw [← e1]; exact h) f₀).trans ?_
      rw [hval₀ _ (a.comp (genMap ξ q)) (by
        rw [Category.assoc, Over.w, RingHom.comp_assoc, hg, ← RingHom.comp_assoc, spec_comp (algebraMap R _)]; rfl)]
      refine (valAt_spec (a.comp κ.toRingHom) (Γ.pt t).left ⊤ le_top le_top s).trans ?_
      rw [hs t, hc₁]
      rfl
    · intro e' v hv' h
      obtain ⟨c, hc', hr⟩ := hcore W₀ f₀ hval₀ e' v hv'
      obtain ⟨r, hr⟩ := hr h
      refine ⟨genMap ξ q r + u e', add_mem ⟨r, rfl⟩ (hu e' ((hlat e').2 ⟨v, hv'⟩)), ?_⟩
      rw [LinearMap.add_apply, LinearMap.smul_apply, hc', hr, map_add (f := _), map_mul, map_natCast, nsmul_eq_mul, mul_add,
        ← add_assoc]
      rfl

end GlobalTheory.CompanionTheory.HtLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorsionInjective
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem exists_qfGroup_of_generic_fullTorsion : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' :=
  @PositivityTheory.Xgn.exists_torsion_group_extension

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

