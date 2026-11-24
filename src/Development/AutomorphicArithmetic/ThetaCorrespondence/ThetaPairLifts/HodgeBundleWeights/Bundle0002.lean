module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasPhiExistsExtAndUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PhiCOfNoIntegralForm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CubicalStructureConstSectionPullback
section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.ConstDefCub
theorem cubical_structure_pullback_const_point : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    _root_.GlobalTheory.TangentConstLB.lbIso_tangent_const E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)
end GlobalTheory.ConstDefCub
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_structure_const_section_pullback : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  first | exact @_root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point | exact _root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point | (intros; apply _root_.GlobalTheory.ConstDefCub.cubical_structure_pullback_const_point <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeformationRetractsOfKodairaSpencerZero
section
section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
variable {C : Over (Sp (DualNumber R))} [GrpObj C] {φ : C.left ⟶ A.left} {j : A.left ⟶ C.left}
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
theorem exists_retraction_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
      ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left)
        (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i),
        IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
        (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) →
        ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  intro Pr GD E _ _ _ H Dw l Xo c K _ _ y x' _ _ A _ A' _ π π' i h _ hπ' _ hKS
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  exact GlobalTheory.DeRham.exists_retraction_of_isKSValue_one Pr.p5 GD h hA' gA' hKS
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) → ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  first | exact @_root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | exact _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | (intros; apply _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DivisorMultipleNonnegEventually
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.LargeAll
set_option maxHeartbeats 800000 in
theorem exists_smul_nonneg_of_large : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  intro _ D T j Y e o hY _ a n hdom hn f hf
  obtain ⟨s, hs, h⟩ := GlobalTheory.LargeCover.exists_smul_nonneg_all D T j Y e o hY a n hdom hn f hf
  have hsm : (algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s) • f = s • f :=
    @algebraMap_smul (𝓞 Y.d.c₂.F) _ Y.d.c₂.F _ _ (Rul Y.d.Xo₂ Y.d.c₂) _ _ _ (Formalism.L2.Pj.rulesTower _) s f
  refine ⟨algebraMap (𝓞 Y.d.c₂.F) Y.d.c₂.F s, by simpa using hs, fun la v hv => ?_⟩
  rw [hsm]
  exact h la v hv
end GlobalTheory.LargeAll
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_multiple_nonneg_eventually : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n → ∀ f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n, ∃ s : Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  first | exact @_root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large | exact _root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large | (intros; apply _root_.GlobalTheory.LargeAll.exists_smul_nonneg_of_large <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsUnramifiedCurveOverField
section
section
set_option autoImplicit false
namespace GlobalTheory.RefSum.UnramCurveField
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField
end
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
theorem exists_unramified_curve_over_field : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n :=
  fun h E _ _ _ H n q hn hq hnd => exists_field_of_rayField h.p8 E H n q hn hq
    (fun e => hnd ((e.mul_left 2).mul_right _)) (fun e => hnd (e.mul_left _))
end GlobalTheory.RefSum.UnramCurveField
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_curve_field_existence : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n := by
  first | exact @_root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field | exact _root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field | (intros; apply _root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeneratedWeightsMulStableAndBounded
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem generated_weights_mul_stable_and_bounded : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → (h.data f₁ f₂ th k).MulStable ∧ (h.data f₁ f₂ th k).MulBound fun _ => k.beta := by
  intro hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have tr : ∀ (a b : AllWt.Weight (T.Q.Dw j)) (_ : a = b) (g : Cusp Z Y.U a), ∃ g' : Cusp Z Y.U b, g'.1 = g.1 ∧
      (g ∈ latOn Y.U Z (wtOf _ a 0) → g' ∈ latOn Y.U Z (wtOf _ b 0)) := by
    rintro a b rfl g
    exact ⟨g, rfl, id⟩
  have key : ∀ (i : ℕ) (hi : i < P.T) (w' : Cusp Z Y.U P.u₁) (f' : Cusp Z Y.U (P.wt i)),
      ∃ g' : Cusp Z Y.U (P.wt (i + 1)), g'.1 = w'.1 * f'.1 ∧
        (w' ∈ latOn Y.U Z (wtOf _ P.u₁ 0) → f' ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) →
          g' ∈ latOn Y.U Z (wtOf _ (P.wt (i + 1)) 0)) ∧
        ((h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' : (h.data f₁ f₂ th k).V (i + 1)) :
            (h.data f₁ f₂ th k).Sec (i + 1)) =
          (h.data f₁ f₂ th k).mulW i (f₁.b.equivFun w') (h.equivV f₁ f₂ th k hi.le f') := by
    intro i hi w' f'
    have hx := _root_.GlobalTheory.T.cuspidal_sections_mul_mem D T j Y e o hG hE Z P.u₁ (P.wt i) w' f' hPr
    obtain ⟨g, hg, hgl⟩ := hx
    have hy := tr _ _ (P.u₁_add_wt i) g
    obtain ⟨g', hg', hgl'⟩ := hy
    refine ⟨g', hg'.trans hg, fun a b => hgl' (hgl a b), ?_⟩
    exact (h.coe_equivV f₁ f₂ th k _ g').trans ((h.mulW_adjSec f₁ f₂ th k i w' f' g' (hg'.trans hg)).symm.trans
      (congrArg _ (h.coe_equivV f₁ f₂ th k hi.le f').symm))
  refine ⟨?_, ?_⟩
  · intro i hi w hw f hf
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', -, hl, he⟩ := hk
    have hw' : f₁.b.equivFun.symm w ∈ latOn Y.U Z (wtOf _ P.u₁ 0) :=
      (h.mem_lattice f₁ f₂ th k _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).lattice) (f₁.b.equivFun.apply_symm_apply w)) hw)
    have hf' : (h.equivV f₁ f₂ th k hi.le).symm f ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) :=
      (h.equivV_mem f₁ f₂ th k hi.le _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).M i) (LinearEquiv.apply_symm_apply _ f)) hf)
    refine ⟨h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g', (h.equivV_mem f₁ f₂ th k _ g').2 (hl hw' hf'), ?_⟩
    exact he.trans (congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f)))
  · intro i hi σ w hw f hf g hg
    have pe : ∀ (a b : AllWt.Weight (T.Q.Dw j)), a = b → ∀ σ x,
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ x =
          petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ x := by
      rintro a b rfl σ x
      rfl
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', hgp, -, he⟩ := hk
    have hgg : g = h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' :=
      Subtype.ext (hg.trans ((congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
        (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f))).symm.trans he.symm))
    have hb := _root_.GlobalTheory.HSApp.petOn_mul_le D T j Y e o hG hE Z P.u₁ (P.wt i) (f₁.b.equivFun.symm w)
      ((h.equivV f₁ f₂ th k hi.le).symm f) k.beta (zero_le_one.trans k.one_le_beta) hB σ
    have e0 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ g'.1 =
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.u₁ + P.wt i) 0) σ
          ((f₁.b.equivFun.symm w).1 * ((h.equivV f₁ f₂ th k hi.le).symm f).1) :=
      (congrArg (petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ) hgp).trans
        (pe _ _ (P.u₁_add_wt i).symm σ _)
    have e1 := h.nrm_equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) σ g'
    have e2 := h.normAt_eq f₁ f₂ th k σ (f₁.b.equivFun.symm w)
    have e3 := h.nrm_equivV f₁ f₂ th k hi.le σ ((h.equivV f₁ f₂ th k hi.le).symm f)
    have e2' := (congrArg ((h.data f₁ f₂ th k).normAt σ) (f₁.b.equivFun.apply_symm_apply w).symm).trans e2
    have e3' := (congrArg (((h.data f₁ f₂ th k).nm i).nrm σ) (LinearEquiv.apply_symm_apply _ f).symm).trans e3
    calc _ = _ := congrArg (((h.data f₁ f₂ th k).nm (i + 1)).nrm σ) hgg
      _ = _ := e1
      _ = _ := e0
      _ ≤ _ := hb
      _ = _ := congrArg₂ (fun a b => Real.sqrt k.beta * a * b) e2'.symm e3'.symm
end GlobalTheory.HSApp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.CovTop
theorem haarMeasure_fundamentalDomain_ne_zero_of_cocompact : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ 0 := by
  intro _ D Tu C t0 _ i P μ 𝓕 hF h0
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D i).gram
  haveI : μ.IsHaarMeasure := hF.1.1
  have h1 : μ Set.univ = 0 := by
    rw [hF.2.measure_eq_tsum Set.univ]
    refine ENNReal.tsum_eq_zero.2 fun g => ?_
    rw [Set.smul_set_univ, Set.univ_inter, h0]
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h1
end GlobalTheory.CovTop
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact | exact _root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact | (intros; apply _root_.GlobalTheory.CovTop.haarMeasure_fundamentalDomain_ne_zero_of_cocompact <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KoecherPrincipleUnitConstant
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatLine
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
end GlobalTheory.FlatLine
namespace GlobalTheory.CovTop
theorem koecher_principle_unit_constant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (g h : Rul Y.d.Xo₂ Y.d.c₂), g ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → h ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → GlobalTheory.FlatLine.idem Z * g = g → GlobalTheory.FlatLine.idem Z * h = h → g * h = GlobalTheory.FlatLine.idem Z → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 g z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 h z ≤ C) → ∃ a : Y.d.c₂.F, g = a • GlobalTheory.FlatLine.idem Z := by
  intro _ D T j Y e o hY _ Z g h hg _ hgi _ _ hB
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨C, hC⟩ := hB _ hσ
  have hs : g ∈ GlobalTheory.AllWt.suppOn Z := by
    rw [← hgi, mul_comm]
    exact GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)
  exact GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by
    have h1 := (hC z hz).1
    rwa [GlobalTheory.FlatLine.homN_zero] at h1
end GlobalTheory.CovTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PeriodMinimumPhiPos
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PeriodMinPos
theorem period_minimum_phi_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  intro _ E _ _ _ H Dw l Xo c T io y φ hφ G t' m1 m2 hG
  obtain ⟨G₀, t₀, m1₀, m2₀, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩ := hφ
  obtain ⟨m⟩ := GlobalTheory.SlopeRec.nonempty_sabMap_of_models m1 m2 m1₀ m2₀
  have hG₀ : (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G₀.G := fun h =>
    hG ((abLocus_pullback abLocusOne G.semi m.cart.1 _).2 h)
  have hnt : ¬ Subsingleton P.D.toPre.X := fun h =>
    hG₀ ((GlobalTheory.TorRef.closed_mem_abLocus_iff T P).2 h)
  rw [not_subsingleton_iff_nontrivial] at hnt
  obtain ⟨a, ha⟩ := exists_ne (0 : P.D.toPre.X)
  have hQa : 1 ≤ Q a := ReciprocityTheory.ChartRestriction.G.DVR.QForm.Q_pos hϖ P.D hQ ha
  have hint : ∀ a c, ∃ z : ℤ, (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a c = z := by
    intro a c
    refine ⟨Q (a + c) - Q a - Q c, ?_⟩
    have h1 := hβ (a + c)
    have hs := β.2.1 c a
    simp only [map_add (f := _), LinearMap.add_apply] at h1
    rw [hβ a, hβ c] at h1
    push_cast
    linarith
  have hpos : ∀ a, 0 ≤ (β : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ) a a := fun a => by
    rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)
  have hne : β ≠ 0 := fun e => by
    have h1 := hβ a
    rw [e] at h1
    have : (1 : ℝ) ≤ Q a := by exact_mod_cast hQa
    simp at h1
    linarith
  haveI : Module.Finite (𝓞 E) P.D.toPre.X := .of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have h1 := GlobalTheory.LeastExponentProbe.one_le_phiC (fun _ => rfl) β hint hpos hne
  linarith
end GlobalTheory.PeriodMinPos
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_period_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  first | exact @_root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | exact _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos | (intros; apply _root_.GlobalTheory.PeriodMinPos.period_minimum_phi_pos <;> assumption)
end
end

