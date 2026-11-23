module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevCore

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem dict_transport {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {X : Comp → Data E r} {V W : HSp D} (h : V = W) (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (d : GA D W → Σ k, Frame (X k).Ψ r) (hdd : ∀ g (h' : V = W), d g = dict (h' ▸ g))
    (Kf : Subgroup (GA D V)) (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (N : ℕ) (hl : IsLevelK V N Kf) (hd : DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) :
    ∃ (Kf' : Subgroup (GA D W)) (hr' : W.rank = r), IsLevelK W N Kf' ∧ DictIsUnif W d Kf' th hr' ∧
      ∀ g τ i, ‖dmin (X (d g).1).Gm (d g).2 τ i‖ = 1 := by
  subst h
  obtain rfl : d = dict := funext fun g => hdd g rfl
  exact ⟨Kf, hr, hl, hd, hu⟩

end GlobalTheory.LevCore


open GlobalTheory.LevCore in
theorem GlobalTheory.LevGeo.laws_of_coreJ : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  intro D T j hT hj
  obtain ⟨hH, hL, _, hDat⟩ := hT.pins
  refine ⟨⟨hj, hH, hDat j hj, hL.2, hT.unf j hj, hT.chiTriv j hj, ?_, ?_⟩, ?_⟩
  · intro σ hσ
    obtain ⟨th, hr, hinf, hdu⟩ := hT.dictU j hj σ hσ
    obtain ⟨Kf', hr', h1, h2, h3⟩ := dict_transport (hT.spaceW j hj σ hσ) (T.dict j σ) (coreDict T.toCore j σ)
      (fun g h' => by unfold coreDict; rw [dite_eq_left h']) (T.Kf j σ) th hr _
      (hL.1 ▸ hT.levelK j hj σ hσ) hdu (hT.muUnit j hj σ hσ).2.2.2
    exact ⟨Kf', th, hr', h1, hinf, h2, h3⟩
  · intro σ hσ
    have h := hT.modelW j hj σ hσ
    rw [hT.spaceW j hj σ hσ] at h
    exact h
  · intro G σ f
    have hg := Formalism.L2.Pj.goodEmb_goodOf (c := T.Q.c) σ
    have key : ∀ (W : HSp D) (h : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W)
        (d : GA D W → Σ k, Frame ((T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)).X k).Ψ D.R.r),
        (∀ g (h' : T.V j (Formalism.L2.Pj.goodOf T.Q.c σ) = W), d g = T.dict j _ (h' ▸ g)) →
        petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) W d (muQ1 W) G f =
          petAt (T.U j (Formalism.L2.Pj.goodOf T.Q.c σ)) (xiR D) (T.V j _) (T.dict j _) (muQ1 _) G f := by
      intro W h
      subst h
      intro d hdd
      obtain rfl : d = _ := funext fun g => hdd g rfl
      rfl
    exact key _ (hT.spaceW j hj _ hg) _ (fun g h' => by unfold coreDict; rw [dite_eq_left h'])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def SameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Y.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
    IsTanAtG Y.oF.t (ptF y) w ∧ w ≫ Y.m0.toSABMap.φ = u ∧ w ≫ Y.m.φ = v

def Matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S)) : Prop :=
  a.x = ptF y ≫ Y.jQ ∧
    (∀ i : Fin Dw.p, ∃ j : Fin (Dw.mult τ.1), (j : ℕ) = i ∧ SameVec Y y (y.u τ.1 j) (a.v i).left) ∧
    ∀ i : Fin Dw.q, ∃ j : Fin (Dw.mult (conjEmb τ.1)), (j : ℕ) = i ∧ SameVec Y y (y.u (conjEmb τ.1) j) (a.w i).left

def Reads (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H)
    (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), GlobalTheory.FlatLine.Tested y →
    ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a →
      evR Xo c f y = sig S (algebraMap c.F S) a

end GlobalTheory.BdryUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionLeviGLIsotropicFrame
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem reduce_gl_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) (j : ℕ) : ∃ (L : Set (GL (Fin j) (AF F ⊗[F] E))) (B : ℝ), IsCompact L ∧
    ∀ α : GL (Fin j) (AF F ⊗[F] E), ∃ (δ : GL (Fin j) E) (l : Fin j → ℤ), ∃ c ∈ L,
      bc (inclR (F := F) (AF F)) δ * α = tor F E l * c ∧
      (absE F E (Matrix.GeneralLinearGroup.det α) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ :=
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  GlobalTheory.GodementSectionReduction.reduction_GL_diagonalUnitPowers_compact (inclR (F := F) (AF F)) GlobalTheory.Doubling.continuous_absE
    (fun u => GlobalTheory.Doubling.absE_inclR u) (by positivity)
    (by rw [GlobalTheory.T.tensorIdeleNormalizedAbs_ideleHalfAtInfinity _ _ _ hc]; simp) (GlobalTheory.Eis.Conv.red_gl _ _ _ hc j)

theorem reduce_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (W : Set (GAd σ J)) (B : ℝ), IsCompact W ∧ ∀ (p : GAd σ J) (β : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * β.1 → ∃ γ ∈ ratPts σ J, γ ∈ parFlag σ J C (fun _ => 0) ∧ ∃ q ∈ fixG σ J C, ∃ l : Fin j → ℤ, ∃ w ∈ W, γ * p = q * lv (tor F E l) * w ∧ (absE F E (Matrix.GeneralLinearGroup.det β) : ℝ) ≤ B * ∏ i, (bse F ^ l i)⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF lv hl
  obtain ⟨L, B, hL, hR⟩ := reduce_gl_cm hF.cm j
  refine ⟨lv '' L, B, hL.image hl.cont, fun p β hp => ?_⟩
  obtain ⟨δ, l, c, hc, hred, hle⟩ := hR β
  have h1 := hl.rat δ
  generalize bc (inclR (F := F) (AF F)) δ = u at h1 hred
  refine ⟨lv u, h1, ⟨⟨u.1, fun _ _ h => absurd h (lt_irrefl _), hl.onC u⟩,
    (u⁻¹).1, fun _ _ h => absurd h (lt_irrefl _), by rw [← map_inv]; exact hl.onC u⁻¹⟩,
    lv u * p * lv (u * β)⁻¹, ?_, l, lv c, ⟨c, hc, rfl⟩, ?_, hle⟩
  · change _ * _ = _
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hl.onC, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ (adMat F C), hp, ← Matrix.mul_assoc, hl.onC, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc u.1, ← Units.val_mul, Units.mul_inv, Matrix.mul_one]
  · rw [mul_assoc _ (lv _) (lv c), ← map_mul, ← hred, map_inv, inv_mul_cancel_right]

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
section
noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def resRd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) :
    Rul Xo c →+* (↥(U.X k).dom → ℂ) where
  toFun f := fun y => rdU U f k y.1
  map_one' := by
    funext y
    haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, y.2, dif_pos, Pi.one_apply]
    exact congrArg toC (evalAt_one _ _ (U.un k ⟨y.1, y.2⟩) (hT _ _))
  map_mul' f g := by
    funext y
    exact congrFun (congrFun (AllWt.rdU_mul U f g) k) y.1
  map_zero' := by
    funext y
    simp
  map_add' f g := by
    funext y
    simp

theorem resRd_apply {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (f : Rul Xo c)
    (y : ↥(U.X k).dom) : resRd U hT k f y = rdU U f k y.1 := rfl

theorem resRd_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hT : AllTest Xo c) (k : U.Comp) (a : c.F) (f : Rul Xo c) :
    resRd U hT k (a • f) = σ a • resRd U hT k f := by
  funext y
  simp [resRd_apply, map_smulₛₗ]

def holAlg (X : Data E r) : Subalgebra ℂ (↥X.dom → ℂ) where
  carrier := {g | ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ ∀ y, g y = F y.1}
  mul_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F * F', hF.mul hF', fun y => by simp [hg, hg']⟩
  add_mem' := by
    rintro g g' ⟨F, hF, hg⟩ ⟨F', hF', hg'⟩
    exact ⟨F + F', hF.add hF', fun y => by simp [hg, hg']⟩
  algebraMap_mem' a := ⟨fun _ => a, differentiableOn_const a, fun y => rfl⟩

end GlobalTheory.FlatPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LFun

open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
private theorem isUnit_of_isUnit_norm' {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (z : S) (h : IsUnit (Algebra.norm R z)) : IsUnit z := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
  obtain ⟨u, hu⟩ := h
  refine IsUnit.of_mul_eq_one (u.inv 1) ?_
  have := congrArg (fun f : Module.End R S => f 1) u.val_inv
  simp only [hu] at this
  simpa using this


open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
theorem _root_.GlobalTheory.LFun.resEtaPow_of_resEta : ∀ (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (χ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)ˣ →* Circle) (n : ℕ), _root_.GlobalTheory.LFun.ResEta F E χ n →
      _root_.GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toMonoidHom).range χ n := by
  intro F E _ _ _ _ _ h2 χ n hχ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨⟨η, hη⟩, hall⟩ := hχ
  have hηe := hη.eq_normSign
  intro a
  rw [show χ ((Units.map ↑(algebraMap (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))) a) = η a ^ n from
    hall η hη a]
  split_ifs with ha
  · obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ha
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    rw [map_mul, hη.2.1 t, hη.2.2.1 w]
    simp
  · have hs : _root_.GlobalTheory.IdeleNormChar.normSign E a ≠ 1 := by
      intro h1
      obtain ⟨t, ht⟩ := (_root_.GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 h1
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff.1 ht
      have hzu : IsUnit z :=
        isUnit_of_isUnit_norm' z (hz ▸ Units.isUnit _)
      apply ha
      have hn : Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit =
          a / _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t := by
        ext
        simpa using hz
      have key : a = _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t *
          Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit := by
        rw [hn, mul_div_cancel]
      rw [key]
      exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    have hm : _root_.GlobalTheory.IdeleNormChar.normSign E a = -1 := (Int.units_eq_one_or _).resolve_left hs
    rw [hηe]
    simp [hm, _root_.GlobalTheory.IdeleNormChar.signToCircle]

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarEqOfWeilPairingEqPrincipalCMTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.TwistScalarUnique

def coordMul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (s : E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z k := ty k s * z k
  map_add' z w := by funext k; simp [mul_add]
  map_smul' c z := by funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem cmHost_sqrtNegDisc_re_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0.re = 0 := by
  have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im] at h2 h3
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  by_contra hne
  have him : H.rt0.im = 0 := by
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [him] at h2
  nlinarith [mul_self_nonneg H.rt0.re]

theorem exists_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    (∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0) ∧ ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩
  have hre := cmHost_sqrtNegDisc_re_eq_zero H
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by apply Complex.ext <;> simp [hre]
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]; simpa using this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · refine ⟨⟨τ, h⟩, (starRingEnd ℂ).comp τ, ?_⟩
    show starRingEnd ℂ (τ (H.rt : E)) ≠ H.rt0
    rw [h, hconj]; exact fun e => hne e.symm
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩, τ, ?_⟩
    · show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
      rw [h, map_neg, hconj, neg_neg]
    · rw [h]; exact fun e => hne e.symm

theorem nonempty_of_isTypeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {p q g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) (hpq : p + q = 1) : Nonempty (Fin g) := by
  obtain ⟨⟨τ₁, h₁⟩, τ₂, h₂⟩ := exists_embedding H
  rcases Nat.add_eq_one_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h := (hty τ₂).2 h₂
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₂} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩
  · have h := (hty τ₁).1 h₁
    obtain ⟨⟨i, -⟩⟩ : Nonempty {i // ty i = τ₁} := (Nat.card_pos_iff.1 (by rw [h]; norm_num)).1
    exact ⟨i⟩

theorem eq_of_weilEq_complex {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (A : PAT H (Sp ℂ))
    {p q : ℕ} (hpq : p + q = 1)
    (hdet : ∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ p) ∧
      (τ H.rt ≠ H.rt0 → LieMult A.t.act (𝟙 (Sp ℂ)) τ q)) (s s' : 𝓞 E)
    (h : WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ))) : s = s' := by
  have hT : ThetaUnifAV := thetaUnifAV_all
  have hL : Out.Laws := abelianSchemeLaws_all.1
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨u, HA, χA, -, hA, -⟩ := PureType.exists_isThetaUnif hT A.pol
  obtain ⟨D, Pe, F, -, -, -, -, -, hact⟩ := PureTriple.exists_datum_period hT hL A hty hdet u hA
  let G : 𝓞 E → (Fin A.pol.g → ℂ) →ₗ[ℂ] (Fin A.pol.g → ℂ) := fun s =>
    F.toLinearMap ∘ₗ coordMul ty (s : E) ∘ₗ F.symm.toLinearMap
  have hG : ∀ s z, u.ex (G s z) = u.ex z ≫ A.t.act.act s := fun s z => by
    have e := hact s (F.symm z)
    rw [F.apply_symm_apply] at e
    exact e
  have key := (weilEq_iff_hermForm_eq hT hL A.pol A.pol A.pol A.pol u u u u HA HA χA χA hA hA
    (A.t.act.act s) (𝟙 _) (A.t.act.act s') (𝟙 _) (G s) LinearMap.id (G s') LinearMap.id (hG s)
    (fun _ => (Category.comp_id _).symm) (hG s') (fun _ => (Category.comp_id _).symm)).1 h
  have hGeq : ∀ z, G s z = G s' z := by
    intro z
    by_contra hne
    have hpos := hA.2.1 (G s z - G s' z) (sub_ne_zero.2 hne)
    have e := key z (G s z - G s' z)
    simp only [hermForm, LinearMap.id_apply] at e
    rw [sub_dotProduct, e, sub_self] at hpos
    simp at hpos
  obtain ⟨k⟩ := nonempty_of_isTypeFn H hty hpq
  have e1 := hGeq (F fun _ => 1)
  simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at e1
  have e2 := congrFun (F.injective e1) k
  have e3 : ty k (s : E) = ty k (s' : E) := by simpa [coordMul] using e2
  exact RingOfIntegers.ext ((ty k).injective e3)

theorem eq_of_weilEq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (A : PAT H (Sp (𝓞 K))), ρ ^ 2 = -(H.d : 𝓞 K) →
    HasType H A.t.act ρ 1 0 → ∀ s s' : 𝓞 E,
    WeilEq A.t.PP.L (A.t.act.act s) (𝟙 _) A.t.PP.L (A.t.act.act s') (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    s = s' := by
  intro E _ _ _ H K _ _ ρ σ₁ A hρ hA s s' h
  have hβi : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)
  obtain ⟨⟨A', mA, -⟩, hA2⟩ := GlobalTheory.LamT.pat_pullback E H (𝓞 K) ℂ (σ₁.comp (algebraMap (𝓞 K) K)) A
  obtain ⟨-, -, wA, hwA⟩ := hA2 A' mA inferInstance
  have hlie : ∀ (τ : 𝓞 E →+* ℂ) (n : ℕ), LieMult A'.t.act (𝟙 (Sp ℂ)) τ n ↔
      LieMult A.t.act (spMap (σ₁.comp (algebraMap (𝓞 K) K))) τ n := fun τ n => by
    have := GlobalTheory.lieMult_iff_of_isGrpPullback mA.cart A'.t.act A.t.act mA.act (𝟙 (Sp ℂ)) τ n
    rwa [Category.id_comp] at this
  have hweil : WeilEq A'.t.PP.L (A'.t.act.act s) (𝟙 _) A'.t.PP.L (A'.t.act.act s') (𝟙 _) (𝟙 (Sp ℂ)) := by
    refine (GlobalTheory.PairingFibre.weilEq_iff (f₂ := 𝟙 _) (g₂ := 𝟙 _) (f₂' := 𝟙 _) (g₂' := 𝟙 _) mA.cart mA.cart
      mA.cart mA.cart A.t.PP.isLB A.t.PP.isLB A'.t.PP.isLB A'.t.PP.isLB ⟨wA, hwA.1⟩ ⟨wA, hwA.1⟩ (mA.act s)
      (by simp) (mA.act s') (by simp) (𝟙 (Sp ℂ))).2 ?_
    rwa [Category.id_comp]
  have hT := hA ℂ (σ₁.comp (algebraMap (𝓞 K) K)) hβi
  have hd0 : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h0 => hd0 (by have := H.sqrt_neg_disc_sq; rw [h0] at this; linear_combination this)
  have hsq : ∀ x : ℂ, x ^ 2 = -(H.d : ℂ) → x = H.rt0 ∨ x = -H.rt0 := fun x hx =>
    sq_eq_sq_iff_eq_or_eq_neg.1 (hx.trans H.sqrt_neg_disc_sq.symm)
  have hβρ : (σ₁.comp (algebraMap (𝓞 K) K)) ρ ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hρ]; simp
  have hτ : ∀ τ : 𝓞 E →+* ℂ, τ H.rt ^ 2 = -(H.d : ℂ) := fun τ => by
    rw [← map_pow, H.rt_sq]; simp
  have hne : H.rt0 ≠ -H.rt0 := fun h => hr0 (by linear_combination h / 2)
  rcases hsq _ hβρ with hc | hc
  · refine eq_of_weilEq_complex H A' (p := 1) (q := 0) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 1).2 ((hT τ).1 (ht.trans hc.symm))
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => ht (h.trans hc)))
  · refine eq_of_weilEq_complex H A' (p := 0) (q := 1) rfl (fun τ => ⟨fun ht => ?_, fun ht => ?_⟩) s s' hweil
    · exact (hlie τ 0).2 ((hT τ).2 (fun h => hne (ht.symm.trans (h.trans hc))))
    · rcases hsq _ (hτ τ) with h | h
      · exact absurd h ht
      · exact (hlie τ 1).2 ((hT τ).1 (h.trans hc.symm))

end GlobalTheory.TwistScalarUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMem
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq

theorem wd_rat_mem_TT : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}, Crv D cc δ → ∀ {N N' : ℕ} {x : VC D N N'} {M : ℕ}, 0 < M → M • x ∈ La0 D (tor0 D cc δ) N N' → ∀ {F : VC D N N' → ℂ}, F ∈ TT D (tor0 D cc δ) N N' → Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) N N' := by
  intro D cc δ hc N N' x M hM hx F hF
  obtain ⟨hd, m, hm, hFm⟩ := hF
  have hg := (GlobalTheory.InducedType.induced_type D).1
  have hint := (_root_.GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (GlobalTheory.NormSum.VacMove.klat _ (GlobalTheory.NormSum.VacMove.moves_one D N) (GlobalTheory.NormSum.VacMove.moves_one D N'))).2.2.1
  refine ⟨GlobalTheory.FinWeil.RatTransl.differentiable_wd x hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have h0 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hFm _ (AddSubgroup.nsmul_mem _ hy M)
  obtain ⟨k, hk⟩ := hint _ (AddSubgroup.nsmul_mem _ hy m) _ hx
  have e : (m * M) • y = M • (m • y) := by rw [mul_comm, mul_smul]
  funext w
  exact GlobalTheory.FinWeil.RatTransl.wd_wd_of_int h0 k (by rw [e, GlobalTheory.FinWeil.RatTransl.hf_nsmul, hk]) w

end GlobalTheory.FunObj.NormUniq
end
end

