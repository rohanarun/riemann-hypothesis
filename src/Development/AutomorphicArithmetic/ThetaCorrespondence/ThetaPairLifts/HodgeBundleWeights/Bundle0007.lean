module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2120
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioIdentity
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.CovolumeRatioIdentity : Prop :=  ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.EquivariantActionEqOfAgreeOnGenerators
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvAct
theorem equivariant_action_ext : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA1 Γ _ ι ρ hact X' _ φ ℓ ρ' hN hproj hℓ hℓφ hρ
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨n, hn, hη⟩ := _root_.GlobalTheory.T.interior_equivariant_action_invariant hP E H Dw l Xo c TF Z hpq hA Γ ι ρ (_root_.GlobalTheory.LevelMoveRestr.restr_eq E H Dw l Xo c TF Z hpq hA Γ ι ρ hact)
  haveI := hℓ
  haveI : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProjOver hproj
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := (isNormalScheme_iff_pred X').mp hN
  have hne : Nonempty (V₀ TF.Y Z) :=
    ⟨⟨genPt Z, (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)⟩⟩
  haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian (pullG TF Z φ) :=
    IsSemiAbelian.pullback _ _ TF.Y.t.semi
  have hcomp : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
    rw [← Category.assoc, hℓφ]
  have hκ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (φ ≫ (barComp TF.Y Z).ι) ℓ
    ((isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr hcomp rfl)
  obtain ⟨κ, hκ, hκψ⟩ : ∃ κ : (pullG TF Z (j₀ TF.Y Z)).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z (j₀ TF.Y Z)) (pullG TF Z φ) ℓ κ ∧ κ ≫ pullψ TF Z φ = pullψ TF Z (j₀ TF.Y Z) :=
    ⟨_, hκ, pullback.lift_fst _ _ _⟩
  have hκw : κ ≫ (pullG TF Z φ).hom = (pullG TF Z (j₀ TF.Y Z)).hom ≫ ℓ := hκ.1.w
  have hM : ∀ γ, ∃ M : (pullG TF Z φ).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z φ) (pullG TF Z φ) (ρ' γ).asIso.hom M ∧ κ ≫ M = n γ ≫ κ := fun γ =>
    exists_isGrpPullback_extend hP.p22 X' (V₀ TF.Y Z) hS ℓ (ρ γ).asIso.hom (ρ' γ).asIso.hom (hρ γ) (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
      (n γ) (hn.1 γ)
  choose m hm hmκ using hM
  have huniq := eq_of_comp_eq_of_isGrpPullback hS ℓ (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
  have hact' : ∀ a : 𝓞 E, κ ≫ ((pullAct TF Z φ).act a).left = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
    intro a
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ) = _ ≫ (κ ≫ pullψ TF Z φ)
      rw [pullAct_pullψ, ← Category.assoc, hκψ, pullAct_pullψ]
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ (pullG TF Z φ).hom) = _ ≫ (κ ≫ (pullG TF Z φ).hom)
      rw [Over.w, hκw, ← Category.assoc, Over.w]
  refine ⟨m, ⟨hm, fun γ a => ?_, fun γ₁ γ₂ => ?_⟩, ?_⟩
  · refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, (hm γ).1.w, ← Category.assoc, Over.w]
    · calc κ ≫ ((pullAct TF Z φ).act a).left ≫ m γ
          = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ ≫ m γ := by rw [← Category.assoc, hact', Category.assoc]
        _ = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ n γ ≫ κ := by rw [hmκ]
        _ = n γ ≫ ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
          rw [← Category.assoc, hn.2.1 γ a, Category.assoc]
        _ = n γ ≫ κ ≫ ((pullAct TF Z φ).act a).left := by rw [hact']
        _ = κ ≫ m γ ≫ ((pullAct TF Z φ).act a).left := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · refine huniq _ _ ?_ ?_
    · rw [(hm _).1.w, Category.assoc, (hm γ₁).1.w, ← Category.assoc, (hm γ₂).1.w, Category.assoc, map_mul,
        Aut.mul_asIso]
      rfl
    · calc κ ≫ m (γ₁ * γ₂) = n (γ₁ * γ₂) ≫ κ := hmκ _
        _ = n γ₂ ≫ n γ₁ ≫ κ := by rw [hn.2.2, Category.assoc]
        _ = n γ₂ ≫ κ ≫ m γ₁ := by rw [hmκ]
        _ = κ ≫ m γ₂ ≫ m γ₁ := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · intro γ a b hab w w' hw hw' hwb hwa
    have lift : ∀ v : V₀ TF.Y Z ⟶ (pullG TF Z φ).left, v ≫ (pullG TF Z φ).hom = ℓ →
        ∃ u : V₀ TF.Y Z ⟶ (pullG TF Z (j₀ TF.Y Z)).left, u ≫ (pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _ ∧
          u ≫ pullψ TF Z (j₀ TF.Y Z) = v ≫ pullψ TF Z φ ∧ u ≫ κ = v := by
      intro v hv
      have e : (v ≫ pullψ TF Z φ) ≫ TF.Y.t.G.hom = 𝟙 _ ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (v ≫ (pullG TF Z φ).hom) ≫ _ = _
        rw [hv, Category.id_comp, hcomp]
      refine ⟨pullback.lift _ _ e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ (κ ≫ pullψ TF Z φ) = v ≫ pullψ TF Z φ
        rw [hκψ]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc]
        change _ ≫ (κ ≫ (pullG TF Z φ).hom) = v ≫ (pullG TF Z φ).hom
        rw [hκw, ← Category.assoc]
        change (pullback.lift _ _ e ≫ pullback.snd _ _) ≫ ℓ = _
        rw [pullback.lift_snd, Category.id_comp, hv]
    obtain ⟨u, hu1, hu2, hu3⟩ := lift w hw
    obtain ⟨u', hu1', hu2', hu3'⟩ := lift w' hw'
    have := hη γ a b hab u u' hu1 hu1' (by rw [hu2, hwb]) (by rw [hu2', hwa])
    rw [← hu3, ← hu3', Category.assoc, hmκ, ← Category.assoc, this, Category.assoc]
end GlobalTheory.EqvAct
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariant_action_eq_of_agree_on_generators : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).asIso.hom ≫ ℓ = ℓ ≫ (ρ' γ).asIso.hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  first | exact @_root_.GlobalTheory.EqvAct.equivariant_action_ext | exact _root_.GlobalTheory.EqvAct.equivariant_action_ext | (intros; apply _root_.GlobalTheory.EqvAct.equivariant_action_ext <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerMapCompatibilities
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSPkg
open GlobalTheory.DeRham GlobalTheory.Cris
theorem kodaira_spencer_map_properties : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  intro PP E _ _ _ H Dw l Xo c TF U δ K _ _ P hU y' hU' hs hev
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ y' = frX P := by
    apply GlobalTheory.FlagMod.xF_ext (Y := TF.Y)
    · rw [Category.assoc, hs, spMap_comp_spMap]
      congr 1
    · exact GlobalTheory.FlagMod.frX_snd P
    · have h1 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ (y' ≫ TF.Y.j)) ⁻¹ᵁ U.1 :=
        GlobalTheory.FlagMod.le_preimage_comp _ hU'
      rw [Category.assoc, ← GlobalTheory.FlagMod.spMap_ev _ U.2 h1, ← GlobalTheory.FlagMod.spMap_ev _ U.2 hU,
        GlobalTheory.FlagMod.ev_spMap _ _ _ hU' h1]
      refine congrArg (fun f => spMap f ≫ (U.2 : IsAffineOpen U.1).fromSpec) ?_
      ext r
      rw [RingHom.comp_apply, hev r]
      simp [GlobalTheory.FlagTan.red]
  have hx : GlobalTheory.FlagTan.IsTanX P (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp_spMap]
      rfl
    · rw [← Category.assoc, hred, GlobalTheory.FlagMod.frX_fst]
  have P5 := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G (y' ≫ pullback.fst _ _)
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G P.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hUn := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := _root_.GlobalTheory.PolExists.polForm_exists P5 Xo hπ
  have hadj := _root_.GlobalTheory.PolAdjoint.polForm_adjoint P5 Xo hπ a ha hpol
  have hK := _root_.GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P5 hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback P hπ a ha
  have hL := (P5.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := _root_.GlobalTheory.LieBasis.lifts_basis_mod_fil P5 P hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))),
      ∃ w, GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ => by
    obtain ⟨_, w, -, hw⟩ := _root_.GlobalTheory.KSExist.ksRow_exists_lieComb hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => _root_.GlobalTheory.KSExist.isKSValue_act hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, GlobalTheory.KSExist.conj_embK]) a₀
    exact ⟨w, hw⟩
  exact ⟨A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub, hb, _, hπ, hπ', rfl, hpol, hu,
    fun σ k => hbl ⟨σ, k⟩, hrow, hA, gA, hA', gA', LB.isLB_pull Xo.univ.t.PP.isLB _⟩
end GlobalTheory.KSPkg
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_map_compatibilities : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  first | exact @_root_.GlobalTheory.KSPkg.kodaira_spencer_map_properties | exact _root_.GlobalTheory.KSPkg.kodaira_spencer_map_properties | (intros; apply _root_.GlobalTheory.KSPkg.kodaira_spencer_map_properties <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerUniversalFamily
section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan.KSUniv
open GlobalTheory.FlagTan in
theorem kodaira_spencer_universal : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y hpq
  classical
  obtain ⟨X₀, h1, h2, hinj⟩ :=
    _root_.GlobalTheory.TanBasis.exists_point_tanBasis E H Dw l Xo c K y (HIx Dw (psiSet H)) (card_HIx (isHalf_psiSet H))
  choose N hN using fun k : HIx Dw (psiSet H) =>
    _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent hP E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 (Pi.single k 1))
  have hL := _root_.GlobalTheory.T.kodaira_spencer_of_direct_sum_deformation hP E H Dw l Xo c K y _ X₀ hpq h1 h2 N hN
  let L : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K) := Fintype.linearCombination K N
  have hLa : ∀ M, L M = ∑ k, M k • N k := fun M => Fintype.linearCombination_apply _ _ _
  have h0 : spMap (dir c (0 : HIx Dw (psiSet H) → K)).toRingHom ≫ X₀ =
      spMap (algebraMap K (DualNumber K)) ≫ y.x := by
    rw [← h2, ← Category.assoc, spMap_comp_spMap']
    congr 2
    ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have Linj : Function.Injective L := (injective_iff_map_eq_zero L).2 fun M hM =>
    hinj ((_root_.GlobalTheory.T.flag_deformation_const_of_kodaira_spencer_zero hP hG E H Dw l Xo c K y _ hpq (isTanX_dir h1 h2 M)
      (by rw [← hM, hLa]; exact hL M)).trans h0.symm)
  let e := LinearEquiv.ofInjectiveEndo L Linj
  let P := LinearMap.toMatrix' (e.symm : (HIx Dw (psiSet H) → K) →ₗ[K] (HIx Dw (psiSet H) → K))
  have hP' : ∀ M, P.mulVec M = e.symm M := fun M => LinearMap.toMatrix'_mulVec _ M
  refine ⟨spMap (reparam c.F P).toRingHom ≫ X₀, ?_, ?_, fun M => ?_⟩
  · rw [Category.assoc, h1, sOf, spMap_comp_spMap']
    congr 1
    rw [← RingHom.comp_assoc]
    congr 1
    exact (reparam c.F P).comp_algebraMap
  · rw [← Category.assoc, spMap_comp_spMap', ← h2]
    congr 2
    ext z
    simp [reparam]
  · rw [← Category.assoc, spMap_comp_spMap', dir_comp_reparam, hP']
    have := hL (e.symm M)
    rwa [← hLa, show L (e.symm M) = M from e.apply_symm_apply M] at this
end GlobalTheory.FlagTan.KSUniv
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_universal_family : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), 1 ≤ Dw.p + Dw.q → ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧ spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧ ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
  first | exact @_root_.GlobalTheory.FlagTan.KSUniv.kodaira_spencer_universal | exact _root_.GlobalTheory.FlagTan.KSUniv.kodaira_spencer_universal | (intros; apply _root_.GlobalTheory.FlagTan.KSUniv.kodaira_spencer_universal <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberUpperBound
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace MainStatements.Tam.A
end MainStatements.Tam.A
namespace MainStatements.Tam
theorem tamagawa_number_upper_bound : VolSt → StabSt → NumSt → _root_.MainStatements.Tam.ArchimedeanTamagawaUpperBound := fun hV hS hN hP D Tu C t0 hC i P μ 𝓕 hF L hL =>
  MainStatements.Tam.A.up_core hV hS hN D Tu C t0 hC i P μ 𝓕 hF L hL (_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P)
end MainStatements.Tam
end
end
end

