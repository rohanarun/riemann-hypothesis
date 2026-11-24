module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoSec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFlagHodgeIndexVanishing

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ArchimedeanTamagawaUpperBound
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
noncomputable section
namespace MainStatements.Tam
def ArchimedeanTamagawaUpperBound : Prop := ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L)
end MainStatements.Tam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BoundaryUnitValuationIntegral
section
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
end GlobalTheory.BdryUnitVal
namespace GlobalTheory.BdryUnitVal
theorem boundary_unit_at_integral_points : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  intro _ E _ _ _ H Dw l Xo c Y Z V τ sig f hVZ hsig hvn hrd T io y₀ hio hlies
  letI := io.toAlgebra
  obtain ⟨φ, hφ⟩ := exists_factor T io hio
  have hy : ∀ s, GlobalTheory.AllWt.ptF y₀.1 s ∈ (V : Set (Xo.XF c)) := fun s => hVZ ▸ hlies s
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := pt_ext E H Dw l Xo c Y V T io φ hφ y₀.1 hy
  have hp : Dw.mult τ.1 = Dw.p := by rw [Datum.mult, if_pos τ.2]
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := by rw [Datum.mult, if_neg (conj_ne τ)]
  obtain ⟨v, hv, hsv⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 τ.1 Dw.p hp
  obtain ⟨w, hw, hsw⟩ := GlobalTheory.T.exists_lieEigenBasis_of_integralFramedPoint E H Dw l Xo c Y T io φ hφ y₀.1 y₀.2.2 χ hχ1 hχ2 (conjEmb τ.1) Dw.q hq
  let aT : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.V φ := ⟨χ, hχ1, hχ3, v, w, hv, hw⟩
  have hx : (spMap (algebraMap T.V T.Fr) ≫ χ) ≫ pullback.fst _ _ =
      spMap (algebraMap T.V T.Fr) ≫ (χ ≫ pullback.fst _ _) := Category.assoc _ _ _
  obtain ⟨v', hv', ev⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hv
  obtain ⟨w', hw', ew⟩ := GlobalTheory.DetExtendZero.exists_basis (GlobalTheory.FlatRow.eigStable Y.t c) (algebraMap T.V T.Fr) hx hw
  rw [hφ] at hv' hw'
  let aK : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Framed Y V τ.1 T.Fr io :=
    ⟨spMap (algebraMap T.V T.Fr) ≫ χ, by rw [Category.assoc, hχ1, ← GlobalTheory.DetExtendZero.spMap_comp, hφ], by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hχ3 ⟨_, rfl⟩, v', w', hv', hw'⟩
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsChange aT aK (algebraMap T.V T.Fr) 1 1 := by
    refine ⟨hφ, rfl, fun i => ?_, fun i => ?_⟩
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.v_basis.1 k).1) i
      convert this using 2 with k
      exact (ev k).symm
    · have := GlobalTheory.DetExtendZero.comb_one (fun k => (aK.w_basis.1 k).1) i
      convert this using 2 with k
      exact (ew k).symm
  have e := hsig T.V T.Fr φ io aT aK (algebraMap T.V T.Fr) 1 1 hc
  simp only [Matrix.det_one, mul_one] at e
  have hm : Matches Y V τ y₀.1 aK :=
    ⟨hχ2.symm, fun i => ⟨Fin.cast hp.symm i, rfl, by
      change SameVec Y y₀.1 _ (v' i).left
      rw [ev]; exact hsv i⟩, fun i => ⟨Fin.cast hq.symm i, rfl, by
      change SameVec Y y₀.1 _ (w' i).left
      rw [ew]; exact hsw i⟩⟩
  have hr := hrd T.Fr y₀.1 y₀.2.1 aK hm
  change nval T.V 1 (evR Xo c f y₀.1) = 0
  rw [hr]
  change nval T.V 1 (sig T.Fr io aK) = 0
  rw [e]
  exact nval_unit T _ (hvn T.V φ aT)
end GlobalTheory.BdryUnitVal
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_unit_valuation_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  first | exact @_root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | exact _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points | (intros; apply _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CanonicalExtensionExtendsIffModification
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CanonBirat
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin GlobalTheory.TopForm GlobalTheory.MorJac GlobalTheory.Cartier
section General
variable {X Y : Scheme.{0}}
end General
section Flag
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
end Flag
theorem canonicalExtension_extends_iff_modification : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z _ hKS hV ω₀ M ω b s hs m
  haveI := hV.1
  haveI := hV.2.2
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (dimFlag Dw) _
  have hI : IsIntegral (Y₀ TF.X Z) := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsIntegral (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X := hI
  refine extends_iff_of_hom hKS (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) M M.σ (Category.comp_id _) ?_ ω₀ ω hs m
  rw [Modif.off_eq]
  exact M.iso
end GlobalTheory.CanonBirat
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalExtension_birational_invariance : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g : H0 (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str (tens (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z b).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).canChart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB hs).mul ω₀.ω ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).pullOff m)) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @_root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification | exact _root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification | (intros; apply _root_.GlobalTheory.CanonBirat.canonicalExtension_extends_iff_modification <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlagDeformationConstOfKodairaSpencerZero
section
section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
theorem eq_const_of_kodaira_spencer_eq_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, hA, A', hA', π, π', i, h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.kodaira_spencer_full_flag_tangent P E H Dw l Xo c K y x' hpq hx hks
  letI := hA
  letI := hA'
  obtain ⟨q, hq1, hq2⟩ := _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (_root_.GlobalTheory.T.const_deformation_obj_eq P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_deformation_const_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  first | exact @_root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero | exact _root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero | (intros; apply _root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.InteriorEquivariantActionInvariant
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
attribute [local instance] CategoryTheory.Hom.group
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EqvInterior
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}
section Moves
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)
end Moves
section Lift
variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
end Lift
section Move
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Move
section Laws
variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) {Xo : Moduli Dw l} {c : Coeff l}
variable (TF : TorFlag Xo c) (Z : Comp Xo c)
variable (g : LevelAut Dw l) (r : V₀ TF.Y Z ⟶ V₀ TF.Y Z)
  (hr : r ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c g)
end Laws
theorem equivariant_action_preserves_interior : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  intro _ E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ
  refine ⟨fun γ => nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ),
    ⟨fun γ => nF_cart hpq hA TF Z _ _ (hρ γ), fun γ a => act_nF hpq hA TF Z _ _ (hρ γ) a, fun γ₁ γ₂ => ?_⟩,
    fun γ a b hab w w' hw hw' hb ha => ?_⟩
  · apply hom_ext' TF Z
    · rw [nF_snd, Category.assoc, nF_snd, ← Category.assoc, nF_snd, Category.assoc, map_mul, Aut.mul_asIso]
      rfl
    · rw [nF_toU, Category.assoc, nF_toU, ← Category.assoc, nF_toU, Category.assoc, ← nu_mul hpq hA Xo c, map_mul,
        mul_inv_rev]
  · apply hom_ext' TF Z
    · rw [Category.assoc, nF_snd, ← Category.assoc, Category.assoc (ρ γ).asIso.hom]
      erw [hw, hw']
      rw [Category.id_comp, Category.comp_id]
    · have hq : b - liftLa (ι γ)⁻¹ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
        rw [← Submodule.Quotient.eq]
        exact hab.trans (liftLa_spec (ι γ)⁻¹ a).symm
      have L : (w ≫ nF hpq hA TF Z (ι γ)⁻¹ (ρ γ).asIso.hom (hρ γ)) ≫ toU TF Z =
          i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta b).left ≫ (nu hpq hA Xo (ι γ)⁻¹).φ := by
        rw [Category.assoc, nF_toU, ← Category.assoc, sec_toU TF Z b w hw hb, Category.assoc, Category.assoc]
      have R : ((ρ γ).asIso.hom ≫ w') ≫ toU TF Z = (ρ γ).asIso.hom ≫ i₀ TF.Y Z ≫ pullback.fst _ _ ≫ (Xo.univ.eta a).left := by
        rw [Category.assoc, sec_toU TF Z a w' hw' ha]
      rw [L, R, GlobalTheory.LevelActionLaws.eta_congr Xo hq, (nu_spec hpq hA Xo (ι γ)⁻¹).2.1 a,
        ← Category.assoc (pullback.fst _ _), ← GlobalTheory.CompLevelStab.mvF_fst]
      simp only [← Category.assoc]
      rw [← hρ γ]
end GlobalTheory.EqvInterior
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
theorem _root_.GlobalTheory.T.interior_equivariant_action_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹) → ∃ n : Γ → ((GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left ⟶ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)).left), GlobalTheory.EqvAct.IsEqvAct ρ (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullAct TF Z (j₀ TF.Y Z)) n ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ (𝟙 (V₀ TF.Y Z)) (GlobalTheory.EqvAct.pullG TF Z (j₀ TF.Y Z)) (GlobalTheory.EqvAct.pullψ TF Z (j₀ TF.Y Z)) n := by
  first | exact @_root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | exact _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior | (intros; apply _root_.GlobalTheory.EqvInterior.equivariant_action_preserves_interior <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerOfDirectSumDeformation
section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.Published GlobalTheory.Published.AbelianDeRham DividedPowers
variable {R : Type} [CommRing R]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
open GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.Published ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]
theorem kodaira_spencer_direct_sum : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K]
    (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X),
    1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x →
    ∀ N : ι → HIx Dw (psiSet H) → K,
      (∀ k, IsKS (psiSet H) y (spMap (dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) →
      ∀ M : ι → K, IsKS (psiSet H) y (spMap (dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  intro Pr E _ _ _ H Dw l Xo c K _ _ y ι _ _ X hpq hXs hXy N hN M
  have P := Pr.p5
  have e₀ : ∀ m : ι → K, DeRham.epsRed K ≫ spMap (dir c m).toRingHom =
      spMap (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom := fun m => by
    rw [← Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => fst_dir (c := c) m z)
  have tan : IsTanX y (spMap (dir c M).toRingHom ≫ X) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hXs]
      unfold sOf
      rw [← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun r => (dir c M).commutes _)
    · rw [← Category.assoc, ← hXy]
      exact congrArg (· ≫ X) (e₀ M)
  obtain ⟨M₀, A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, what₂⟩ :=
    _root_.GlobalTheory.T.exists_kodaira_spencer_flag_tangent Pr E H Dw l Xo c K y _ hpq tan
  obtain ⟨C, _, πC, hC⟩ := exists_isGrpPullback Xo.univ.t.G X
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have aC := PolPull.isAbelianScheme_of_isGrpPullback hU hC
  have gC := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hC.1 hg
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hL := (P.2.1 K A _ hA gA).1
  obtain ⟨φ, hφ, eφ⟩ : ∃ φ : A'.left ⟶ C.left, IsGrpPullback A' C (spMap (dir c M).toRingHom) φ ∧ φ ≫ πC = π' := by
    have w : π' ≫ Xo.univ.t.G.hom = (A'.hom ≫ spMap (dir c M).toRingHom) ≫ X :=
      hπ'.1.w.trans (Category.assoc _ _ _).symm
    exact ⟨hC.1.lift _ _ w, hC.cancel (hπ'.congr rfl (hC.1.lift_fst _ _ w).symm) (hC.1.lift_snd _ _ w),
      hC.1.lift_fst _ _ w⟩
  have h₀ := (hi.comp hφ).congr (e₀ M) rfl
  refine ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hpol, hu, hl, fun τ a => ?_⟩
  obtain ⟨-, -, f, hf, hd, -⟩ := what₂ τ a
  obtain ⟨gs, hgs⟩ := exists_isFilLift_dir P aC gC h₀ hf
  have row : ∀ k, ∃ w, IsLieComb (fun b => N k ⟨τ, a, b⟩) (ub τ.1) w ∧ DeRham.IsLieImage (gs k) w := fun k => by
    obtain ⟨B, _, χ, hχ⟩ := exists_isGrpPullback C (spMap (dir c (Pi.single k (1 : K))).toRingHom)
    have w : (i ≫ φ) ≫ C.hom = (A.hom ≫ DeRham.epsRed K) ≫ spMap (dir c (Pi.single k (1 : K))).toRingHom := by
      rw [Category.assoc _ (DeRham.epsRed K), e₀]
      exact h₀.1.w
    have sq : hχ.1.lift _ _ w ≫ χ = i ≫ φ := hχ.1.lift_fst _ _ _
    have hj : IsGrpPullback A B (DeRham.epsRed K) (hχ.1.lift _ _ w) :=
      hχ.cancel (h₀.congr (e₀ _).symm sq.symm) (hχ.1.lift_snd _ _ _)
    obtain ⟨v, hc, hv⟩ := (hN k).row P hj hπ (hχ.comp hC)
      (by rw [← Category.assoc, sq, Category.assoc, eφ, hiπ]) hpol hu hl τ a hf hd
    obtain ⟨v', hv', -⟩ := hL.1 (gs k)
    have fl := hgs (Pi.single k 1) B χ _ hj hχ sq
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at fl
    obtain rfl := IsKSValue.unique P (PolPull.isAbelianScheme_of_isGrpPullback aC hχ)
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hχ.1 gC) hv ⟨_, fl, hv'⟩
    exact ⟨_, hc, hv'⟩
  choose w hwc hwl using row
  let e := (Fintype.equivFin ι).symm
  refine ⟨lieComb (fun q => M (e q)) (fun q => w (e q)), ?_, f, hf, hd, _, ?_,
    isLieImage_lieComb _ (f := fun q => gs (e q)) fun q => hwl _⟩
  · obtain ⟨V, _, _, v, -, -, htan, hcomb, -, -⟩ := _root_.GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo K y.x
    choose n hn using fun σ k => (htan _).1 (y.tan σ k)
    have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → V) (w : epsR K ⟶ A),
        (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
      fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
    have hun : ∀ j, (ub τ.1 j).left ≫ π = v (n τ.1 j) := fun j => (hu _ j).trans (hn _ j).symm
    rw [key _ _ _ _ hun, (key _ _ _ _ fun q => (key _ _ _ _ hun).1 (hwc (e q))).1 (isLieComb_lieComb _ _),
      e.sum_comp fun k => M k • ∑ j, N k ⟨τ, a, j⟩ • n τ.1 j]
    congr 1
    simp only [Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
    exact Finset.sum_comm
  · rw [e.sum_comp fun k => M k • gs k]
    exact hgs M A' φ i hi hφ rfl
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_of_direct_sum_deformation : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (ι : Type) [Fintype ι] [DecidableEq ι] (X : Sp (TrivSqZeroExt K (ι → K)) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → X ≫ Xo.s = sOf c _ → spMap (TrivSqZeroExt.fstHom c.F K (ι → K)).toRingHom ≫ X = y.x → ∀ N : ι → GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, (∀ k, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c (Pi.single k (1 : K))).toRingHom ≫ X) (N k)) → ∀ M : ι → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) (∑ k, M k • N k) := by
  first | exact @_root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | exact _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum | (intros; apply _root_.GlobalTheory.FlagTan.kodaira_spencer_direct_sum <;> assumption)
end
end

