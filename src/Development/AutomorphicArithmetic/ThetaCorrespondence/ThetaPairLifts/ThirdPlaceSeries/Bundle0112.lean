module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0059
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDimensionLogBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0488
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0097
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairForm
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop
noncomputable section
namespace GlobalTheory.MiTop.PairingL2
open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned
variable {D : D7}
end GlobalTheory.MiTop.PairingL2
namespace GlobalTheory.MiTop.PairingL2
open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem pwOf_op_ramCrd_eq_puFun (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u w : D.what₂.Word) (hwu : w = u) (hc : W.P.I.wU w = W.P.I.wU u)
    (x : Fin (W.P.Dc.a (W.P.I.wU u)) → ℂ) (T : Cu W.S.X u W.S.Y.hK) (hT : _root_.GlobalTheory.MiTop.IsColumnForm W u T (_root_.GlobalTheory.MiTop.columnOfCoordinates W u x)) :
    (((_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin w).op (ramCrd (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) x) : HHX W.S.X) : L2X W.S.X) =
      PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) T := by
  subst hwu
  have hi : ∀ i : Fin (W.P.Dc.a (W.P.I.wU w)), Fin.cast (congrArg W.P.Dc.a hc).symm i = i := fun i => Fin.ext rfl
  have hfun : (fun i => D.eMu w (D.jN w (W.P.I.eNu w
      (Pi.single (Fin.cast (congrArg W.P.Dc.a hc).symm i) (1 : D.what₂.LL))))) =
      (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) := by
    funext i
    exact congrArg (fun k => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single k (1 : D.what₂.LL))))) (hi i)
  rw [hfun]
  have hr : Fintype.linearCombination ℂ (fun i => D.eMu w (D.jN w (W.P.I.eNu w (Pi.single i (1 : D.what₂.LL))))) x =
      D.eMu w (_root_.GlobalTheory.MiTop.columnOfCoordinates W w x) := by
    refine (Fintype.linearCombination_apply ℂ _ x).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.MiTop.columnOfCoordinates, map_sum, map_smul]
  refine op_eq (_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin w) _ T ?_
  show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr w) W.S.Y.hK T = _
  refine hT.trans ?_
  show _ = ((Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ _ x) : (D.mem w).A.Mu0) : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)
  exact congrArg (fun z : (D.mem w).A.Mram => (z : (D.mem w).C.cls 0 → (D.mem w).C.Y 0 → ℂ)) hr.symm
end GlobalTheory.MiTop.PairingL2
namespace GlobalTheory.MiTop.PairingL2
open Formalism.L2.SG.JoinSI Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowsJoinPinned
theorem pairForm_alt : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → _root_.GlobalTheory.MiTop.PairingFormCondition W v := by
  intro hDS hCusp D L hT Gi Gl Kc Yd cX ex W hB v hv
  have hM := (_root_.GlobalTheory.MiTop.botHyp_match_alt W hB).2.2.2.2.2
  obtain ⟨v₀, hv₀, hF⟩ := exists_eval (W.Q.seeEval hB.see.2) W.Q.instEq W.Q.ιS_eq
  have key : ∃ l : ℂ, l ≠ 0 ∧ ∀ e : W.Q.Rl.HE.H,
      W.Q.Rl.HE.e e ∈ W.Q.Rl.toRealDat.EEat (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true) →
        _root_.GlobalTheory.MiTop.rowFormOfVector W e (PiTensorProduct.tprod ℂ v₀) = l • _root_.GlobalTheory.MiTop.rowFormOfVector W e (PiTensorProduct.tprod ℂ v) := by
    by_cases hl : ∃ l : ℂ, l ≠ 0 ∧ PiTensorProduct.tprod ℂ v₀ = l • PiTensorProduct.tprod ℂ v
    · obtain ⟨l, hl0, hl⟩ := hl
      exact ⟨l, hl0, fun e _ => (congrArg (_root_.GlobalTheory.MiTop.rowFormOfVector W e) hl).trans ((_root_.GlobalTheory.MiTop.rowFormOfVector W e).map_smul l _)⟩
    · refine ⟨1, one_ne_zero, fun e he => ?_⟩
      by_cases h0 : _root_.GlobalTheory.MiTop.rowFormOfVector W e = 0
      · rw [h0]
        exact (smul_zero (1 : ℂ)).symm
      · obtain ⟨F, h1, h2, -⟩ := hF ⟨W.Q.Rl.HE.e e, he⟩
        exact absurd (_root_.GlobalTheory.T.unit_vector_rows_conjugate_alt hDS hCusp W hB v₀ v hv hv₀ (_root_.GlobalTheory.MiTop.rowFormOfVector W e) (hM e he) h0 F h1 h2) hl
  obtain ⟨l, hl0, hl⟩ := key
  refine ⟨starRingEnd ℂ (W.Q.uS * (W.Q.κS : ℂ)) * l, mul_ne_zero ?_ hl0, ?_⟩
  · have hu : W.Q.uS ≠ 0 := by
      intro h
      have := W.Q.uS_norm
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact (map_ne_zero _).2 (mul_ne_zero hu (Complex.ofReal_ne_zero.2 W.Q.seeK.1.ne'))
  intro e he u m hm x x' hx T b hTc hP
  obtain ⟨φ, hφ, rfl⟩ := hP
  refine (inner_join (twQ W.P) W.Dcf W.Spf (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs W.P.Zs W.Q.zs W.P.Dc W.Q.dc W.S.Y.hK W.S.G W.Q.wdD
    (fun y => _root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD y)) W.Q.bR (W.Q.sp.trans W.Q.spPin) W.Q.sEE W.Q.sEEc W.Q.sEEj e m (W.P.I.wU u) hm
    x' x hx.symm).trans (congrArg (cj (twQ W.P)) ?_)
  obtain ⟨F, h1, -, h3⟩ := hF ⟨W.Q.Rl.HE.e (Tw.out e), he⟩
  have hz := (congrArg (fun b => (((_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd b x) : HHX W.S.X) : L2X W.S.X))
    (funext (hB.pins.bR_read (W.P.I.wU u)))).trans
    (_root_.GlobalTheory.MiTop.PairingL2.pwOf_op_ramCrd_eq_puFun W u (W.Q.wdD (W.P.I.wU u)) (W.Q.wdD_wU u) (W.Q.wU_wdD (W.P.I.wU u)) x T hTc)
  refine Eq.trans ?_ (inner_smul_star W.Q.instEq _ _ _ l (W.Q.uS * (W.Q.κS : ℂ)) (hl (Tw.out e) he) F φ _ h1 hφ _ _ h3 hz)
  exact congrArg (fun y => ⟪Tw.out y, (_root_.Formalism.IndefR.pwOf_alt W.S W.Q.hin (W.Q.wdD (W.P.I.wU u))).op (ramCrd (W.Q.bR (W.P.I.wU u)) x)⟫_ℂ)
    (W.Q.seeDef e he)
end GlobalTheory.MiTop.PairingL2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBounds
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.DefSizes
namespace GlobalTheory.CovTop.DefSizes
theorem parameters_scale_rank_gap_bounds :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| *
      (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) -
        (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) +
      (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) +
      ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤
      C * unitE p := by
  have hdim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ w : ℤ,
      (GlobalTheory.DualWeyl.dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := fun n la h => (_root_.GlobalTheory.WeylDimBound.dim_weyl_dual_bound n la h).2.2
  have H := Closed.and _root_.GlobalTheory.CovTop.WtShape.wtN_z (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1)
  simp only [_root_.GlobalTheory.CovTop.LiftWeightNumerator, _root_.GlobalTheory.CovTop.HostNAlt, _root_.GlobalTheory.CovTop.LiftsCondition] at H
  unfold _root_.GlobalTheory.CovTop.LiftsCondition
  refine Closed.imp H ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, hw⟩, ⟨A, -, hh⟩⟩ := h
  obtain ⟨x0, h⟩ := _root_.GlobalTheory.CovTop.EventuallyAtAllPoints.and hw hh
  exact ⟨35, by norm_num, x0, fun x hx hle ι p hp i _ =>
    sizes_at p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) (Fm.sizes x hx ι) hdim⟩
end GlobalTheory.CovTop.DefSizes
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PatternOfTraceAtGStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_measure_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ κ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0), _root_.GlobalTheory.FamTrace.TraceAtElement a κ → ∀ i : Fin a.n, ∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1) := by
  first | exact @_root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt | exact _root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt | (intros; apply _root_.GlobalTheory.FamTrace.TraceBwd.pattern_of_traceAtG_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemH
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.LevProd.Fwd
section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
end Columns
section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
end Local
section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Split
end GlobalTheory.LevProd.Fwd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
namespace GlobalTheory.LevProd.Fwd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
set_option maxHeartbeats 1000000 in
theorem mem_prCat_of_pr_eq (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : J.Ch₀ j)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (hg : g ∈ J.A.U j β)
    (y : Fin J.r → (Formalism.L2.Col.Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N j)))
    (hy : ∀ i r s, (J.G i).q.pr (mt _ g (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm r)
      (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm s)) = (J.G i).q.pr (incA (I.rec7 l Z) (y i (Pi.single s 1) r))) (i : Fin J.r) :
    y i ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get (show j < B.R.m by omega)) (J.P i)) := by
  have hjm : j ≤ B.R.m := by omega
  have hA := hJ.is
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hjm β
  obtain ⟨-, κ, hκ⟩ := (hA.U j hjm _ g).1 hg
  have hd : Disjoint (B.primes X).vGs (I.Q (W.P.I.tup t)) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I _) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have huni : κ.1 ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
    have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hjm).1
    have huni : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hjm) (B.T u)
        (I.rec7 l Z).R.f (J.A.bad j)) (x : TC.GA B (B.R.N j)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
      intro S x hx
      have h := ((S.U_eq x).1 hx).1
      rw [hgram] at h
      exact h
    exact huni _ κ.1 κ.2
  have hloc : ∀ PP i, J.pl i = PP →
      GlobalTheory.Mem.ColAd.locM (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) PP κ.1 = GlobalTheory.Mem.ColAd.ratM PP (y i) := by
    rintro _ i rfl
    exact locM_of_pr (J.G i).q (J.pl i) (J.G i).idem _ _ g κ.1 hκ (y i) (hy i)
  have hsurj : ∀ P : I.Q (W.P.I.tup t), ∃ i, J.pl i = P.1 := fun P => hJ.surj P.1 ((hW.tq.Q t P.1).2 P.2)
  choose ι hι using hsurj
  have hmem : J.pl i ∈ I.Q (W.P.I.tup t) := (hW.tq.Q t _).1 (J.mem i)
  obtain ⟨κ', hκ', e'⟩ := mem_levQ I hI (hA.reads j hjm) c κ.1 huni κ.2 (fun P => by
      rw [hJ.std j (by omega)]
      refine Matrix.ext fun r s => ?_
      refine (GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hI _ ⟨P.1, Finset.mem_union_right _ P.2⟩
        (Finset.disjoint_right.1 hd P.2) u _ r s).trans ?_
      rw [Matrix.one_apply]
      split_ifs <;> simp)
    (fun P => y (ι P)) (fun P => hloc _ _ (hι P)) ⟨J.pl i, hmem⟩
  have hii : ι ⟨J.pl i, hmem⟩ = i := hJ.inj (hι ⟨J.pl i, hmem⟩)
  rw [hii] at e'
  have hb : levQAt I.sel (I.tup (W.P.I.tup t)) (I.idx (W.P.I.tup t)) (I.Tp (W.P.I.tup t)) j c.1 =
      (I.idx (W.P.I.tup t)).levQ j ((J.A.b0 j (J.A.chOf j c)).get (show j < B.R.m by omega)) := by
    rw [← (hA.rep j hjm c).1]
    unfold levQAt Idx.get
    conv_lhs => rw [← Option.some_get (c.1.2.2 (show j < B.R.m by omega))]
    rfl
  rw [hb, hL.grpQ, Subgroup.mem_subgroupOf, e'] at hκ'
  have hPi : J.P i = ⟨J.pl i, Finset.mem_union_right _ hmem⟩ := Subtype.ext (hJ.eq i)
  rw [hPi]
  exact hκ'
end GlobalTheory.LevProd.Fwd
namespace GlobalTheory.LevProd
open GlobalTheory.LevProd.Fwd
set_option maxHeartbeats 1000000 in
theorem phi_mem_H_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ g ∈ J.A.U j (J.ι j α), ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α g hg
  have hjm : j ≤ B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  have hrk := rankN (I.rec7 l Z) j hjm
  have hstd := fun i : Fin J.r => (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; exact this.trans (Nat.le_succ _))
  choose e he hF using hstd
  let e₀ : Fin J.r → (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ≃ Fin ((I.rec7 l Z).R.N j)) := fun i => (e i).trans (finCongr hrk)
  have key := fun i : Fin J.r => prCat_iff _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega) _ _
      (hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (by omega) (J.ι j α)) (e₀ i) (fun r => he i r)
  have hHo : ∀ i, IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := fun i => by
    have h := (key i).1
    rw [hJ.sec j hjm α i] at h
    exact h
  have hHr : ∀ i y, y ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j (J.ι j α)).get (show j < B.R.m by omega)) (J.P i)) →
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := fun i y hy => by
    have h := ((key i).2 y).1 hy
    rw [hJ.sec j hjm α i] at h
    exact h
  have hUo := (GlobalTheory.ChartReps.twDat_reps I hW.tr.ok hP l Z u _ _ J.A hJ.is j hjm (J.ι j α)).1.opn
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl hglc hglp _ using hgl
  have hAt : ∀ i x, gl i x ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun i x =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hglp i x).1 _ rfl
  have hVo : ∀ i, IsOpen {x | gl i x ∈ J.A.U j (J.ι j α)} := fun i =>
    hUo.preimage (f := fun x => (⟨gl i x, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt i x)⟩ : GfC _)) ((hglc i).subtype_mk _)
  have hy : ∀ i, ∃ y, GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈
      (fun v => (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * v) ⁻¹' ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set _) ∩ {x | gl i x ∈ J.A.U j (J.ι j α)}) := fun i =>
    GlobalTheory.denseGL_completion _ (J.G i).compl.dense (e₀ i) (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i) _
      (((hHo i).inter (hVo i)).preimage (continuous_const.mul continuous_id))
      (by
        rw [Set.mem_preimage, inv_mul_cancel]
        exact ⟨one_mem _, by rw [Set.mem_setOf_eq, map_one]; exact one_mem _⟩)
  choose y hy using hy
  set x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k := fun i =>
    (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) with hx
  have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
    intro i
    funext i'
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
    by_cases h : i' = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
    · rw [Pi.mulSingle_eq_of_ne h]
      exact locHom_eq_one (J.G i).q (J.G i').q _ _
        (fun hv => h ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).1 hv)) (hAt i _)
  have hg' : g * ((List.finRange J.r).map fun i => gl i (x i)).prod ∈ J.A.U j (J.ι j α) := by
    refine mul_mem hg (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact (hy i).2
  have hφ' : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (g * ((List.finRange J.r).map fun i => gl i (x i)).prod) i =
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) := by
    intro i
    rw [map_mul, map_list_prod, List.map_map]
    simp only [Function.comp_def, hphi]
    rw [list_prod_mulSingle x, Pi.mul_apply]
    exact mul_inv_cancel_left _ _
  intro i
  have h1 := hHr i _ (_root_.GlobalTheory.LevProd.Fwd.mem_prCat_of_pr_eq hW J hJ j hj _ _ hg' y (fun i r s => by
    obtain ⟨r, rfl⟩ := (e₀ i).surjective r
    obtain ⟨s, rfl⟩ := (e₀ i).surjective s
    exact (locHom_std (J.G i).q _ _ (e i) (hF i) _ r s).symm.trans (congrArg (fun z => z.val r s) (hφ' i))) i)
  have h2 : x i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := (hy i).1
  have h3 := mul_mem h1 (inv_mem h2)
  rw [hx] at h3
  simpa using h3
end GlobalTheory.LevProd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.SamePlace
open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}
set_option maxHeartbeats 1000000 in
theorem phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.LevProd.localHomProduct J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hm := moves_of_mem_KO (J₀.G i₀).q ((J₀.G i₀).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₀ i₀ hj; omega)) hsd
    ((J₀.G i₀).latX j _) h0
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm ((J.G i).latX j _) g hm _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
end GlobalTheory.LevProd.SamePlace
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PhiMemKOOfNotTwAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.OffTwist
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.LevProd.OffTwist
theorem GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ ((ha.stdQ _ _).1 j _) (B.T u) hv
    (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
  · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
    exact ⟨c, hc⟩
  · refine (hlb _).2 fun r => ?_
    by_cases h : r = s
    · subst h
      refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
    · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
  · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
    exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
      ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnderStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_twist_local_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads →
    Function.Injective (fun i => (J.G i).q.v) ∧ ∀ i, (J.G i).q.v = (J.pl i).under (𝓞 (I.rec7 l Z).host.F) := by
  first | exact @_root_.GlobalTheory.Fam.QJPlaces.places_under_alt | exact _root_.GlobalTheory.Fam.QJPlaces.places_under_alt | (intros; apply _root_.GlobalTheory.Fam.QJPlaces.places_under_alt <;> assumption)
end
end

