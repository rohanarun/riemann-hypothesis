module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.RecTie
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Formalism.LocalToGlobal.GlobalTheory.ConcNP
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0027
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top

namespace GlobalTheory.Cp

section Cls

open Formalism.MainNotions.Pk

abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

theorem d3_a {C0 : ℝ} {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : D3 C0 𝒜 Fm) : 𝒜 Fm := h.1.1.1.1

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, Formalism.BasicNotions.DV.Used (Fm.D x i) μ

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        Formalism.MainNotions.TwGoodAtAll (Fm.D x i) (Fm.ex x hx i).nch ⟨Formalism.MainNotions.twE Fm x hx i, N0, S⟩

def Duty {eps : ℝ} (Fm : FamP eps) : Prop :=
  PageFix Fm ∧ PageWin Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ TameDistinctF Fm ∧ ChosenWall Fm ∧ TupUsedF Fm ∧ TwAllF Fm

end Cls

section IndefiniteRowSideFullHecke

open _root_.Formalism _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def RationalLiftSpanAtUsedTuples (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def ThThetaG (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def DcPtG (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))


open Classical in
structure NumTieG (P : RowSideFamily ex) : Prop where
  Ij : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.Ij (P.I.tup t) ((i : ℕ) + 1) w = (P.A3.indefDown P.S0).Iw i t (D.plEq w)
  jw : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.jw (P.I.tup t) ((i : ℕ) + 1) w =
      Formalism.DivisionValues.jw ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).HT i t) (D.plEq w)
        ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).Tl i t)
  etaJ : ∀ (i : Fin D.R.m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ (P.A3.indefDown P.S0).Tw then
      P.A3.A.fam.etaJ P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i ((P.A3.indefDown P.S0).μ (D.plEq w)) (D.plEq w) else 0

structure DivRows3G (P : RowSideFamily ex) : Prop where
  sharpRR : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR
  baseRR : HLatTie ex.p0.s.RR (P.A3.indefDown P.S0).RR (P.A3.indefDown P.S0).XE P.I.eRR0
  divisionRows_rationalLift : RationalLiftSpanAtUsedTuples P
  thTheta : ThThetaG P
  num : NumTieG P
  colsBk : ∀ u x y, D.div.Bk u (P.I.eNu u x) (P.I.eRR y) =
    (P.A3.colData2 P.C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)).B (P.I.wU u) x y

end IndefiniteRowSideFullHecke

section At

open _root_.Formalism

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowsAt4 (Q : Formalism.IndefR.RealT Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where
  w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl
  covol : ((Q.Rl.toCx3 Q.F).data Q.F.cr false).L3 (Q.Rl.num Q.F C CH)
  onto : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).ON (Q.Rl.num Q.F C CH)
  lamLow : hO → ((Q.Rl.toCx3 Q.F).data Q.F.cr true).L6 (Q.Rl.num Q.F C CH)
  seeIso : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE
  miStar : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE
  fun0 : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).FUN (Q.Rl.num Q.F C CH)
  pass : Formalism.IndefR.Links.PassIn3 Q.Rl Q.F C CH
  kap : Formalism.L2.Rows.RowsHoldKap3 P

end At

section Serv

open Formalism.MainNotions.Pk _root_.Formalism.L2

end Serv

end GlobalTheory.Cp

namespace GlobalTheory.Fc.R1

open GlobalTheory.Fc GlobalTheory.Cp

def P_hRB : BdP Bundle := fun D O _ b =>
  Formalism.IndefR.RowsB b.B

def P_hPA : BdP Bundle := fun D O _ b =>
  Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3

def OneMap {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ b.B.O (Formalism.IndefR.phEff b.B.Q.Rl) j

abbrev DefT : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), Bundle D O c → ℝ → ℝ → Prop

def H_rRows (DR : DefT) (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, ∃ C : ℝ, 0 ≤ C ∧ EvSel (sel σ) Fm (d3_a hc) fun x hx _ i =>
    RowsAt4 (σ Fm (d3_a hc) x hx i).B.Q C CH (DIVinN Fm) (OneMap (σ Fm (d3_a hc) x hx i)) ∧ DR _ _ _ (σ Fm (d3_a hc) x hx i) C CH

def H_hTF (𝒜 : FamClass) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3

def H_hTu (cT : ℝ → ℝ → ℝ) (𝒜 : FamClass) : Prop :=
  Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm

end GlobalTheory.Fc.R1

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelPrimeColumnValuationsAtBundlePoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.AllBundlePointProperties

open GlobalTheory.Fc

def LevelPrimeColumnValuationsClosed (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u

def LevelPrimeColumnValuationsAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => LevelPrimeColumnValuationsClosed 𝒜

def H_aAtG (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1

def ArithmeticConditionAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aAtG 𝒜

end GlobalTheory.Fc.AllBundlePointProperties

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem.Top

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

open GlobalTheory.Fc

def ReferenceChainEvaluationAdmissible (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u

def ReferenceChainEvaluationAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => ReferenceChainEvaluationAdmissible 𝒜

def H_aPtTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw

def TwistedPointAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPtTw 𝒜

def H_aPer0 (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)

def PeriodAtZeroAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPer0 𝒜

def H_aPerTw (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw

def TwistedPeriodAtBundlePoints {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_aPerTw 𝒜

def H_tie (𝒜 : FamClass) : Prop :=
  Closed (W3 𝒜) fun Fm _ => Formalism.MainNotions.RealPlaceSecondLayerConditions Fm

def Row_tie {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) : Prop := Row Q Lk fun 𝒜 _ => H_tie 𝒜

end GlobalTheory.Fc.PeriodEntriesOverColumns

end
end

