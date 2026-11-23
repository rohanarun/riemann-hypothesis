module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.BigOn.Exp.TupLe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def AllPtsAlt (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}, PtAt ex Csz → Fin D.R.m → Prop) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts)
    (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz) (j : Fin D.R.m), p.PointConditions' → More p → Q p j
open Classical in
def PlacesCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ ex _} p j => ∀ w : D.what₂.places.Pl, D.plEq w ∈ p.R.twPl →
  IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w) →
  ∀ ρ : Setup D.ntw, ρ.Good → RealPin p.R p.cG ρ →
  ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) →
  p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
    (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi →
  SplitSet (p.R.Q (p.R.mu (D.plEq w))) ∧
    (∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) ∧
    idem (p.R.Q (p.R.mu (D.plEq w))) + cA D (idem (p.R.Q (p.R.mu (D.plEq w)))) =
      idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q) +
        cA D (idem ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
          (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q))
open Classical in
def FlatCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)) (ψ : Twist D Circle) (t : p.P.T),
  B.Good → BaseOf (R2 p) j B → ψ.Good → B.admitted ψ.Q → (R2 p).xi t = B.de.chi * ψ.chi →
  idem ((R2 p).Q t) + cA D (idem ((R2 p).Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) →
  ∃ (z : GA D (Vc D j)) (c : ℂ), SuppAt (idem ((R2 p).Q t)) (Vc D j) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) t) c ∧
    (princ B).vecFlat ψ = c • (R2 p).ωP j t (z⁻¹, 1) ((R2 p).vP j t)
def TraceCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ρ.LevelOf D.nexp →
  ∀ (i : D.ntw.Tw) (b : Bool) (ψ : Twist D Circle) (ω : PairRep (Vc D j) (Wc D j)), ψ.Good → (ρ.B i j b).admitted ψ.Q →
    (ρ.B i j b).IsWeil ψ.chi ω → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (series (ρ.B i j b).F ω ((princ (ρ.B i j b)).vecFlat ψ) h P) =
        series (ρ.B i j b).F ω ((ρ.B i j b).vecFlat ψ) h P
def CoefficientCondition' : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ c : ℂ, c ≠ 0 → IsScale p.R p.v₀ B c → ∀ u : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ,
    (∀ τ, (u τ : ((R2 p).MW j (sg0 D p.P.A3.A)).sm τ) = p.v₀ j _ τ) → ∀ O' : Subring ℂ, IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ h ∈ GfC (Vc D j), ∀ v, InCoefLat (R2 p) j h v →
      ∃ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h), (R2 p).ioP j (PiTensorProduct.tprod ℂ u) v = c • P
def SmallnessCondition : Prop := _root_.GlobalTheory.BigOn.Exp.TupLe.AllPtsAlt fun {D _ _ _ _ _ _ _ _ _} p j => ∀ (B : Base (Vc D j) (Wc D j)), B.Good → BaseOf (R2 p) j B →
  ∀ O O' : Subring ℂ, IsCoefRing (embLL0 D) (labLL0 D) O → IsCoefRing D.what₂.embLL (labLL D) O' →
    ∀ (h : GA D (Vc D j)), ∀ P ∈ B.coefLat D.what₂.embLL (labLL D) O' (finPt (Vc D j) h),
      P ∈ Submodule.span O' (B.coefLat (embLL0 D) (labLL0 D) O (finPt (Vc D j) h) : Set (PolF D (Wc D j).rank (Vc D j).rank))
section Units
variable {O K : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K]
end Units
section Read
variable {D : D7} {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ D.nexp i j b)
  {L : Type} [Field L] [Algebra (D.ntw.O i) L] (e : L →+* ℂ) (he : ∀ c : D.ntw.O i, e (algebraMap _ L c) = ρ.eO i b c)
end Read
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
variable {p w j}
end Point
section Move
variable {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
include hρ
end Move
section Assembly
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem realTw_le_alt (s1 : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition) (s2 : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition) (s3 : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition) (s4 : _root_.GlobalTheory.BigOn.Exp.TupLe.CoefficientCondition') (s5 : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition) (hr : p.PointConditions') (hm : More p)
    (hL : Links2 p) (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin p.R p.cG ρ) (hlev : ρ.LevelOf D.nexp)
    (hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)))
    (e : FractionRing (ex.nch.Oe w) →+* ℂ) (h1 : ∀ x, e (ex.nch.embW w x) = D.what₂.embLL x)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    {ν : ℂ} (hν : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν) (hR : RatAt p w j hρ ν) {rd : Can p w j} (hc : IsCan p rd) :
    realTw p rd ≤ twLat p w j hρ ν := by
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hK := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)
  obtain ⟨Z⟩ := hm.2.2.series
  have hF : Faithful (rdAt p w j hρ ν) := realRd_faithful _ _ _ _ _ _ _ _ _ _ p.nexp p.v₀ ρ hρ _ j _ ν hν.1 hL.2.2.1
    p.charW.base.models.HW (Z.vec j) hK
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z, cz, hz, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  have hO' : IsCoefRing D.what₂.embLL (labLL D) (imO ex.nch w e) := by
    refine ⟨fun τ => FWT.embV_spec (RingHom.id _) D.what₂.embLL (RingHom.comp_id _) τ, fun a => ?_⟩
    obtain ⟨b, hb⟩ := mem_of_ringOfIntegers (O := ex.nch.Oe w) (ex.nch.embW w) a
    exact ⟨b, by rw [RingHom.comp_apply, hb, h1]⟩
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨-, -, -, -, u, hu, -⟩ := id hs
  refine le_of_comb hρ hc hR hF hK e h1 h2 hN ?_
  rintro x ⟨h, hh, v, hv, hx⟩
  obtain ⟨P, hP, hio⟩ := s4 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 c c0 hs u hu _ hO' h hh v hv
  have hP' := s5 _ _ _ _ _ _ _ _ _ _ p j hr hm _ hB hB0 _ _ (hρ.isCoefRing (ex.nch.twI w) (ex.nch.sd w)) hO' h P hP
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hzf
  refine ⟨ν⁻¹ * c * cz⁻¹, unitOff_mul (unitOff_root hn ?_) (unitOff_inv hcz),
    series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((ρ.B (ex.nch.twI w) j (ex.nch.sd w)).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]
  · clear hP hio
    induction hP' using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨s, h', P', hd, g, hg, a, ea⟩ := series_eq_gen hρ _ j _ hok hω hhz (lat_translate_of_prime hρ _ j _ p1 p2 hz hQ)
      rw [ea]
      exact Submodule.smul_mem _ (⟨_, ⟨algebraMap _ _ a, h2 a⟩⟩ : imO ex.nch w e) (Submodule.subset_span ⟨s, h', P', hd, hg⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
    | smul a y _ hy =>
      rw [show a • y = (a : ℂ) • y from rfl, map_smul]
      exact Submodule.smul_mem _ a hy
  · have e1 : adForm (R2 p) j x (p.v₀ j _) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
        (ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v) :=
      ((congrArg (adForm (R2 p) j x) (funext hu)).symm.trans (hx u)).trans (one_smul _ _)
    have e2 : ser (R2 p) j ((R2 p).mu (D.plEq w)) ((R2 p).vP j ((R2 p).mu (D.plEq w))) u h v = (c * cz⁻¹) •
        series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
            (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))) (h * z) P := by
      rw [mul_comm, mul_smul, ← map_smul, ← hio]
      refine Eq.trans ?_ (congrArg (cz⁻¹ • ·) (hB0.series_eq_ser _ _ u (h * z) v)).symm
      rw [hfl]
      funext g
      have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z⁻¹ cz (inv_mem hzf) u (h * z) v g
      rw [mul_inv_cancel_right] at e3
      refine Eq.trans ?_ (congrArg (cz⁻¹ * ·) e3).symm
      exact (inv_mul_cancel_left₀ hcz.1 _).symm
    rw [e1, e2, map_smul, s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, smul_smul, mul_assoc]
end Assembly
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.Ind
theorem small_along_alt : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  intro 𝒜 σ hS hP
  refine Formalism.MainNotions.Pk.Closed.of_class fun Fm CH hw _ _ => ⟨0, le_refl _, fun C _ => ?_⟩
  obtain ⟨x0, hx0⟩ := GlobalTheory.four_f_r_le_min_g_family _ Fm
  refine ⟨x0, fun x hx hx0' i => ?_⟩
  have hA := hx0 x hx0' hx i
  have hs := hS Fm (w3_a hw) x hx i
  have hp := hP Fm (w3_a hw) x hx i
  refine ⟨fun w hw1 => ((σ Fm (w3_a hw) x hx i).muDef C CH).2.2.2 w |>.2 hw1, ?_, ?_⟩
  · exact _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  · exact _root_.GlobalTheory.T.indefScale_theta_degree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Fm.D x i).tcLL hA (σ Fm (w3_a hw) x hx i).ok1 hp.1 C CH
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallPlacePrimeLocal
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem emb_cj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    (τ : E →+* PadicAlgCl l) :
    io.toRingHom.comp (GlobalTheory.ExpFrame.cj τ) = ComplexEmbedding.conjugate (io.toRingHom.comp τ) := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E (io.toRingHom.comp τ) x
private theorem places_inj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    {ι : Type} {inc : ι → (E →+* PadicAlgCl l)} (h : IsHalf inc) :
    Function.Injective fun τ => InfinitePlace.mk (io.toRingHom.comp (inc τ)) := by
  intro τ τ' e
  have hi : ∀ a b : E →+* PadicAlgCl l, io.toRingHom.comp a = io.toRingHom.comp b → a = b := fun a b hab =>
    RingHom.ext fun x => io.injective (RingHom.congr_fun hab x)
  rcases InfinitePlace.mk_eq_iff.1 e with e | e
  · exact h.1 (hi _ _ e)
  · exact absurd (hi _ _ ((emb_cj_pz io _).trans e)) (h.2.1 τ τ')
set_option maxHeartbeats 1600000 in
private theorem frame_embedding_exists {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hmu : ∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res N (mu τ))) (hθ : F.IsEig mu θ) :
    ∃ π : Submodule ℂ (UA D.host.E N → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧
        (∀ v, GlobalTheory.Hk3.Good p.R.toRealDat t v → ∀ x ∈ locU N v, cLoc v x ∈ GlobalTheory.LFun.KGL v (n := N) → RU D.host.E N x φ = φ) ∧
        ∀ Q : (blk p j t).Pl, (∀ x ∈ locU N (labOf p j t Q), cLoc (labOf p j t Q) x ∈ GlobalTheory.LFun.KGL (labOf p j t Q) (n := N) →
          RU D.host.E N x φ = φ) ∧
        ∀ i, (ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E N).comp (locU N (labOf p j t Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j t Q) (n := N)).comap ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j t Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab N (ix i).2))
              ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype x)) φ = T.io (θ i) • φ := by
  subst hN
  classical
  have hs : (Vc D j).SigOK := D.sp.V_sig _
  have hp : (Vc D j).IsPosDef := p.vpos j
  have hinf : Formalism.L2.Theta.IsInfFam p.R.θ := p.charW.base.models.inf
  obtain ⟨jj, h₀, hTr⟩ := GlobalTheory.DefTransfer.exists_isTransfer D (Vc D j) p.R.θ hinf hs hp
  obtain ⟨B, hB1, hB2⟩ := UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary D (Vc D j) hs hp jj hTr.2.1
  obtain ⟨Fm, hF0, hFl, hFr, hFh⟩ := UpperTheory.exists_nonzero_vectorValued_eigenform_unitary p j t F e0 ix inc T mu θ hθ
  have hb : ∀ τ, T.io.toRingHom.comp (e0.comp (Links.labLL D τ)) = Formalism.BasicNotions.TH.tauE D τ := fun τ => by
    rw [← Formalism.IndefR.Conj.labE_base τ]
    exact RingHom.ext fun x => T.liftFrame_embedding_base _
  have hemb : ∀ τ, T.io.toRingHom.comp (inc τ) = Formalism.BasicNotions.TH.tauE D τ ∨
      T.io.toRingHom.comp (inc τ) = ComplexEmbedding.conjugate (Formalism.BasicNotions.TH.tauE D τ) := fun τ => by
    rcases T.lab τ with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, emb_cj_pz, hb])
  have hfix : ∀ (k : Formalism.L2.Theta.GA D (Vc D j)), (∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t,
      levChi p j t ⟨_, h⟩ = 1) → ∀ g, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k) = Fm g := by
    rintro k ⟨h, h1⟩ g
    have := hFr ⟨_, h⟩ g
    rw [h1, Units.val_one, one_smul] at this
    exact this
  have hev : ∀ᶠ κ in nhds (1 : Formalism.L2.Theta.GA D (Vc D j)), ∀ g,
      Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict κ) = Fm g :=
    (GlobalTheory.ThetaIntegrand.eventually_level (Vc D j) (p.R.βV j) (p.R.datVt j t)).mono fun κ h => hfix κ h
  obtain ⟨F1, h10, h1l, h1i, h1e, A, hA⟩ := UpperTheory.vectorValued_autForm_equivariant_infinite_component D (Vc D j) p.R.θ jj h₀ hinf hTr
    (fun τ => T.io.toRingHom.comp (inc τ)) hemb mu T.sh Fm hF0 hFl hev
  let lam : D.what₂.Tau → DomWeight (Vc D j).rank := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + T.sh τ, fun a b hab => add_le_add_left (Int.ofNat_le.2 (hmu τ hab)) _⟩
  obtain ⟨π, hπ, hw, φ, hφ, hφ0, hsum⟩ := UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued D.host.E (Vc D j).rank D.what₂.Tau (fun τ => T.io.toRingHom.comp (inc τ))
    (places_inj_pz T.io T.half) mu T.sh lam (fun _ _ => rfl) B hB1 hB2 F1 h10 h1l h1i h1e
  have htr : ∀ g y, F1 (g * y) = A (Fm ((Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (jj g * h₀) *
      (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (GlobalTheory.DefTransfer.cj jj h₀ y))) := fun g y => by
    rw [hA, ← map_mul, GlobalTheory.DefTransfer.cj_apply, map_mul jj]
    congr 3
    group
  have hK : ∀ v v', GlobalTheory.Hk3.Good p.R.toRealDat t v' → GlobalTheory.Hk3.hyp (Vc D j) v = GlobalTheory.Hk3.hyp (Vc D j) v' →
      ∀ x ∈ GlobalTheory.DefTransfer.KP (Vc D j).rank v, RU D.host.E (Vc D j).rank x φ = φ := by
    intro v v' hg he x hx
    have h1 := (hTr.2.2.2.2.2.2.1 v x).2 hx
    rw [he] at h1
    have h2 := hfix _ (UpperTheory.levChi_eq_one_of_good_place p j t v' hg _ h1)
    have := hsum Unit Finset.univ (fun _ => x) 1 (fun _ _ => hx.1.1) fun g => by
      rw [Finset.univ_unique, Finset.sum_singleton, one_smul, htr, h2, hA]
    simpa using this
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun _ => rfl, hw τ, ?_⟩, φ, hφ, hφ0, fun v hv x h1 h2 => hK v v hv rfl x ⟨h1, h2⟩, fun Q => ?_⟩
  · rw [emb_cj_pz]
    exact GlobalTheory.DefU.AU.HasWt.conjugate (π := GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) (hw τ)
  have hg : GlobalTheory.Hk3.Good p.R.toRealDat t (plOf p j t Q) :=
    ((GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
      p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2).1
  have hKQ := hK (labOf p j t Q) _ hg (GlobalTheory.SphConj.hyp_conj _ _)
  refine ⟨fun x h1 h2 => hKQ x ⟨h1, h2⟩, fun i hi => ?_⟩
  subst hi
  obtain ⟨r1, r2, -⟩ := (T.ix_range (ix i)).1 ⟨i, rfl⟩
  obtain ⟨hloc, R, hR, hRs⟩ := UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace p j t (ix i).1 (ix i).2 r1 r2
  rw [GlobalTheory.SplitTransfer.heckeVec_divInd hTr hKQ hR]
  refine hsum _ R (fun γ => (GlobalTheory.DefTransfer.cj jj h₀).symm γ) _ (fun γ hγ => ((hTr.2.2.2.2.2.2.2 _ _ R hR).1 γ hγ).1.1) fun g => ?_
  simp only [htr, MulEquiv.apply_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, hRs _ Fm hFr, hA, ← map_smul]
  exact congrArg A (hFh i hloc _)
theorem _root_.GlobalTheory.T.small_place_prime_local_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W hD _ w hw hW _ _ F R inc T mu θ hmu hθ
  obtain ⟨π, h1, h2, φ, h3, h4, h5, h6⟩ := frame_embedding_exists p j (p.R.mu w) hD.Nr F R.e0 R.ix inc T mu θ hmu hθ
  exact ⟨π, h1, h2, fun v hv => ⟨φ, h3, h4, h5 v (UpperTheory.good_place_of_twist_place_dividing p j P W hD w hw hW v hv)⟩, φ, h3, h4, fun Q _ => h6 Q⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLiftsBijectiveBase
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.BigOn.SplitRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem lUnif_of_rows_alt (p : PtAt ex Csz) (h : p.PointConditions') : (R2 p).LUnif := h.prim.unif
theorem split_lifts_bijective_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : ((R2 p).toCx (F2 p)).H5 (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have h5 := hR.lifts0.1
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at h5
  exact h5
theorem rat_theta_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : ((R2 p).toCx (F2 p)).RATth (F2 p).cr false := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hr := hR.ratTh
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hr
  exact hr
theorem level_proviso_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : (lv ((F2 p).fc ((R2 p).toCx (F2 p)).zs) false).Proviso := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  have hv := hR.proviso0
  rw [GlobalTheory.CharRealise.toCx3_eq_one p.R p.F p.phsOne] at hv
  exact hv
theorem base_links_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : BaseLinks (R2 p) (F2 p) :=
  ⟨_root_.GlobalTheory.BigOn.SplitRows.split_lifts_bijective_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.rat_theta_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.level_proviso_of_split_data p h⟩
theorem rank_conditions_of_split_data (p : PtAt ex Csz) (h : p.PointConditions') : RankRows (S2 p) := by
  have hR := complex_data_conditions_base_level_of_primitive_links h.ok h.sep p.charW h.prim
  exact ⟨(indefiniteDataAtBaseLevel hR).D_pos, fun j => (indefiniteDataAtBaseLevel hR).dW_eq (hR.wf false) j⟩
end Point
theorem uniform_and_base_links_and_rank_of_split_data : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.PointConditions' → (R2 p).LUnif ∧ BaseLinks (R2 p) (F2 p) ∧ RankRows (S2 p) :=
  fun _ _ _ _ _ _ _ _ _ _ p h => ⟨_root_.GlobalTheory.BigOn.SplitRows.lUnif_of_rows_alt p h, _root_.GlobalTheory.BigOn.SplitRows.base_links_of_split_data p h, _root_.GlobalTheory.BigOn.SplitRows.rank_conditions_of_split_data p h⟩
end GlobalTheory.BigOn.SplitRows
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StmtJHolds
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section HC
variable {R : Ranks} (P : HCParam R)
end HC
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section JB
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end JB
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section Core
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end Core
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open _root_.Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
theorem stmtJ_holds_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  intro L hA
  obtain ⟨hG2, hCr, hG2g, hDi, hRd, hP⟩ := hA
  have hF : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ := fun j h1 h2 ρ => jFacts_of hP j h1 h2 ρ
  have hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith [hP.1, hP.2.1]
  exact ⟨_root_.GlobalTheory.JumpSets.jumpLemma_a_of_admissible_alt_alt hP hG2 hCr hG2g hDi hRd, jumpSetBound_of_realPlaceFacts hF, jumpSetCloud_of_realPlaceFacts hF, jumpSetDistinct_of_realPlaceFacts hF,
    jumpSetEta_of_realPlaceFacts hF hpar D.R.t_odd.pos L.Sc_pos L.etaSz_pos, jumpSetFinal_of_realPlaceFacts hF, jumpSetGap_of_realPlaceFacts hF⟩
end GlobalTheory.JumpSets
end
end
end

