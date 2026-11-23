module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar


open GlobalTheory.Mem.SymChar.Resid in
theorem resid_at_w : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  intro D X _h _hE hgw kv k hk N hN
  classical
  have hg : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := hgw kv
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  set w := D.naut.plGw kv.1 kv.2 with hwdef
  let S : AddSubgroup (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := (wInt X w).toAddSubgroup
  let mk := QuotientAddGroup.mk' S
  have hmk : ∀ a b, a - b ∈ wInt X w → mk a = mk b := fun a b hab =>
    (QuotientAddGroup.eq_iff_sub_mem).2 hab
  let f0 : ℤ →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    mk.comp (Int.castAddHom (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
  have hf0 : f0 (D.host.g kv.1 : ℤ) = 0 := by
    show mk ((((D.host.g kv.1 : ℕ) : ℤ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) = 0
    rw [Int.cast_natCast]
    exact (QuotientAddGroup.eq_zero_iff _).2 (natCast_g_mem X kv.1 hg)
  let φ : ZMod (D.host.g kv.1) →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    ZMod.lift (D.host.g kv.1) ⟨f0, hf0⟩
  have hφ : ∀ t : ZMod (D.host.g kv.1), φ t = mk ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    intro t
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast]
    rw [ZMod.lift_coe]
    show mk _ = mk _
    congr 1
    simp
  suffices hs : mk (argS X k) = φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) by
    unfold ModW
    rw [hφ] at hs
    exact (QuotientAddGroup.eq_iff_sub_mem).1 hs
  have hsum : φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) =
      ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then wtA D.R.rS D.R.k (side X w) i j • φ (N i j) else 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← zsmul_eq_mul, map_zsmul]
    · exact map_zero φ
  rw [hsum, GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex _ D.R.rS D.R.k D.R.r (rank_eq D) (side X w) (fun i j => φ (N i j))]
  unfold argS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ]
    apply hmk
    have := dual_row X w hN (X.vectorsInLattice.1 a).2 (posE D a) (_root_.GlobalTheory.Mem.SymChar.hA_symVec_sub_ite_mem_wInt D X w kv.1 hg a) (posN D a)
    rw [symVec_posN] at this
    exact this
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hw : SymFrame.EwAt X w
      · have hs : side X w = true := by simp [side, hw]
        rw [if_pos hs, hφ]
        apply hmk
        have h1 := one_sub_ew_mem X kv.1 hg hw
        have := dual_row X w hN (X.vectorsInLattice.2.2 i).2 (posB D i) (_root_.GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec D X w kv.1 hg hw h1 i)
          (posB D ⟨i.1 + 1, hi⟩)
        rw [symVec_posB X w hw] at this
        have e1 : (posB D ⟨i.1 + 1, hi⟩) = ⟨D.R.rS + i.1 + 1, by have := rank_eq D; omega⟩ :=
          Fin.ext (by simp only [posB]; omega)
        rw [e1] at this
        exact this
      · have hs : side X w = false := by simp [side, hw]
        rw [if_neg (by simp [hs])]
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have hew := GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one D X kv hw
        have hbw : X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩ ∈ X.B.I.Lf :=
          Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1
        have hint := Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 i).2 hbw
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) =
            hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) * X.ew := by
          conv_lhs => rw [X.bwd_w i]
          rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, mul_comm]
        show hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) ∈ wInt X w
        rw [e]
        exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hew
    · rw [dite_eq_right hi, dite_eq_right hi, map_zero]

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InstBack
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

-- Construct the records directly at the index used by the transported columns.
abbrev latTrZ (Gy : G.LatInst (w.D Z)) : G.LatInst (w.D (setDivZ Z N h)) := { Gy with }

open DivX (md) in
abbrev divTrZ (X : DivX (w.D Z)) : DivX (w.D (setDivZ Z N h)) :=
  { X with md := fun S κ p _ la z => { md X S κ p la z with } }

def kerTr {t : ColT w Z} {Gy : G.LatInst (w.D Z)} (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) (colTTr w Z N h t).Gt (colTTr w Z N h t).cmp
      (w.tw (setDivZ Z N h)) (latTrZ w Z N h Gy) :=
  fun u v g => { ker u v g with }


set_option maxHeartbeats 4000000 in
def ktTr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker) :
    KerT (colTTr w Z N h t) (divTrZ w Z N h X) (latTrZ w Z N h Gy) (kerTr w Z N h ker) :=
  { kt with
    O := fun u a => { kt.O u a with }
    E := { kt.E with }
    std := { kt.std with }
    ok := ⟨⟨fun u μ v hv => { (kt.ok.1.choose u μ v hv) with }, fun u μ v hv => kt.ok.1.choose_spec u μ v hv⟩, kt.ok.2⟩ }


set_option maxHeartbeats 8000000 in
theorem entC_tr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker)
    (H : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (hh : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs X (w.tw Z)),
      kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs hh) :
    ∃ (Pl : Examples₂.EntPl (w.D (setDivZ Z N h))) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D (setDivZ Z N h)))
      (hh : Formalism.L2.Ker.KerEntHyp Pl (ktTr w Z N h kt).O Bs (divTrZ w Z N h X) (w.tw (setDivZ Z N h))),
      (ktTr w Z N h kt).E = Formalism.L2.Ker.kerEntC Pl (ktTr w Z N h kt).O Bs hh := by
  obtain ⟨Pl, Bs, hh, e⟩ := H
  exact ⟨{ Pl with }, Bs, { hh with },
    congrArg (fun E : Formalism.BasicNotions.KerEnt (w.D Z) X (w.tw Z) =>
      ({ E with } : Formalism.BasicNotions.KerEnt (w.D (setDivZ Z N h))
        (divTrZ w Z N h X) (w.tw (setDivZ Z N h)))) e⟩

end GlobalTheory.Mem.Db.DivTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.JointsTrue

open _root_.Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR


set_option maxHeartbeats 1000000 in
theorem isDetLift_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Theta.AE D) (he : JoinChr.IsPlIdem D e P)
    (k : D.host.Eˣ) (y : Theta.AE D) (hy : Joints.IsRatioAt D e (k : D.host.E) y) (x : Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hx : ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Herm.Af D.host.F) = Joints.finE D y) :
    IsDetLift D.sp.cm x.1 (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
  let φ : Theta.AE D →+* AfE D.host.F D.host.E := Joints.finE D
  have hinc : ∀ a : D.host.E, φ (Theta.incA D a) = a ⊗ₜ[D.host.F] 1 := fun a => rfl
  have hc : ∀ z, φ (Theta.cA D z) = Formalism.UG.sigR D.sp.cm.sig _ (φ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [(Theta.cA D).map_zero, φ.map_zero, RingHom.map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [(Theta.cA D).map_add, φ.map_add, φ.map_add, ha, hb, RingHom.map_add (f := _)]
  have h1 : (finAf D.host.F D.host.E (Neutral.B1.localIdele _ P (Formalism.L2.Host.atFin P k)) : AfE D.host.F D.host.E) = φ (JoinChr.locE D e k) := by
    rw [GlobalTheory.Core.Cls.JointsStd.finAf_localIdele (e := φ e) (by rw [← φ.map_mul, he.1]) (fun a ha => ?_) k, JoinChr.locE, φ.map_add,
      φ.map_mul, φ.map_sub, φ.map_one, hinc]
    rw [he.2.2 a ha, ← hinc, ← φ.map_mul]
    exact not_congr (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _)
  have h2 := congrArg φ hy
  rw [φ.map_mul, hc, ← h1] at h2
  unfold IsDetLift h90
  rw [MonoidHom.div_apply, div_eq_iff_eq_mul]
  exact Units.ext (h2.symm.trans (by rw [Units.val_mul, hx]; rfl))


end GlobalTheory.Mem.JointsTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelDatumLatticeTargetSideTrueChains
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 1000000 in
theorem kerEnt_latT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, (∃ y ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat (i + 1)).L, ((I.tw l l0 Z).fm u μ).emb (i + 1) y = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi φ
  have hL1 := fun x => _root_.GlobalTheory.Mem.Col2.GStep.locW_latOf_iff (I.stp u μ (i + 1)) B.fields.emb (lamT (B.hcW u) (i + 1)) ((l.fmL u μ).fam (i + 1))
    B.places w _ (Pl.iL w) (Pl.iL_int w) x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun c' => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← (((I.tw l l0 Z).fm u μ).emb_basis (i + 1)).2, ← ((((I.tw l l0 Z).fm u μ).lat (i + 1)).b.sum_repr y), map_sum]
        exact Submodule.sum_mem _ fun a _ => by
          rw [LinearMap.map_smulₛₗ]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · obtain ⟨v', hv'⟩ := _root_.GlobalTheory.Mem.KerVal.fm_succ_mem_valQ I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi y c'
      exact ⟨v', hv', (_root_.GlobalTheory.Mem.IntDualT.mem_locW_iff_prTC_le_one I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (y.1 c') v' hv').1
        ((hL1 y).1 hy c')⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨x, rfl⟩ := _root_.GlobalTheory.Mem.Col2.TC.form_of_rat_values I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi φ hF
      (fun c' => (hc c').imp fun _ h => h.1)
    refine ⟨x, (hL1 x).2 fun c' => ?_, rfl⟩
    obtain ⟨v', hv', hn⟩ := hc c'
    exact (_root_.GlobalTheory.Mem.IntDualT.mem_locW_iff_prTC_le_one I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (x.1 c') v' hv').2 hn

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNearStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelElement_at_bad_primes_integral_and_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)) (κ' : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ' = 1 → PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * x * k (chOf c)) ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 → ∀ P : SBof I a, (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((((k (chOf c))⁻¹ * x * k (chOf c) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) (((((k (chOf c))⁻¹ * x * k (chOf c))⁻¹ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ ∀ g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), LiftsInv I κ' P g → GlobalTheory.TwU.NearAt (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((k (chOf c))⁻¹ * x * k (chOf c)) (GlobalTheory.TwU.seamGL (sm I l Z) g) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.ReadBad.main | exact GlobalTheory.Mem.Col2.AdT.ReadBad.main | (intros; apply GlobalTheory.Mem.Col2.AdT.ReadBad.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_group_element_eq_level_component_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LocSplice.main | exact GlobalTheory.Mem.Col2.AdT.LocSplice.main | (intros; apply GlobalTheory.Mem.Col2.AdT.LocSplice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonzeroForcedContentPlacesAgreeOverEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl

theorem resCharW_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) :
    Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl w) = Examples₂.PlacesToy.resCharW w := by
  have hm : ((Examples₂.PlacesToy.resCharW w : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
    have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO K) (Examples₂.PlacesToy.resCharW_mem w)
    rwa [map_natCast] at this
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem FTypeG_of_kapDef {D : D7} (hk : DV.KapDef D) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    FTypeG D j = -(∑ τ : D.what₂.Tau, ((∑ i : Fin (D.R.sigW j).1, |((DV.aPlusQ D j τ i : ℚ) : ℝ)|) +
      ∑ c : Fin (D.R.sigW j).2, |((DV.aMinusQ D j τ c : ℚ) : ℝ)|)) / 2 := by
  unfold FTypeG fockDeg
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hb, hs⟩ := hk j h1 h2 τ
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hb i]
    norm_cast
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [show ((DV.aMinusQ D j τ c : ℚ) : ℝ) = -((D.what₂.kaSmall j τ c : ℚ) : ℝ) by rw [hs c]; push_cast; ring, abs_neg]
    norm_cast

theorem mem_W1F_forced_iff (s : Scale) {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    (v : HeightOneSpectrum (𝓞 B.LL)) :
    v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K s (w.D Z)) ↔
      ∃ j : ℕ, j < B.R.m ∧ FK s (w.D Z) (j + 1) (Examples₂.PlacesToy.resCharW v) ≠ 0 := by
  constructor
  · rintro ⟨j, y, hy, h⟩
    refine ⟨j.1, j.2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h
    · have e : F0K s (w.D Z) (Formalism.DivisionValues.conjPl v) j = FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW v) := by
        show FK s (w.D Z) (j.1 + 1) (Examples₂.PlacesToy.resCharW (Formalism.DivisionValues.conjPl v)) = _
        rw [resCharW_conjPl]
      exact e ▸ h
  · rintro ⟨j, hj, h⟩
    exact ⟨⟨j, hj⟩, v, Or.inl rfl, h⟩

theorem FK_enl (s : Scale) {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (h : B'.toPre = B.toPre)
    (hk : DV.KapDef (w.D Z)) (hk' : DV.KapDef (w'.D Z')) (j p : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ B.R.m) :
    FK s (w.D Z) j p = FK s (w'.D Z') j p := by
  have h2' : j ≤ B'.R.m := by rw [h]; exact h2
  unfold FK
  rw [FTypeG_of_kapDef hk h1 h2, FTypeG_of_kapDef hk' h1 h2']
  clear hk hk'
  cases B'
  subst h
  rfl

theorem resCharW_of_below {B B' : Base} {f : Fr B.toPre} {T : TwDat B} {f' : Fr B'.toPre} {T' : TwDat B'}
    (w : ColW B f T) (w' : ColW B' f' T') (Z : w.Lt) (Z' : w'.Lt) (v : HeightOneSpectrum (𝓞 B.LL))
    (v' : HeightOneSpectrum (𝓞 B'.LL)) (hB : Below (w.D Z) (w'.D Z') v v') :
    Examples₂.PlacesToy.resCharW v' = Examples₂.PlacesToy.resCharW v := by
  have he : (w.D Z).what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w.D Z).what₂.LL) : (w.D Z).what₂.LL) =
      (w'.D Z').what₂.embLL (((Examples₂.PlacesToy.resCharW v : ℕ) : 𝓞 (w'.D Z').what₂.LL) : (w'.D Z').what₂.LL) := by
    simp only [map_natCast]
  have hm := (hB _ _ he).1 (Examples₂.PlacesToy.resCharW_mem v)
  exact Examples₂.PlacesToy.prime_mem_unique _ (Examples₂.PlacesToy.resCharW_prime _) (Examples₂.PlacesToy.resCharW_prime _)
    (Examples₂.PlacesToy.resCharW_mem _) hm

theorem nonzeroForcedContentPlaces_agree_over_enlargement : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B')
    (w' : ColW B' f' T'), Enl B B' → ∀ (Z : w.Lt) (Z' : w'.Lt), DV.KapDef (w.D Z) → DV.KapDef (w'.D Z') →
    ∀ v v', Below (w.D Z) (w'.D Z') v v' →
      (v ∈ R3.placesWithNonzeroContentOrConj (w.D Z) (F0K K.s (w.D Z)) ↔ v' ∈ R3.placesWithNonzeroContentOrConj (w'.D Z') (F0K K.s (w'.D Z'))) := by
  intro K B f T w B' f' T' w' hE Z Z' hk hk' v v' hB
  have hres := resCharW_of_below w w' Z Z' v v' hB
  have hm : B'.R.m = B.R.m := by rw [hE.1]
  refine (mem_W1F_forced_iff K.s w Z v).trans (Iff.trans ?_ (mem_W1F_forced_iff K.s w' Z' v').symm)
  rw [hm, hres]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [FK_enl K.s w w' Z Z' hE.1 hk hk' (j + 1) _ (Nat.succ_pos j) hj]

end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismCongruentNearFrameReadingStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphism_congruent_near_frame_reading : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → CongE P.1 (dep' P) g' g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' := by
  first | exact @GlobalTheory.Mem.Col2.AdT.NearCong.main | exact GlobalTheory.Mem.Col2.AdT.NearCong.main | (intros; apply GlobalTheory.Mem.Col2.AdT.NearCong.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalAutomorphismsNearSameAdelicCongruentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_automorphisms_near_same_adelic_congruent : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.AdTieNear.main | exact GlobalTheory.Mem.Col2.AdT.AdTieNear.main | (intros; apply GlobalTheory.Mem.Col2.AdT.AdTieNear.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInducedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_embedding_at_orbitPosition_eq_induced_alt : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | exact GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced | (intros; apply GlobalTheory.Mem.Top.KerOne.splitPlace_embedding_at_orbitPosition_eq_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLatticeStatement
section
alias GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange :=
  GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv
end

