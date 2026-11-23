module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0539
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0212
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0092
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0111
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0195
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0215
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.FrobDualOfTripleAttN
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1811
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0144
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0101
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0214

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedTopDatum
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.TopDatumTheta
open GlobalTheory.LocMod.StepVec
open GlobalTheory.FunObj.Comparison₂ (IsRed)
section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end Gen
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {v : VCom f.c}
theorem k_add_s_succ_eq_r (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega
def ReducesModIdeal (G : GLoc v) (w : Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (kP w)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r),
    a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
      Ideal.Quotient.mk w.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1
theorem reducesModIdeal_iff_maxM_sub {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (kP w)) (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) = M.map (resS D.host.F w)) :
    _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E), Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this
theorem chS_eq_chrStep_fst (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) : (_root_.GlobalTheory.BaseChain.com_z W).chS j = (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 := by
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hPk.bot.hyp.2.2.2.1.lev
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have e : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 = (_root_.GlobalTheory.Fam.pk_z W).mu0 := funext fun i => by
    change (_root_.GlobalTheory.Fam.pk_z W).mu0 i * (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = _
    rw [hb, mul_one]
  change (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta j).1 = _
  rw [e]
theorem locF_iter_alt {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {j a b : ℕ}
    (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t) (hr : D.R.r ≤ a)
    {ea : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin a} {eb : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b}
    (oa : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea) (ob : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb) (χ : ℕ → (kP w)ˣ →* ℂˣ)
    (hχ : ∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)
      (χ (c + 1)) (G.S.μ (c + 1))) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)} (hN : IsIntM N) :
    locF D.R.t j hr (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (fun y => G.S.P.lam y) χ (redM w N) =
      G.S.P.iterPhi (Fin D.R.t) G.S.μ G.S.tame j ((N.map π').submatrix eb ea) := by
  rw [redM_eq_map _ hN]
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) ea eb
    (isIx_of_isOrd _ ha oa) (isIx_of_isOrd _ hb ob) hr G.S.P G.S.μ G.S.tame χ hχ (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (_root_.GlobalTheory.TopDatumTheta.reducesModIdeal_iff_maxM_sub G hπ hred)
    (Matrix.of fun i j => (⟨N i j, hN i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)))
theorem chi_compat_of_mu_eq (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (G : GLoc v) (w : (_root_.GlobalTheory.Fam.pk_z W).Pg) (hq : Formalism.L2.NTheta.IsIdemAt G.q.e w.1) {π' : Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ D.R.m)
    (hμ : (ofSplit G.q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta c).1⁻¹ (G.S.μ c)) :
    GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi c w.1) (G.S.μ c) :=
  GlobalTheory.ChainOnto.chi_compat_of_isComp D _ G.q w.1 hq π' hπ hred (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.com_is_alt W hPk) w.2 c h1 h2 _
    (G.S.tame _) (by rw [_root_.GlobalTheory.TopDatumTheta.chS_eq_chrStep_fst hPk]; exact hμ)
set_option maxHeartbeats 1000000 in
theorem place_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (i : Fin n) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') {N : Matrix (Fin D.sp.X'.rank) (Fin (Yc D (j + 1)).rank) (Datum.EAf D)}
    (hN : N = frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) :
    (((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) ≠ 0 →
      ∀ a b, toEAf D (G i).q.e * N a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
    (IsIntM N → locF D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G i) (pl i).1) (fun y => (G i).S.P.lam y) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (redM (pl i).1 N) = ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x)) := by
  obtain rfl : (G i).s = j := _root_.GlobalTheory.TopLocData.s_eq_alt (G i) h
  have hq := (hGR.idem i).1
  obtain ⟨π', hπ, hred, hint, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D _ (G i).q (pl i).1 hq
  obtain ⟨ea, ha, mS⟩ := hGR.frame i ((G i).s + 1) 0 rfl
  obtain ⟨eb, hb, mT⟩ := hGR.frameTop i
  have hco := coords_moved (ofSplit (G i).q) ((G i).FY ((G i).s + 1) 0 rfl) (G i).FT hπ
    (typeFrame (G i).S.ϖ (stdOrd _ _ ((G i).s + 1) 0 rfl)) (LatFrame.refl _ _) ea eb mS
    (by rw [show (LatFrame.refl (G i).k _).bas.val = 1 from rfl, Matrix.mul_one]; exact mT) x
  have hP : ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) =
      (G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1) ((N.map π').submatrix eb ea) := by
    rw [hN]
    exact congrArg ((G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1)) hco
  rw [hP]
  refine ⟨fun hz a b => part_int (G i).q hπ hint ?_, fun hI => ?_⟩
  · simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hz ((ixSucc _ _ ((G i).s + 1)).symm (eb.symm a)) (ea.symm b)
  · have r1 : (Yc D ((G i).s + 1)).rank = D.R.r + ((G i).s + 1) * D.R.t := by
      rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (by omega)]; rfl
    have r2 : D.sp.X'.rank = D.R.r + ((G i).s + 1 + 1) * D.R.t := by
      rw [D.sp.X'_rank, (G i).hs]; rfl
    have hs := (G i).hs
    exact _root_.GlobalTheory.TopDatumTheta.locF_iter_alt (G i) hπ hred r1 r2 _ ha hb (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc => _root_.GlobalTheory.TopDatumTheta.chi_compat_of_mu_eq hPk (G i) (pl i) hq hπ hred (by omega) (by omega) (hGR.mu i (c + 1) (by omega) (by omega))) hI
set_option maxHeartbeats 1000000 in
theorem datum_eq_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') :
    (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x) ∧
        IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) then
      omegaG (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1 + 1))
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))) *
        omegaQ ∅ (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)))
      else 0) =
    if IsHalf (∑ i, (G i).q.e) x then
      ∏ i, ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) else 0 := by
  obtain ⟨G', rfl⟩ : ∃ G' : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v, G = fun i => G' (pl i) :=
    ⟨fun w => G (pl.symm w), funext fun i => congrArg G (pl.symm_apply_apply i).symm⟩
  have hpl := fun i => _root_.GlobalTheory.TopDatumTheta.place_alt hPk hGR i h x rfl
  by_cases hx : IsHalf (∑ i, (G' (pl i)).q.e) x
  swap
  · rw [if_neg hx, if_neg fun H => hx ((isHalf_actO_iff _ _ _).1 H.1)]
  have hy := (isHalf_actO_iff (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x).2 hx
  rw [if_pos hx]
  by_cases hI : IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))
  · rw [if_pos ⟨hy, hI⟩, GlobalTheory.FunObj.Comparison₂.omegaQ_eq_prod, Finset.prod_empty, mul_one,
      omegaG_eq_prod (r_le_Y (j + 1)) _ _ _ _ _ (fun w => _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1) (fun w y => (G' w).S.P.lam y)
        (fun g => (hGR.lev g).1.trans (pl.forall_congr_right (q := fun w => ∃ y, _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1 y (g w))))
        (fun g y hy => ((hGR.lev g.1).2 g.2 (fun i => y (pl i)) fun i => hy (pl i)).trans
          (Equiv.prod_comp pl fun w => (G' w).S.P.lam (y w))), ← Equiv.prod_comp pl]
    exact Finset.prod_congr rfl fun i _ => (hpl i).2 hI
  · rw [if_neg fun H => hI H.2]
    refine (Finset.prod_eq_zero_iff.2 (by_contra fun hne => hI fun a b => ?_)).symm
    have h1 : (∑ i, (G' (pl i)).q.e) • actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x = actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x :=
      Matrix.ext fun r s => hy r s
    rw [← h1, frMapO_smul]
    exact sum_part_mem _ _ _ _ fun i => (hpl i).1 (fun h0 => hne ⟨i, Finset.mem_univ _, h0⟩) a b
theorem exists_isWeilDatumO_omT_at_last (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    rintro n rfl
    exact W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
set_option maxHeartbeats 1000000 in
theorem moved_top_datum_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hGP : GPin G), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (hψ : IsStdChar D f.c.ψ (-1)) d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) → IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX → ∀ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT), (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M P) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∃ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT i).q.e) (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) (prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT)) F ∧ IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk _ v hv hVT n G pl hGP hGR j h hψ _ _ hΛ hΛX M hM hLT hMv
  refine ⟨1, one_ne_zero, fun d hd => ?_⟩
  obtain ⟨hvac, e, he, hθ⟩ := hd.2
  obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.TopDatumTheta.exists_isWeilDatumO_omT_at_last W j h
  have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hGR.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT hΛ hM hΛX hLT
    _ hb _ hb' (hMv _) (hVT.movesT _) e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    hvac.2.theta hcth hθ
  subst hee
  refine ⟨_, ?_, hWe.om_pres _ _ hcth, (one_smul _ _).symm⟩
  have hfun : prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT) = _ := funext fun x => (_root_.GlobalTheory.TopDatumTheta.datum_eq_alt hPk hGR h x).symm
  rw [hfun]
  exact hmove
end GlobalTheory.TopDatumTheta
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedDataSAssemble
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
open _root_.Formalism.L2 in
set_option maxHeartbeats 1000000 in
theorem tiedDataS_assemble_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : _root_.Formalism.L2.NTiedAllAlt D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : _root_.Formalism.L2.TiedDataSAlt ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, _root_.Formalism.L2.NTiedAllAlt D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
set_option maxHeartbeats 2000000 in
theorem WPt.exists_pinned_spectral_data_compatible : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : _root_.Formalism.L2.TiedDataSAlt q.O.ex, _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_core_parameters_agree hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core_data_of_point.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core_data_of_point.a.host.fr.ι q.w.δ.M' := by
    generalize q.core_data_of_point.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core_data_of_point.a.host.fr.j x := by
    rw [h1]
    exact q.core_data_of_point.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    _root_.GlobalTheory.Mem.Top.Bl.tiedDataS_assemble_alt q.O.ex q.core_data_of_point.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core_data_of_point.a.chrN q.core_data_of_point.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, _root_.Formalism.L2.NTiedAllAlt (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩
end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TripleAttOfIsTriple
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
end Triple
theorem triple_att_n_of_is_triple {D : D7} {T : WDTie D.nd D.naut} {C₀ : CharFrame D} (S : CharSide D C₀) (hF : FrobDense D)
    (hG : _root_.UpperTheory.GalS.GalHodgeN D T) (h : _root_.GlobalTheory.Triple.IsGaloisTriple D) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (s : D.ntw.Sig i) :
    _root_.GlobalTheory.TripleGal.TripleAttN D.naut (bk0 D) i s := by
  obtain ⟨C, art, h⟩ := h
  obtain ⟨ρ, h1, σ, π, r, ν, w, red, h2⟩ := h.triple hi s
  exact _root_.GlobalTheory.TripleLocal.triple_att_n_of_is_triple_with hF hG h.artin h1 h2 S
end GlobalTheory.TripleLocal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwGe
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem twGe_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.TwistLowerBound := by
  intro h1 h2 h3 h4 hA hC
  have h4' := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS h4
  have hD := _root_.GlobalTheory.T.realization_embedding_compatible_alt
  have hR := _root_.GlobalTheory.T.adForm_eq_levelTrace_singleSeries h1 h2 h3 h4'
  have hG := _root_.GlobalTheory.T.twisted_embedding_compatibility_rows_alt h1 h2 h3 h4' hA hC
  have hS := _root_.GlobalTheory.T.schroedinger_ext_zero_product_vacuum_alt
  unfold _root_.GlobalTheory.BigOn.Exp.TwistLowerBound
  unfold _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hD hG hS ⊢
  unfold _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at hR
  refine (((hD.and hR).and hG).and hS).imp fun Fm CH _ H => ?_
  obtain ⟨x0, hx0⟩ := ((H.1.1.1.and H.1.1.2).and H.1.2).and H.2
  refine ⟨x0, fun x hx h0 i p hp hM w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨k1, k2⟩, k3⟩, k4⟩ := hx0 x hx h0 i p hp
  have d := k1 hM w hw j ρ hρ ν rd hfit hcan
  have r := k2 hM w hw j
  have g := k3 hM w hw j ρ hρ ν rd hfit hcan
  have s := k4 hM w hw j ρ hρ ν rd hfit hcan
  obtain ⟨-, e, he1, he2⟩ := hfit.1
  unfold twLat
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, h, w', a, κ, N, hN, hκ, hhw, ha⟩ := g e he1 he2 z hz
  choose y hy hyv using fun k => r (h k) (hhw k).1 (w' k) (hhw k).2
  obtain ⟨b, hb⟩ := s e he1 he2 z n a y κ N hy hN hκ (ha y hyv)
  rw [d e he1 he2 z n (fun k => b * a k) y hy hb]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y k,
    Submodule.subset_span ⟨h k, (hhw k).1, w' k, (hhw k).2, fun v => ?_⟩, rfl⟩)
  rw [one_smul]
  exact hyv k v
end GlobalTheory.BigOn.Exp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.GalN (Ab)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalS
section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]
def NiceAlt (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ ∃ rc : IrrGL (k := w.adicCompletion E) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc ∧ NcW (rc (algNorm σ))
structure LocalConditionsAbovePrime (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  deRham : _root_.UpperTheory.GalS.NiceAlt π h → IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)
  jumps : _root_.UpperTheory.GalS.NiceAlt π h → ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
structure IsGalUAlt (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ → Aw (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), _root_.UpperTheory.GalS.LocalConditionsAbovePrime π ι r HT P h Bw hj
def PairUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT
def CuspUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT
def CarUAlt : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      _root_.UpperTheory.GalS.IsGalUAlt π (quadChar E ^ a) ι r wt HT ∧
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc → NcW (rc (algNorm σ)) →
        Ab (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))
theorem CuspUAlt.of_isCsd (H : _root_.UpperTheory.GalS.CuspUAlt) {E : Type} (Ω : Type) [Field E]
    [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      _root_.UpperTheory.GalS.IsGalUAlt π (quadChar E ^ a) ι r wt HT :=
  H E Ω l ι a ha π _ hr (isPolarized_of_isCsd hc)
theorem IsGalUAlt.aw {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
    {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
    (H : _root_.UpperTheory.GalS.IsGalUAlt π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (hrc : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    Aw (wdOf h hl ι r) ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2)) :=
  _root_.GlobalTheory.GalOfCusp.rec_algNorm_alt hrc σ ▸ H.away w hl A h rc hrc σ hσ
theorem mergeP'_alt (_ : GlobalTheory.Published.AutomorphicFormsFiniteGL) (_ : _root_.UpperTheory.Zero.LLC.RecTExists) (_ : _root_.UpperTheory.GalS.CuspUAlt) (h : _root_.UpperTheory.GalS.CarUAlt)
    (_ : GlobalTheory.Published.RegularAlgebraicPurity) : _root_.UpperTheory.GalS.CarUAlt := h
end UpperTheory.GalS
end
end
end

