module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NeatTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0078
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardMiddleLatticesOverGenusLatticeStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_middleLattices_over_genus_lattice : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)), {𝓛 : Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) | (∃ Λ', IsRowLat D F0 Λ' ∧ (Lsub Λ' (lf D F0)).comap (((D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)).restrictScalars (𝓞 D.host.E)) = 𝓛) ∧ 𝓛.comap ((LinearMap.inl D.host.E (D.sp.X 0).V D.host.E).restrictScalars (𝓞 D.host.E)) = M}.ncard = (Tu D u - 1) ^ D.R.f := by
  first | exact @GlobalTheory.LoopC.GluingNum.gluingNum | exact GlobalTheory.LoopC.GluingNum.gluingNum | (intros; apply GlobalTheory.LoopC.GluingNum.gluingNum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EnnrealVolumeRatioStepCancel
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Step

theorem volU_pos (i : ℕ) : 0 < volU i := by
  have : 0 < sphV i := by
    unfold sphV
    exact Finset.prod_pos fun l _ => by have := Real.pi_pos; positivity
  unfold volU
  positivity

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  positivity

theorem rankFac_mul_meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) :
    rankFac E M * meanConst E M = 2 ^ (M * Formalism.HermitianLatticesTheory.fDeg E) := by
  have hv := vInv_pos E
  unfold rankFac meanConst
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  set L := Formalism.HermitianLatticesTheory.lValEta E M
  have h2 : 0 < 2 * v := by positivity
  have key : (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)
      = 2 ^ (M * f) * v ^ (M * f) := by
    rw [← Real.rpow_add h2, ← mul_pow, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hp : 0 < v ^ (M * f) := by positivity
  calc (2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * L * ((2 * v) ^ ((f : ℝ) / 2) * (v ^ (M * f))⁻¹ / L)
      = ((2 * v) ^ ((f : ℝ) * ((M : ℝ) - 1 / 2)) * (2 * v) ^ ((f : ℝ) / 2)) * (v ^ (M * f))⁻¹ := by
        field_simp
    _ = 2 ^ (M * f) := by rw [key]; field_simp

theorem meanConst_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < meanConst E M := by
  have hv := vInv_pos E
  unfold meanConst
  positivity

theorem rankFac_pos (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ)
    (hL : 0 < Formalism.HermitianLatticesTheory.lValEta E M) : 0 < rankFac E M := by
  have hv := vInv_pos E
  unfold rankFac
  positivity

theorem ennreal_volume_ratio_step_cancel (X Y : ENNReal) (m d t r a b ρ : ℝ) (hm : 0 < m) (hd : 0 < d) (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (ht : r * m = t) (hρ : ρ * a = r * b)
    (h : X * ENNReal.ofReal (m * d) = Y * ENNReal.ofReal (t * d)) :
    X / ENNReal.ofReal a = Y / ENNReal.ofReal b * ENNReal.ofReal ρ := by
  have hmd : 0 < m * d := mul_pos hm hd
  have h1 : X = Y * ENNReal.ofReal r := by
    have e : t * d = r * (m * d) := by rw [← ht]; ring
    rw [e, ENNReal.ofReal_mul hr.le, ← mul_assoc] at h
    exact (ENNReal.mul_left_inj (ENNReal.ofReal_pos.2 hmd).ne' ENNReal.ofReal_ne_top).1 h
  have e2 : ρ = b * (r / a) := by field_simp; linarith
  rw [h1, e2, ENNReal.ofReal_mul hb.le, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_div_of_pos ha, mul_div_assoc]

theorem volumeStep_of_siegelMean : SiegelMean → VolumeStep := by
  intro hS I P Q hPQ hn s hs
  obtain ⟨I', e, x, A, xf, hperp, hsig⟩ := _root_.GlobalTheory.PerpInst.exists_isPerpInst I P Q hPQ hn s hs
  refine ⟨I', e, x, A, hperp.1, hperp.2.1, hperp.2.2.1, hperp.2.2.2.1, hperp.2.2.2.2.1, hsig, ?_⟩
  intro c μf _ _ c' μf' _ _ hc hc'
  obtain ⟨fund, hfund⟩ := _root_.GlobalTheory.FundExists.exists_isFundDom I μf
  have hU := _root_.GlobalTheory.StabUnfold.gaugeUnfold I I' e s x A xf hn hperp c μf c' μf' fund hc hc' hfund
  obtain ⟨-, hM⟩ := hS I hn s μf fund hfund
  have hcov := (_root_.GlobalTheory.CovolRat.covol_eq_inter_fund I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)).1
  rw [Set.univ_inter] at hcov
  have hf : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := (_root_.GlobalTheory.FlagMeas.instance_numbers I).1
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta I.E I.n := by
    have := (_root_.GlobalTheory.FlagMeas.LProd.neg_log_prod_le I.E I.cm.cmUnram (I.n - 1) I.n (by omega)).2
    have hI : Finset.Ioc (I.n - 1) I.n = {I.n} := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    rwa [hI, Finset.prod_singleton] at this
  have hd : 0 < ∏ v, gaussDens (I.ε v) (sgn ℝ s) := by
    refine Finset.prod_pos fun v _ => (_root_.GlobalTheory.GaussMean.Density.gaussDens_spec I.n (I.ε v)).2.2 s ?_
    obtain ⟨hp, hq⟩ := hPQ v
    cases s
    · have : 0 < I.qAt v := by
        have h1 : 1 ≤ Q := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
    · have : 0 < I.pAt v := by
        have h1 : 1 ≤ P := by simpa using hs
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.1 this
      exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  have hR := _root_.GlobalTheory.FlagMeas.mass_ratio_mul_unitary_volume I.E I.n (by omega)
  have hn' : I.n - 1 = I'.n := by have := hperp.2.1; omega
  rw [hf, hn'] at hR
  have hrm := rankFac_mul_meanConst I.E I.n hL
  rw [hf] at hrm
  refine ennreal_volume_ratio_step_cancel _ _ _ _ _ _ _ _ _ (meanConst_pos I.E I.n hL) hd (rankFac_pos I.E I.n hL)
    (pow_pos (volU_pos _) _) (pow_pos (volU_pos _) _) hrm hR ?_
  rw [← hU, hM, gaugeVol, hcov]
  simp only [div_eq_mul_inv]
  ring

end GlobalTheory.GaussMean.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.FinitenessBundle

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  simp only [Gflag, star_sub, star_mul', star_star, star_natCast]
  ring

theorem finX_of_decay : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X),
    Formalism.L2.SG.WuDecay.WuDecay X → Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → FinX Y := by
  intro hR D X Y hW hI
  refine Formalism.L2.SG.Pf.finX_of_neat Y (fun u => Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) (fun u => ?_)
    (GlobalTheory.RowsFiniteDim.finiteDimensional_HHX hR D X hI) (fun u u' t => Formalism.L2.SG.Pf.FinXP.fibFin_holds D X Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' => Formalism.L2.SG.Pf.FinXP.pairIndep_of Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds D X Y u u' s₁ s₂ s₁' s₂')
    (fun u u' t => ?_) Formalism.L2.SG.Closed.VolPosC_holds
  · have hL : X.LevelSubgroupNormalized := Formalism.L2.SG.Closed.level_subgroup_properties X
    exact Formalism.L2.SG.Closed.InHHC_holds D X Y u hI (Formalism.L2.SG.Closed.FoldOKC_holds Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds D X Y u hL hW)
  · rw [← NumberField.IsCMField.complexConj_eq_self_iff]
    exact star_Gflag _ _ _ _

end GlobalTheory.FinitenessBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletions
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMass.GlueLoc

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

variable {D : D7} (Z : LocDat D)

def locSp : Formalism.L2.SG.CntLocal.LocSp D Z.M where
  V := Vp D
  H := locH Z
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p := baseChangeAt_form Z.M p (Z.hcj p)

theorem eq_of_latP {A B : LV D} (hA : A.FG) (hB : B.FG) (h : ∀ p, lattice₂ D Z.M p A = lattice₂ D Z.M p B) : A = B := by
  apply eq_of_locP
  intro P
  exact (locEqC_holds D Z (P.under (𝓞 D.host.F)) A B hA hB).1 (h _) P rfl

theorem mem_of_bcP {Λ : LV D} (hΛ : Λ.FG) {x : (VS D).V} (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ := by
  have e : Λ ⊔ Submodule.span (𝓞 D.host.E) {x} = Λ := by
    refine eq_of_latP Z (hΛ.sup (Submodule.fg_span_singleton x)) hΛ fun p => ?_
    rw [BBTie.latP_sup, BBTie.latP_span, sup_eq_left, Submodule.span_le]
    rintro _ ⟨y, rfl, rfl⟩
    exact h p
  rw [← e]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem mem_dual_iff (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem unimod_of_loc {Λ : LV D} (hΛ : Λ.FG) (hloc : ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  have hf : ∀ p x y, (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  ext x
  rw [mem_dual_iff]
  constructor
  · intro h
    refine mem_of_bcP Z hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    change LocFacts₂ Z.M p (baseChange₂ D p x) w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      change (locH Z p).h _ _ ∈ _
      rw [hf]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h y hy)
      rw [← ho]
      exact BBTie.bt_iota_int Z p o
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Z.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Z p _ o.2) hw
  · intro hx y hy
    refine DualityBasisChange.locGlobIntE D _ fun p => ?_
    rw [← hf, ← (Z.agree p).2.2.2.1]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (Submodule.subset_span ⟨x, hx, rfl⟩) (baseChange₂ D p y)
      (Submodule.subset_span ⟨y, hy, rfl⟩)

variable (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {T T' : D.host.E}
  (G : LFlag (D.sp.Y 0) D.R.rS T) (G' : LFlag (D.sp.Y 0) D.R.rS T')

theorem mmfam_eq (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    (locH Z p).MMfam (tm FP G G' p Λ) = DualityBasisChange.locFam (locSp Z) Z.δ p G.fl G' := by
  funext b
  unfold Loc.HermSp.MMfam
  cases hs : (Z.M p).split with
  | none =>
    rw [DualityBasisChange.locFam_none (locSp Z) p G.fl G' hs]
    rcases b with a | a <;> rfl
  | some g =>
    rcases b with a | a
    · rw [DualityBasisChange.locFam_some_inl (locSp Z) p G.fl G' hs]; rfl
    · rw [DualityBasisChange.locFam_some_inr (locSp Z) p G.fl G' hs]; rfl

theorem span_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      lattice₂ D Z.M p (MMof D G.fl G') := by
  rw [mmfam_eq]
  exact DualityBasisChange.span_locFam Z.agree (locSp Z) p G.fl G'

theorem mmof_latIn : IsLatIn (UPair D G.fl G') (MMof D G.fl G') := by
  rw [R3.MMof_eq]; exact R3.BB_latIn D G.fl G'

theorem spanE_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UPair D G.fl G' : Set (VS D).V)) := by
  rw [← BBTie.bt_spanEp_spanO Z p, span_mmfam, lattice₂, BBTie.bt_spanEp_spanO Z p, ← (mmof_latIn G G').2,
    BBTie.bt_spanEp_spanE]

theorem glue_iff_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  intro D Z FP u u' G G' _ Λ
  constructor
  · rintro ⟨hL, hU, hM⟩
    refine ⟨hL, fun p => ?_⟩
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ :=
      BBTie.latP_mono Z p (hM ▸ inf_le_left)
    refine ⟨BBTie.bt_selfDual Z (locUnimodC_holds D Z) p Λ hL hU, fun i => hle ?_, ?_⟩
    · rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ)]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
        (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not]
      exact congrArg _ hM
  · rintro ⟨hL, h⟩
    refine ⟨hL, unimod_of_loc Z hL.fg fun p => (h p).1, ?_⟩
    refine eq_of_latP Z (Submodule.FG.of_le hL.fg inf_le_left) (mmof_latIn G G').1 fun p => ?_
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ := by
      rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ), Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (h p).2.1 i
    have h3 := (h p).2.2
    rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
      (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not] at h3
    exact h3

end GlobalTheory.GenMass.GlueLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatio
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas.Bound


open scoped ComplexOrder in
theorem zetaE_nonneg (E : Type) [Field E] [NumberField E] (l : ℕ) : 0 ≤ zetaE E l := by
  unfold zetaE dedekindZeta LSeries
  have h : (0 : ℂ) ≤ ∑' n : ℕ, LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) ((l : ℝ) : ℂ) n :=
    tsum_nonneg fun n => LSeries.term_nonneg (by exact Nat.cast_nonneg _) _
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

theorem vInv_nonneg (E : Type) [Field E] [NumberField E] : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  positivity

theorem volU_nonneg (i : ℕ) : 0 ≤ volU i := by
  unfold volU sphV
  positivity

theorem cIw_nonneg (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 ≤ cIw p q j := by
  unfold cIw
  have h := volU_nonneg
  refine div_nonneg (mul_nonneg (by positivity) (mul_nonneg (h _) (h _)))
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (h _) (by positivity)) (h _)) (h _))

theorem div_le_of_scaled {C K x m T V J : ENNReal} {R : ℝ} (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hK0 : K ≠ 0) (hK : K ≠ ⊤)
    (hm0 : m ≠ 0) (hm : m ≠ ⊤) (h1 : C * x / K ≤ T * V * J) (h2 : C * m / K = V * ENNReal.ofReal R) :
    0 < R ∧ x / m ≤ T / ENNReal.ofReal R * J := by
  have hD0 : C / K ≠ 0 := (ENNReal.div_pos hC0 hK).ne'
  have hD : C / K ≠ ⊤ := ENNReal.div_ne_top hC hK0
  have e1 : ∀ y, C * y / K = C / K * y := fun y => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [e1] at h1 h2
  have hp0 : V * ENNReal.ofReal R ≠ 0 := h2 ▸ mul_ne_zero hD0 hm0
  have hp : V * ENNReal.ofReal R ≠ ⊤ := h2 ▸ ENNReal.mul_ne_top hD hm
  have hV0 : V ≠ 0 := left_ne_zero_of_mul hp0
  have hR0 : ENNReal.ofReal R ≠ 0 := right_ne_zero_of_mul hp0
  have hV : V ≠ ⊤ := fun h => hp (by rw [h, ENNReal.top_mul hR0])
  refine ⟨by simpa using hR0, ?_⟩
  calc x / m = (C / K * x) / (C / K * m) := (ENNReal.mul_div_mul_left _ _ hD0 hD).symm
    _ ≤ (T * V * J) / (V * ENNReal.ofReal R) := by rw [h2]; gcongr
    _ = (V * (T * J)) / (V * ENNReal.ofReal R) := by ring_nf
    _ = T * J / ENNReal.ofReal R := ENNReal.mul_div_mul_left _ _ hV0 hV
    _ = T / ENNReal.ofReal R * J := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

theorem flagMeasureBound : VolumeStep → FlagMeasureBound := by
  intro hstep I μf _ _ fund hfund p q hsig hn a j ha hj hjq B hB hBs
  obtain ⟨hf, -, -, -, -, hpq⟩ := _root_.GlobalTheory.FlagMeas.instance_numbers I
  have hpq := hpq p q hsig
  obtain ⟨hmeas, hinv, -⟩ := _root_.GlobalTheory.FlagMeas.typeSet_measurable_invariant I a j B hB
  obtain ⟨hpos, hfin⟩ := _root_.GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top hstep I μf fund hfund p q hsig (by omega)
  refine ⟨hmeas, hpos, hfin, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := _root_.GlobalTheory.FlagMeas.VolRatio.volumeRatio_of_volumeStep hstep I p q (p - ∑ i, j i) (q - ∑ i, j i) hsig
    (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega)
  obtain ⟨t₀, lc₀, sc₀, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hKc, hKo, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  choose c hc0 hc _ using fun v => _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique I.n (I.ε v)
  choose c₀ _ hc₀ _ using fun v => _root_.GlobalTheory.GaugeConst.gauge_exists_pos_unique I₀.n (I₀.ε v)
  let μ₀ : Measure I₀.Gf := Measure.haar
  have hU := _root_.GlobalTheory.FlagUnfold.unfoldBound I I₀ p q a j ha hj hjq (by omega) hsame hsig hsig₀ c μf c₀ μ₀ hc hc₀ B hB hBs
  have hR := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hc hc₀
  rw [(_root_.GlobalTheory.CovolRat.covol_eq_inter_fund I μf fund _ hfund hmeas hinv).1] at hU
  have hR' : ENNReal.ofReal (∏ v, c v) * I.muA μf fund / μf I.Kset = gaugeVol I₀ c₀ μ₀ *
      ENNReal.ofReal (∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac I.E M) := by
    have e : p - ∑ i, j i + (q - ∑ i, j i) = p + q - 2 * ∑ i, j i := by omega
    rw [← e, ← hR, gaugeVol,
      (_root_.GlobalTheory.CovolRat.covol_eq_inter_fund I μf fund Set.univ hfund MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)).1,
      Set.univ_inter]
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, by rw [← hKs]; exact Ks.one_mem⟩).ne'
  have hK : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  have hC0 : ENNReal.ofReal (∏ v, c v) ≠ 0 := by
    simpa using Finset.prod_pos fun v _ => hc0 v
  obtain ⟨hRpos, hle⟩ := div_le_of_scaled hC0 ENNReal.ofReal_ne_top hK0 hK hpos.ne' hfin.ne hU hR'
  refine hle.trans (le_of_eq ?_)
  congr 1
  have hv := vInv_nonneg I.E
  have hres := (dedekindZeta_residue_pos I.E).le
  rw [← _root_.GlobalTheory.FiveFactors.prod_five_factors I.E I.cm.cmUnram p q a j hjq (by omega), ENNReal.ofReal_div_of_pos hRpos, hf, hpq,
    ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (cIw_nonneg p q j) _) (by positivity)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun l _ => zetaE_nonneg I.E l)))]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [_root_.GlobalTheory.FlagMeas.genLinVolume I.E I.cm.cmUnram.1 (j i) (hj i), hf]
  exact (ENNReal.ofReal_mul (by positivity)).symm

end GlobalTheory.FlagMeas.Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRows
section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.NGClass

theorem vec_eq_zero_of_oo {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word} (t : TauC Y u u')
    (h : OOt t = 0) : (Y.tO u u').vec t = 0 := by
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec ampN
  rw [h]
  simp
  rfl

theorem ngClass_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, clsOf Y u u' t = clsOf Y u u' t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') ∧ ∀ t : TauC Y u u', (Y.tO u u').vec t ≠ 0 → t.relevant := by
  intro D X Y u u' hT
  refine ⟨fun t ht => ?_, fun t ht t' ht' heq => ?_, fun t hv => ?_⟩
  · intro h0
    apply ht.1
    show Formalism.L2.SG.TermOp.Gt t = 0
    unfold Formalism.L2.SG.TermOp.Gt
    rw [if_pos h0]
  · obtain ⟨hR, -, -⟩ := Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds D X Y u u' hT
    have hm : t' ∈ clsOf Y u u' t' := ⟨ht', rfl, hR t' ht'⟩
    rw [← heq] at hm
    exact hm.2.1.symm
  · by_contra hr
    exact hv (vec_eq_zero_of_oo Y t
      (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
        Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
        Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
        Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr))

end GlobalTheory.NGClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalMassIntegralLatticesBoundedDetLineStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totalMass_integralLattices_bounded_det_line : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ (V₁ : Type) [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁] (h₁ : V₁ →ₗ⋆[K] V₁ →ₗ[K] K) (I₁ : Submodule (𝓞 K) V₁), h₁.IsSymm → IsOrthoLattice h₁ I₁ 1 → ∀ X : ℕ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 (X ^ 2), orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h₁ I₁ * (X : ℝ) ^ (2 + Real.logb 2 (fDeg K))) := by
  first | exact @GlobalTheory.Mass.LineMass.main | exact GlobalTheory.Mass.LineMass.main | (intros; apply GlobalTheory.Mass.LineMass.main <;> assumption)
end

