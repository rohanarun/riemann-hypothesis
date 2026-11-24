module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0397
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0062
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosed
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := _root_.GlobalTheory.SnFamNG.leaves_of_fam _root_.GlobalTheory.SnFam.famNG_holds
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 _root_.GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 _root_.GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude) (he _root_.GlobalTheory.SnFam.existFam)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil
section
open GlobalTheory.SnFam

namespace GlobalTheory.SnFamTop

theorem stepFamG_of_SWXS (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.Pf.MainEqFam.StepFamG :=
  _root_.GlobalTheory.SnFam.Gen.stepFamG_of_fam
    (fun D h => GlobalTheory.localMass_le_genericMass_nine _ _ h)
    _root_.GlobalTheory.HTieLeaf.main _root_.GlobalTheory.SnFamGenAll.famGen _root_.GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW) _root_.GlobalTheory.FamilyNormRational.familyGroupSumFactorsRowWeightAmplitude _root_.GlobalTheory.SnFam.existFam

end GlobalTheory.SnFamTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocalStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  first | exact @GlobalTheory.AmpLift.amp_lift | exact GlobalTheory.AmpLift.amp_lift | (intros; apply GlobalTheory.AmpLift.amp_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiPulledBackUnipotentMeasureEqBesselImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem pi_muNl_eq_dnB_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  intro D X θ C A hθ _hA
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ w rfl
      exact sf_muNl C τ hθ
    intro v
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  obtain ⟨hemb, hmap⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have h := congrArg (fun μ => μ (Formalism.L2.SG.LoopTerm.trInf C '' A)) hmap
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLocalQuotientMassEqMeasureRatio
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitW

open Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.Choice

theorem loc_at {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (v : InfinitePlace X.B.I.F) (hv : vOf X τ = v) :
    SigmaFinite (muNl C τ v) ∧ SigmaFinite (muHl C u τ v) ∧
    QPK.mulMap (muNl C τ v) (muHl C u τ v)
      (QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v))ᶜ = 0 ∧
    ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ v) (muHl C u τ v)) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) = l2SG (C.nuS u τ) (wT C u τ) := by
  subst hv
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  exact ⟨sf_muNl C τ one_pos, sf_muHl C u τ, (invOn_mulMap C u τ).2.2.1, β, hβm, hβ1, loc_id C u τ hβm hβ1⟩

theorem map_trI_H {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) :
    (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map (trI C) = Measure.pi (C.muW u) := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : trI C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  haveI : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ w rfl; exact sf_muHl C u τ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) = fun τ => muHl C u τ (X.pl.symm τ) := by
    funext τ
    show muHl C u (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muHl C u τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = C.muW u τ := fun τ => map_muHl C u τ
  have : ∀ τ, SigmaFinite ((muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (C.muW_haar u τ).1
  refine (Measure.pi_map_pi (μ := fun τ => muHl C u τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]

theorem prod_l2SG_eq : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (cN cH : ℝ≥0∞), cN ≠ 0 → cN ≠ ⊤ → cH ≠ 0 → cH ≠ ⊤ →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = cN * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A)) →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = cH * Measure.pi (C.muW u) (trI C '' A)) →
    ∏ τ, l2SG (C.nuS u τ) (wT C u τ) = cN * cH := by
  intro D X C hB _ u cN cH hN0 hNt hH0 hHt hN hH
  have hv : ∀ v, vOf X (X.pl v) = v := fun v => X.pl.symm_apply_apply v
  have loc := fun v => loc_at C u (X.pl v) v (hv v)
  choose hsN hsH hconc β hβm hβ1 hβl using loc
  set μN : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muNl C (X.pl v) v with hμN
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muHl C u (X.pl v) v with hμH
  haveI : ∀ v, SigmaFinite (μN v) := hsN
  haveI : ∀ v, SigmaFinite (μH v) := hsH
  haveI : SigmaFinite (muNB D 1) := (muNB_haar (D := D) one_pos).1
  haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1
  obtain ⟨hemb0, hmapN⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsN v) one_pos
  have hemb : MeasurableEmbedding (trI C) := hemb0
  have hmapH := map_trI_H C u
  have eN : X.muN u = cN • Measure.pi μN := by
    ext A hA
    have hc : Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) = Measure.pi μN A := by
      rw [← show (Measure.pi μN).map (trI C) = Measure.pi (fun _ : D.what₂.Tau => muNB D 1) from hmapN,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hN A hA, hc, Measure.smul_apply, smul_eq_mul]
  have eH : X.muH u = cH • Measure.pi μH := by
    ext A hA
    have hc : Measure.pi (C.muW u) (trI C '' A) = Measure.pi μH A := by
      rw [← show (Measure.pi μH).map (trI C) = Measure.pi (C.muW u) from hmapH,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hH A hA, hc, Measure.smul_apply, smul_eq_mul]
  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hFdef
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∏ τ, l2SG (C.nuS u τ) (wT C u τ) := by
    rw [hfdef, Formalism.L2.SG.ProjRows.muInf,
      QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    rw [← Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (wT C u (X.pl v))) _ (fun v => rfl)]
    exact Finset.prod_congr rfl fun v _ => hβl v
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) =
      (cN * cH) * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      eN, eH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [QPK.lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (μN v) (μH v)),
          s ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        have hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u v := by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh
        have hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v :=
          Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm)
            (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')
        show β v (m * h * x v) * ‖X.Wloc u v (m * h * x v)‖ₑ ^ 2 = β v (m * h * x v) * ‖X.Wloc u v (x v)‖ₑ ^ 2
        rw [← enorm_norm (X.Wloc u v (m * h * x v)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    have h3 : ∏ v, F v (x v) = ‖X.Wu u x‖ₑ ^ 2 := by
      rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
    rw [h3, smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hin] at key
  have hW1 : ∫⁻ x, ‖X.Wu u x‖ₑ ^ 2 ∂(X.nuQ u) = 1 := (X.Wu_spec u).2.2.2.2
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hNt hHt), hW1, mul_one, hL1] at key
  exact key

end GlobalTheory.UnitW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstMulTransportedProduct
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
  Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem muN_eq_const_mul_pi_trI : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A →
      X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  intro D X C hB hG u
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using
    Formalism.L2.SG.Pf.AmpWinGlob.place_all C u hG.1 hB
  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsfN v) one_pos
  refine ⟨cN, hcN0, hcNt, fun A _ => ?_⟩
  have htr : trI C = Formalism.L2.SG.LoopTerm.trInf C := rfl
  have hcov : Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) A =
      Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
    rw [htr, show Measure.pi (fun _ : D.what₂.Tau => muNB D 1) = Formalism.L2.SG.LoopTerm.dnB D 1 from rfl, ← hmapT,
      hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
section
namespace GlobalTheory

theorem wuDecayOfGap : Formalism.L2.SG.Pf.WuDecayOfGap := CompanionTheory.Lime.BM.wuDecayOfGap_holds'

end GlobalTheory
end

