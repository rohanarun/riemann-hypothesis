module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0068
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0070
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositiveStatement
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticGenericBound_of_choiceStep_positive : TieOfCtx → StepChoiceConstantsC → StepAnalyticCGP → StepAnalyticGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticGP_of | exact GlobalTheory.SnPos.stepAnalyticGP_of | (intros; apply GlobalTheory.SnPos.stepAnalyticGP_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Chi2ApplyOne
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.BundleTie

variable {D : D7} (X : HidaSetting D)

theorem chi2_apply_one : X.chi2 1 = 1 := by

  obtain ⟨h1, -, -, hmul, hnorm⟩ := Formalism.L2.SG.Pf.level_subgroup_character_unitary X
  have hsq := hmul 1 h1 1 h1
  rw [mul_one (1 : X.B.I.Gf)] at hsq
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact hsq.symm)

theorem e_one : X.B.e 1 = 1 / (X.volK2 : ℂ) := by
  have h1 : (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := (Formalism.L2.SG.Pf.level_subgroup_character_unitary X).1
  rw [X.e_eq 1, if_pos h1]
  have hc : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd 1 = 1 := chi2_apply_one X
  rw [hc, star_one]
  rfl


open _root_.Formalism _root_.Formalism.L2 Formalism.L2.SG in
theorem dstarD_eq
    (hI : (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1))
    (hV : (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) :
    Formalism.MainNotions.StandardLattice.DstarD D =
      X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e := by
  have hre : (X.B.e 1).re = 1 / X.volK2 := by
    rw [e_one X, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hd : (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) = ∏ v, X.dv v := rfl
  have hsub : X.K2 ⊆ X.B.I.Kset := fun x hx => hx.1
  have hv2 : X.volK2 = (X.B.μf X.K2).toReal := rfl
  show Formalism.MainNotions.StandardLattice.volY0 D * Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, D.dsig ρ =
    (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) * X.B.I.vol X.B.μf X.B.fund * (X.B.e 1).re
  rw [hre, hd, ← hI]
  by_cases hv : X.volK2 = 0
  · rw [hv]
    simp
  ·
    have hK2 : X.B.μf X.K2 ≠ 0 := by
      intro h
      apply hv
      simp [hv2, h]
    have hμ : (X.B.μf X.B.I.Kset).toReal ≠ 0 := by
      rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨fun h => hK2 (measure_mono_null hsub h),
        (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top.ne⟩
    calc Formalism.MainNotions.StandardLattice.volY0 D * ((X.B.μf X.B.I.Kset).toReal / X.volK2) * ∏ ρ, D.dsig ρ
        = (Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) * (X.B.μf X.B.I.Kset).toReal / X.volK2 := by ring
      _ = ((∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal) *
            (X.B.μf X.B.I.Kset).toReal / X.volK2 := by rw [hV]
      _ = (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund * (1 / X.volK2) := by
        rw [div_mul_cancel₀ _ hμ, mul_one_div]

theorem autTie : ∀ (D : D7) (X : HidaSetting D), Nonempty (D.s.HH ≃ₗᵢ[ℂ] HHX X) →
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D →
    X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    AutTie D X.B X.pl := by
  intro D X hHH hint hD hinst hVol hcd hds
  obtain ⟨ι⟩ := hHH
  have hV := GlobalTheory.covol_formalDegree_eq D X hinst hVol hcd hds
  have hI := Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X
  exact
    { n_eq := X.n_eq
      f_eq := GlobalTheory.DegreeRankEquations.f_eq D X
      rd_eq := GlobalTheory.DegreeRankEquations.rd_eq D X
      eps_eq := X.eps_eq
      lam_eq := X.lam_eq
      ds := X.ds
      low := X.low
      g_eq := X.g_eq
      g0_eq := X.g0_eq
      D_eq := by
        rw [GlobalTheory.RowsCount.D_eq_finrank_HHX D X hint, ← ι.toLinearEquiv.finrank_eq, D.s_HH]
      Dstar_eq := hD.trans (dstarD_eq X hI hV) }

end GlobalTheory.BundleTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountTypedOfVolumeStep
section
open Formalism.MainNotions.PlaceDegreeData

namespace GlobalTheory.CountBridge

theorem count_typed_of_volumeStep :
    GlobalTheory.FlagMeas.VolumeStep → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀,
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₁ A C (1 / 16) (1 / 16) := by
  intro hV A
  obtain ⟨n₀, C₀, hC₀, hcount⟩ := _root_.GlobalTheory.CountBridge.count_unbundled (_root_.GlobalTheory.CountFinal.countingTheorem_of_volumeStep hV) A
  refine ⟨n₀, C₀, hC₀, fun n₁ hn₁ C hC _D => ?_⟩
  intro I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h hSet hData
  exact hcount n₁ hn₁ C hC I b lam g g₀ e H σ w Hs σs tens μf fund R Re h hSet hData

end GlobalTheory.CountBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositiveStatement
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWordGenericBound_of_cutBound_positive : PN.NGChain → MeanAmpGen → GenCutP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_cut | exact GlobalTheory.SnPos.rowMainEqP_of_cut | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_cut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChain
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

namespace GlobalTheory

theorem closed_steps_gram_vectors : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 =
      PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

theorem closed_steps_equal_words :
    PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧
      StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧
      (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  have hPts : StepPointsG :=
    Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hNorm : StepNormOneG :=
    Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hLoc : ∀ D, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  exact ⟨Formalism.FourierDecayAlt.P.norm_chain, Formalism.L2.SG.Pf.stepClassG_holds, hPts, hNorm,
    tieOfCtx_of closed_steps_gram_vectors, Formalism.L2.SG.NGPin.stepPinExists,
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form Formalism.L2.SG.Pf.formGC_holds,
    Formalism.L2.SG.Pf.formNGC_holds,
    fun hFam => Formalism.L2.SG.Pf.stepLocGenPinnedG_of_loc (Formalism.L2.SG.Pf.stepLocPinnedG_of_fam hLoc hFam)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalVectorCongruentLocalOrthogonal
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocApprox

theorem iota_gS_typed {D : D7} (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w := by
  obtain ⟨sg, hsg, hq, -⟩ := Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.typed_data Z p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]

end GlobalTheory.LocApprox

namespace GlobalTheory.LocApprox


set_option maxHeartbeats 1000000 in
theorem approx : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O, c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), ∀ x ∈ lattice₂ D Z.M p Λ, x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F))) → ∃ l ∈ Lrep Λ F, x - baseChange₂ D p l ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) := by
  intro D Z p hc Λ hΛ T F x hx hxp
  have hO : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1
  rcases hs : (Z.M p).split with _ | g
  · refine ⟨0, zero_mem _, ?_⟩
    have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = 1 := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    rw [ht, map_one, map_zero, sub_zero]
    exact Submodule.subset_span ⟨x, hx, one_smul _ _⟩
  · have ht : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by simp [Formalism.MainNotions.S.LocNG.theta, hs]
    obtain ⟨w, hw, he⟩ := iota_gS_typed Z p g hs
    rw [ht]
    have hspan := GlobalTheory.LocExt.perp_le Z p F hxp
    have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) (Xsp F)) hΛ.fg
    have hxL : x ∈ lattice₂ D Z.M p (Lrep Λ F) := by
      have : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) (Xsp F))) : Set (Vp D p)) := by
        rw [hsat]; exact ⟨hx, hspan⟩
      exact this
    clear hx hxp hspan hsat
    induction hxL using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hl, rfl⟩ := hv
      exact ⟨l, hl, by rw [sub_self]; exact zero_mem _⟩
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    | add u v _ _ ihu ihv =>
      obtain ⟨l, hl, h⟩ := ihu
      obtain ⟨l', hl', h'⟩ := ihv
      refine ⟨l + l', add_mem hl hl', ?_⟩
      rw [map_add (f := _), show u + v - (baseChange₂ D p l + baseChange₂ D p l') = (u - baseChange₂ D p l) + (v - baseChange₂ D p l') by abel]
      exact add_mem h h'
    | smul o v _ ih =>
      obtain ⟨l, hl, h⟩ := ih
      have ho : (o : (D.s.atP p).Ep) ∈ (D.s.atP p).O := hO ▸ o.2
      obtain ⟨a, o', ho', hco⟩ := hc _ ho
      refine ⟨a • l, Submodule.smul_mem _ a hl, ?_⟩
      have hbl : baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨l, hl.1, rfl⟩
      have e1 : baseChange₂ D p (a • l) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [← baseChange_smul₂]; congr 1; exact (algebraMap_smul D.host.E a l).symm
      have key : ∀ (oo ia ig th : (D.s.atP p).Ep) (vv b : Vp D p), oo = ia + ig * o' → ig = th * w →
          oo • vv - ia • b = oo • (vv - b) + th • ((w * o') • b) := by
        intro oo ia ig th vv b h1 h2
        subst h1 h2
        simp only [smul_sub, add_smul, smul_smul, ← mul_assoc]
        abel
      have hov : o • v = (o : (D.s.atP p).Ep) • v := rfl
      have hob : (o : (D.s.atP p).Ep) • (v - baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.smul_mem _ o h
      have hwo : w * o' ∈ (Z.M p).L.O := hO ▸ mul_mem hw ho'
      have k1 := key (o : (D.s.atP p).Ep) _ _ _ v (baseChange₂ D p l) hco he
      have h3 : (w * o') • baseChange₂ D p l ∈ lattice₂ D Z.M p Λ := (lattice₂ D Z.M p Λ).smul_mem ⟨_, hwo⟩ hbl
      have h4 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • ((w * o') • baseChange₂ D p l) ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) :=
        Submodule.subset_span ⟨_, h3, rfl⟩
      have h5 : (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l ∈
          (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) := by
        rw [k1]; exact add_mem hob h4
      have h6 : o • v - baseChange₂ D p (a • l) = (o : (D.s.atP p).Ep) • v - (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p l := by
        rw [hov, e1]
      rw [h6]
      exact h5

end GlobalTheory.LocApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTerms
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowTermReal

variable {D : D7}

theorem gmap_one' (L : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) L = L := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul' (a b : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) :
    Xflag F i ≤ Xflag F j :=
  Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => show a.1 < j by omega)

theorem adapt_map_xflag {T : D.host.E} {g : GV D} {A B : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g A B)
    (j : ℕ) {x : (VS D).V} (hx : x ∈ Xflag A j) : g x ∈ Xflag B j := by
  change x ∈ Submodule.span D.host.E (A.fl.e '' {i | i.1 < j}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : a.1 < j := ha
    have h1 := hg.2 a.castSucc
    have e1 : frame A a.castSucc = A.fl.e a := by simp [frame, FlagG.fvec]
    have e2 : frame B a.castSucc = B.fl.e a := by simp [frame, FlagG.fvec]
    rw [e1, e2, Fin.val_castSucc] at h1
    have h2 : B.fl.e a ∈ Xflag B j := Submodule.subset_span ⟨a, ha', rfl⟩
    have h3 := xflag_mono B (le_of_lt ha') h1
    simpa using add_mem h3 h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem adapt_mul {T : D.host.E} {g h : GV D} {A B C : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g B C)
    (hh : Adapt h A B) : Adapt (g * h) A C := by
  refine ⟨mul_mem hg.1 hh.1, fun a => ?_⟩
  have e : (g * h) (frame A a) - frame C a =
      g (h (frame A a) - frame B a) + (g (frame B a) - frame C a) := by
    simp only [mul_apply_eq_comp, map_sub]; abel
  rw [e]
  exact add_mem (adapt_map_xflag hg _ (hh.2 a)) (hg.2 a)

theorem adapt_of_nlam {T : D.host.E} {Λ : LV D} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D}
    (hn : n ∈ NLam Λ F) : Adapt n F F := by
  refine ⟨hn.1.1, fun a => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [hz, Fin.val_last]
    have hzo : F.fl.z ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      change x ∈ Submodule.span D.host.E (Set.range F.fl.e) at hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
      | smul c x _ hx => simp [hx]
    have hX : Xsp F ≤ Xflag F D.R.rS :=
      Submodule.span_mono fun _ ⟨i, h⟩ => ⟨i, i.2, h⟩
    exact hX (hn.2.2 _ hzo)
  · have hi : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [hi, Fin.val_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem frame_mapLF' {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {g : GV D}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (a : Fin (D.R.rS + 1)) : frame (mapLF g F) a = g (frame F a) := by
  simp only [mapLF, dite_eq_left hg, frame, FlagG.fvec, mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp

end GlobalTheory.RowTermReal

namespace GlobalTheory.RowTermReal

theorem rowLat_first {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u)) F ∧ IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  _root_.GlobalTheory.RowLatAdapt.row_lattice_of_local_standard D (Tu D u) (D.mem u).A.T_prime.ne_zero (X.Fu u) F Z
    (fun p => (FP p).A) (fun p => (hB p).1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L, (y p).hL, hlat.symm.trans hn.2.2⟩)

theorem rowLat_second {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u')) F' ∧ IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  _root_.GlobalTheory.RowLatAdapt.row_lattice_of_local_standard D (Tu D u') (D.mem u').A.T_prime.ne_zero (X.Fu u') F' Z
    (fun p => (FP p).B) (fun p => (hB p).2.1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L', (y p).hL', hlat.symm.trans hn.2.2⟩)

theorem exists_term_of_locOver : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL
  obtain ⟨g0, hg0, hrow0⟩ := rowLat_first X F F' Z FP hB Λ y hL
  obtain ⟨g0', hg0', hrow0'⟩ := rowLat_second X F F' Z FP hB Λ y hL
  obtain ⟨Λ₁, hΛ₁, σ, hσ, hσΛ⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u u).1 _ hrow0
  obtain ⟨Λ₁', hΛ₁', σ', hσ', hσΛ'⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u' u').1 _ hrow0'
  have hg : Adapt (g0 * σ) (lf D (X.Fu u)) F := adapt_mul hg0 hσ
  have hg' : Adapt (g0' * σ') (lf D (X.Fu u')) F' := adapt_mul hg0' hσ'
  have hgΛ : Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ = Λ₁ := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
  have hgΛ' : Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ = Λ₁' := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
  have hrow : IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ) := hgΛ ▸ (Y.rowsOK u).1 Λ₁ hΛ₁
  have hrow' : IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ) := hgΛ' ▸ (Y.rowsOK u').1 Λ₁' hΛ₁'
  have hPD := _root_.GlobalTheory.Unfold.AdmGlued.glued_frame_PD D X Y u u' F F' w hw hG Z FP hB hR Λ y hL _ _ hg hg' hrow hrow'
  rw [hgΛ] at hPD
  set g := g0 * σ with hgdef
  set g' := g0' * σ' with hg'def
  have hγ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg.1) hg'.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') Λ₁' = Λ₁ := by
    rw [← hgΛ, ← hgΛ', gmap_mul', ← gmap_mul' g' g'⁻¹, mul_inv_cancel, gmap_one']
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X (g⁻¹ * g') hγ
  let p : GCar X u u' (X.Fu u) (X.Fu u') Λ₁ Λ₁' := ⟨(x, g⁻¹ * g'), hx, hγ, hγΛ, hPD⟩
  let t : TauC Y u u' := ⟨Λ₁, hΛ₁, Λ₁', hΛ₁', Quot.mk _ p⟩
  refine ⟨t, ?_⟩
  obtain ⟨n, hn, n', hn', hrel⟩ := Formalism.L2.SG.Pf.SatGramRep.grel_rep t p rfl
  have hlin : t.lin = n⁻¹ * (g⁻¹ * g') * n'⁻¹ := by
    have h : g⁻¹ * g' = n * t.lin * n' := hrel
    rw [h]; group
  refine ⟨g * n, adapt_mul hg (adapt_of_nlam hn), ?_, ?_⟩
  · have hA : Adapt (g' * n'⁻¹) (lf D (X.Fu u')) F' :=
      adapt_mul hg' (adapt_of_nlam (Formalism.L2.SG.Pf.nlam_inv hn'))
    have htl : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
    have e : g * n * t.lin = g' * n'⁻¹ := by rw [hlin]; group
    refine ⟨mul_mem hg.1 hn.1.1, fun a => ?_⟩
    show (g * n) (frame (mapLF t.lin (lf D (X.Fu u'))) a) - frame F' a ∈ _
    rw [frame_mapLF' _ htl, ← mul_apply_eq_comp, e]
    exact hA.2 a
  · show Λ = Formalism.HermitianLatticesTheory.gmap (g * n) Λ₁
    have hn1 : Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₁ := hn.1.2
    rw [gmap_mul', hn1, ← hgΛ, ← gmap_mul', mul_inv_cancel, gmap_one']

end GlobalTheory.RowTermReal
end
end

