module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0052
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PeriodG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomTie
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0018
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeGapDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.SharpRestriction.CuspSpanNormBounds.RadialGaugeOfGaugeIdentitySlices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.RowsFinalAmpRoot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0028
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.QuantumDeterminants
  Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec

namespace Formalism.L2.SG.Pf.AmpWinGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u : D.what₂.Word)

def muNv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muNl C (X.pl v) v

def muHv (v : InfinitePlace X.B.I.F) : Measure (Formalism.REAL.UJ (X.B.I.ε v)) := muHl C u (X.pl v) v

theorem place_all (hLF : LocFactor C) (hB : WuBessel C) (v : InfinitePlace X.B.I.F) :
    SigmaFinite (muNv C v) ∧ SigmaFinite (muHv C u v) ∧ QPK.InvOn (muNv C v) (Nloc X u v) ∧
      QPK.InvOn (muHv C u v) (Hloc X u v) ∧ muHv C u v Set.univ = 1 ∧
      QPK.mulMap (muNv C v) (muHv C u v) (QPK.prodSet (Nloc X u v) (Hloc X u v))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
          l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v)) := by
  have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w →
      SigmaFinite (muNl C τ w) ∧ SigmaFinite (muHl C u τ w) ∧ QPK.InvOn (muNl C τ w) (Nloc X u w) ∧
      QPK.InvOn (muHl C u τ w) (Hloc X u w) ∧ muHl C u τ w Set.univ = 1 ∧
      QPK.mulMap (muNl C τ w) (muHl C u τ w) (QPK.prodSet (Nloc X u w) (Hloc X u w))ᶜ = 0 ∧
      ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        ∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
    rintro τ w rfl
    have hθ := Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
    have hH1 : muHl C u τ (vOf X τ) Set.univ = 1 := by
      have h : (muHl C u τ (vOf X τ)).map (eT C τ (vOf X τ)) Set.univ = C.muW u τ Set.univ := by
        rw [map_muHl C u τ]
      rw [Measure.map_apply (eT_emb C τ (vOf X τ)).measurable MeasurableSet.univ, Set.preimage_univ,
        C.muW_one u τ] at h
      exact h
    have hconc : QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))
        (QPK.prodSet (Nloc X u (vOf X τ)) (Hloc X u (vOf X τ)))ᶜ = 0 := by
      have hHH : Hloc X u (vOf X τ) = Hfix X u (vOf X τ) := Hloc_eq X u (vOf X τ)
      rw [hHH]
      exact (invOn_mulMap C u τ).2.2.1
    obtain ⟨β, hβm, hβ1, hid⟩ := loc_main C u τ hLF hB
    exact ⟨sf_muNl C τ hθ, sf_muHl C u τ, invOn_muNl C u τ, invOn_muHl C u τ, hH1, hconc, β, hβm, hβ1, hid⟩
  exact key (X.pl v) v (X.pl.symm_apply_apply v)

theorem map_trInf (hsf : ∀ v, SigmaFinite (muNv C v)) (hθ : 0 < θ) :
    MeasurableEmbedding (Formalism.L2.SG.LoopTerm.trInf C) ∧
      (Measure.pi (muNv C)).map (Formalism.L2.SG.LoopTerm.trInf C) = Formalism.L2.SG.LoopTerm.dnB D θ := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : Formalism.L2.SG.LoopTerm.trInf C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  refine ⟨htr ▸ hPemb.comp (MeasurableEquiv.measurableEmbedding _), ?_⟩
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (muNv C)).map (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => muNv C (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (muNv C) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => muNv C (X.pl.symm τ)) = fun τ => muNl C τ (X.pl.symm τ) := by
    funext τ
    show muNl C (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muNl C τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = muNB D θ := fun τ => map_muNl C τ hθ
  have : ∀ τ, SigmaFinite ((muNl C τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (muNB_haar (D := D) hθ).1
  refine (Measure.pi_map_pi (μ := fun τ => muNl C τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]
  rfl

theorem massU_of (Y : Formalism.L2.SG.Full.Full X) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.MassU Y u C hB := by
  have hθ : 0 < θ := by
    obtain ⟨τ⟩ := Formalism.L2.SG.LoopTerm.tau_nonempty D
    exact Formalism.L2.SG.Pf.WuBL.theta_pos C u τ
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using place_all C u hLF hB

  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  have hpiH : Set.pi Set.univ (Hloc X u) = Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨k1, k2, k3, k4⟩ := X.muH_haar u
  have hHfix : ∀ v, Hloc X u v = Hfix X u v := fun v => Hloc_eq X u v
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨cH, hcH0, hcHt, hcH⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Hloc X u))
    (isClosed_set_pi fun v _ => by rw [hHfix]; exact (place_facts X u v).2.1.isClosed)
    (QPK.isGrp_pi _ fun v => by rw [hHfix]; exact (place_facts X u v).2.2.2.1)
    (X.muH u) (Measure.pi (muHv C u)) ⟨k1, k2, by rw [hpiH]; exact k3, by rw [hpiH]; exact k4⟩
    (QPK.invOn_pi _ _ hH)

  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hF_def
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  have hFinv : ∀ v, ∀ m ∈ Nloc X u v, ∀ h ∈ Hloc X u v, ∀ x, F v (m * h * x) = F v x := by
    intro v m hm h hh x
    have hs := mul_mem_Sloc X u v (Nloc_sub X u v hm) (Hloc_sub X u v hh)
    show ‖X.Wloc u v (m * h * x)‖ₑ ^ 2 = ‖X.Wloc u v x‖ₑ ^ 2
    rw [← enorm_norm (X.Wloc u v (m * h * x)), norm_Wloc_inv X u v hs, enorm_norm]
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hf_def
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * F v y ∂(Formalism.REAL.muG (X.B.I.ε v)) :=
    QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
      (cN * cH) * ∏ v, F v (x v) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      hcN, hcH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have e1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [e1]
    rw [QPK.lintegral_pi_prod_mul (muNv C) (muHv C u) (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have e2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (muNv C v) (muHv C u v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (muNv C v) (muHv C u v)), s ∈ QPK.prodSet (Nloc X u v) (Hloc X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        simp only [hFinv v m hm h hh])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [e2]
    ring
  simp_rw [hin] at key
  have hPm : Measurable (fun x : X.B.I.Ginf => ∏ v, F v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hFm v).comp (measurable_pi_apply v)
  rw [lintegral_const_mul _ hPm, hL1] at key
  have hW1 : ∫⁻ x, ∏ v, F v (x v) ∂(X.nuQ u) = 1 := by
    rw [← (X.Wu_spec u).2.2.2.2]
    refine lintegral_congr fun x => ?_
    rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
  rw [hW1, mul_one] at key

  have hprod : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
    rw [← key]
    refine (Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) _
      (fun v => rfl)).symm.trans ?_
    exact Finset.prod_congr rfl fun v _ => (hloc v).symm

  obtain ⟨hemb, hmapT⟩ := map_trInf C (fun v => hsfN v) hθ
  have hcov : Measure.pi (muNv C) (Y.FN u) =
      Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [← hmapT, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  have hNF : X.muN u (Y.FN u) = cN * Formalism.L2.SG.LoopTerm.dnB D θ (Formalism.L2.SG.LoopTerm.trInf C '' Y.FN u) := by
    rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]
  have hHU : X.muH u Set.univ = cH := by
    rw [hcH, Measure.smul_apply, smul_eq_mul, ← Set.pi_univ, Measure.pi_pi]
    rw [Finset.prod_eq_one fun v _ => hH1 v, mul_one]
  unfold Formalism.L2.SG.Pf.AmpWin.MassU Formalism.L2.SG.LoopTerm.covN
  rw [hNF, hHU, ← ENNReal.toReal_prod, hprod, ENNReal.toReal_mul, ENNReal.toReal_mul]
  ring

theorem ampWin_of_loc (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C) :
    Formalism.L2.SG.Pf.AmpWin.AmpWinP Y u u' C hB :=
  Formalism.L2.SG.Pf.AmpWin.ampWin_of Y u u' C hB (massU_of C u Y hLF hB) (massU_of C u' Y hLF hB)
    (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u τ) (fun τ => Formalism.L2.SG.Pf.GoodS.l2SG_phiOf_ne_zero_and_lt_infty C hLF hB u' τ)

theorem K0_mem_covWin_of_locFactor_wuBessel (Y : Formalism.L2.SG.Full.Full X) (u' : D.what₂.Word) (hLF : LocFactor C) (hB : WuBessel C)
    (hV : 0 < X.volK2)
    (hc : 0 < Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') {large₂} {C1 : ℝ}
    (hW : Formalism.L2.SG.LoopTerm.CovWinN (Y := Y) C large₂ C1 u u') :
    0 < Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB ∧
      Formalism.L2.SG.Pf.OOCore3.WinK large₂ C1 (Formalism.L2.SG.Pf.LocNorm.K0 Y u u' C hB) := by
  have hA := ampWin_of_loc C u Y u' hLF hB
  exact ⟨Formalism.L2.SG.Pf.AmpWin.minWeight_pos Y u u' C hB hA hV hc, Formalism.L2.SG.Pf.AmpWin.K0_mem_covWin_of_ampWin Y u u' C hB hA hV hW⟩

end Formalism.L2.SG.Pf.AmpWinGlob
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmplitudeBoundsAllChoicesUniform
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.Pf.OOCore3 Formalism.L2.SG.Pf.LocNorm
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def AmplitudeBoundsAllChoices {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ θ : ℝ, 0 < θ ∧ normWin D large₂ C1 θ ∧ ∀ (C : Choice X θ) (hB : WuBessel C),
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocUniqP u u' C hB νl) ∧
    0 < K0 Y u u' C hB ∧ WinK large₂ C1 (K0 Y u u' C hB) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

def AmplitudeBoundsAllChoicesUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → AmplitudeBoundsAllChoices large₂ Y u u' ν C1 Cn Ire

end Formalism.L2.SG.Pf.ThmBChain6
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellB
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {k r : ℕ}

theorem isRelStab_of_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) {g : Mx k r}
    (h : IsRelStab (turnL L ka) (tTi k r * g * tT k r)) : IsRelStab L g := by
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  intro a ha
  have ha' : tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r) := (conjI_mem_RStab_iff g a).mpr ha
  have e2 : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * a * g) * tT k r := by
    rw [← conjI_inv, ← conjI_mul, ← conjI_mul]
  have := h _ ha'
  change psi k r L.z (cOfDpsi (ka : ℂ)) (tTi k r * a * tT k r) =
    psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)) at this
  rw [e2, psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc'] at this
  exact this

theorem orbQuot_exists (L : LocBessel k r) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {μR : Measure (Mt k r)}
    (hμ : IsHaarOn (RStab k r g) μR) : ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have hν := Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top
  have : SigmaFinite (haarLie (Nset k r) 1) := hν.1
  have hs := PI.AmpOrbQuot.muN_smul L
  have : SFinite L.μN := by rw [hs]; infer_instance
  have hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN := by
    intro s hs'
    rw [hs, Measure.map_smul, hν.2.2.2 s hs']
    exact (Formalism.MainNotions.BridgeCSB.continuous_lmulM s).measurable.aemeasurable
  have hc : L.μN (PI.AmpOrbQuot.NS k r)ᶜ = 0 := by
    rw [hs, Measure.smul_apply, smul_eq_mul]
    have : haarLie (Nset k r) 1 (PI.AmpOrbQuot.NS k r)ᶜ = 0 := hν.2.2.1
    rw [this, mul_zero]
  exact PI.AmpOrbQuot.exists_isOrbQuot_of_isHaarOn L g μR hg hμ hN hc

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(C.isT τ).1, (C.isT τ).2.1, (C.isT τ).2.2.1, fun a => ((C.isT τ).2.2.2 a a rfl).1,
    fun a => ((C.isT τ).2.2.2 a a rfl).2⟩

theorem gB_mem (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gB C τ γ ∈ UH (Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_C C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ)

theorem relStab_of_relevant (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)) :
    IsRelStab (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (gB C τ γ) := by
  set L := toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT' with hL
  have hκ : (0 : ℝ) < (kaB D)⁻¹ := inv_pos.mpr (kaB_pos D)
  have hc : L.c = ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  apply isRelStab_of_turn L (kaB D) hc
  rw [← isRelStab_iff hκ one_pos (turnL L (kaB D)) (stdL L (kaB D) (kaB_pos D)) L.hz.1 L.hz'.1 rfl rfl rfl]
  have hz : (baseOf X C u u' (vOf X τ)).z = (stdL L (kaB D) (kaB_pos D)).z := zc_vOf_eq_zB_of_inWb C u u' τ L.hz.1
  have hz' : (baseOf X C u u' (vOf X τ)).z' = (stdL L (kaB D) (kaB_pos D)).z' := zc_vOf_eq_zB_of_inWb C u' u τ L.hz'.1
  have hcs : (stdL L (kaB D) (kaB_pos D)).c = cStd := stdL_c L (kaB D) (kaB_pos D)
  show IsRelStab (stdL L (kaB D) (kaB_pos D)) (gStd (kaB D) (gB C τ γ))
  have hγ : gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := gStd_eq C τ γ
  intro a ha
  rw [hγ] at ha ⊢
  have h2 := h.2 a ha
  rw [hz, hz'] at h2
  show psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z (stdL L (kaB D) (kaB_pos D)).c a =
    psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z' (stdL L (kaB D) (kaB_pos D)).c _
  rw [hcs]
  exact h2

section Scale

theorem det_sub_diag {m n : ℕ} (s l : Fin m → ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (h : n ≤ m) :
    ((Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ i : Fin n, s (Fin.castLE h i) * l (Fin.castLE h i)) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.diagonal (s ∘ Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
        Matrix.diagonal (l ∘ Fin.castLE h) := by
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp only [Function.comp]
  ring

theorem mono_scale {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Formalism.FourierDecayAlt.C2.IsMonomial Z) {s l : Fin m → ℂ}
    (hs : ∀ i, s i ≠ 0) (hl : ∀ i, l i ≠ 0) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Matrix.diagonal s * Z * Matrix.diagonal l) := by
  obtain ⟨w, d, hd, rfl⟩ := hZ
  refine ⟨w, fun a => s (w a) * d a * l a, fun a => mul_ne_zero (mul_ne_zero (hs _) (hd a)) (hl a), ?_⟩
  ext i a
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · simp

end Scale

theorem zhat_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1) :=
  Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_C C u τ) (trHyp_C C u' τ) one_ne_zero (uMat γ)

theorem mono_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ)) := by
  rw [zhat_B C u u' τ γ]
  exact mono_scale h (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)

section GfTr

open Formalism.L2.SG.RealObj.InfCut

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem gf_pos_tr (hT : Formalism.L2.SG.Pf.Bridge.TrHyp F Qm Qim c) (hT' : Formalism.L2.SG.Pf.Bridge.TrHyp F' Qm Qim c)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (h : 0 < Gv F.T F'.T (Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A)) :
    0 < Formalism.QuantumDeterminants.Gf k r (Qim *ᵥ F.z) (Qim *ᵥ F'.z) (Qim * A * Qm) := by
  have hz := Formalism.L2.SG.Pf.Bridge.zhat_cs hT hT' one_ne_zero A
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin
  rw [hz, det_sub_diag, det_sub_diag, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT']
  have hsq : ∀ x : ℂ, star x * x = ((Complex.normSq x : ℝ) : ℂ) := fun x => by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [hsq, ← Complex.ofReal_prod, Complex.normSq_mul, Complex.normSq_ofReal]
  have hp : (∏ x : Fin ((Fin.last (r + 1) : Fin (r + 2)) : ℕ),
      Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) x))) =
        ∏ x : Fin ((⟨r, by omega⟩ : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1
          (Fin.castLE (Nat.le_of_lt_succ (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) := by
    show (∏ x : Fin (r + 1), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (le_refl (r + 1)) x))) =
      ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_succ r) x))
    rw [Fin.prod_univ_castSucc]
    have e1 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
    rw [e1, Formalism.L2.SG.Pf.Bridge.lam_last, map_one, mul_one]
    rfl
  rw [hp]
  set Λ : ℝ := ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ
    (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) with hΛ
  have hΛpos : 0 < Λ := Finset.prod_pos fun i _ => Complex.normSq_pos.mpr
    (Formalism.L2.SG.Pf.Bridge.lam_ne hT one_ne_zero _)
  unfold Gv Formalism.L2.SG.RealObj.Dl at h
  rw [dite_eq_left le_rfl, dite_eq_left (Nat.le_succ r)] at h
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h
  have hΛ2 : 0 < Λ * Λ := mul_pos hΛpos hΛpos
  have key := mul_pos hΛ2 h
  show 0 < Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1)))).det -
    F.T * F'.T * (Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det)
  linarith [key]

end GfTr

theorem gf_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : 0 < Gv (Tw (D := D) u) (Tw (D := D) u')
      (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) :=
  gf_pos_tr (trHyp_C C u τ) (trHyp_C C u' τ) (uMat γ) h

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinHyp_at (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (Formalism.L2.SG.Pf.Carrier.sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (j : Fin (nfE D)) (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j))))
    (hH : Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
      (tauE X e j) γ μRv ν) :
    Formalism.L2.SG.Pf.Carrier.CarPinTor.PinHypAt C u u' (e (plE D j)) γ μRv ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH
  refine ⟨h1, h2, ?_, h4, h5⟩
  have key : ∀ j' : Fin (nfE D), j' = (tauE X e).symm (tauE X e j) →
      Formalism.FourierDecayAlt.C6.IsRelevant (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) →
      Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) := by
    intro j' hj' h
    rw [Equiv.symm_apply_apply] at hj'
    subst hj'
    rw [towersOf_base] at h
    exact h
  exact key _ rfl h3

end Formalism.L2.SG.Pf.CarrierT
end
end

