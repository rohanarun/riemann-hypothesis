module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubgroupHaarEqConstSmulPiLocalMeasures
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.MuHPi

theorem hloc_eq_HGv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.Pf.WuDec.Hloc X u v =
      (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HGv X u v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := by
  rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]
  rfl

theorem muH_eq_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muHl C u (X.pl v) v) (Formalism.L2.SG.Pf.WuDec.Hloc X u v) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muHl C u τ w) (Formalism.L2.SG.Pf.WuDec.Hloc X u w) := by
      rintro τ _ rfl; exact invOn_muHl C u τ
    intro v
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_coe] at hc hi
  refine Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG X u)
    (Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [Formalism.L2.SG.RealObj.InfCut.ProductExactness.HinfG, Subgroup.coe_pi]
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_conc _ _ fun v => by rw [← hloc_eq_HGv]; exact (hloc v).2.2.1
  · intro g hg
    exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v)
      (by rw [hloc_eq_HGv]; exact hg v (Set.mem_univ v))
  · exact Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuHPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasures
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory.MuNPi

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem muN_eq_pi_muNl : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word),
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  intro D X θ C u
  have hloc : ∀ v, QPK.InvOn (muNl C (X.pl v) v) (NGv X u v : Set _) := by
    have h : ∀ τ w, vOf X τ = w → QPK.InvOn (muNl C τ w) (NGv X u w : Set _) := by
      rintro τ _ rfl
      exact invOn_muNl C u τ
    exact fun v => h (X.pl v) v (X.pl.symm_apply_apply v)
  haveI : ∀ v, SigmaFinite (muNl C (X.pl v) v) := fun v => (hloc v).1
  obtain ⟨hσ, h0, hc, hi⟩ := X.muN_haar u
  haveI := hσ
  rw [← NinfG_coe] at hc hi
  refine PiM.uniq_on_closed (NinfG X u) (NinfG_closed X u) _ _ hc ?_ hi ?_ h0 ?_
  · rw [NinfG, Subgroup.coe_pi]
    exact PiM.pi_conc _ _ fun v => (hloc v).2.2.1
  · intro g hg
    exact PiM.pi_map_mul_left _ g fun v => (hloc v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · exact PiM.pi_ne_zero _ fun v => (hloc v).2.1

end GlobalTheory.MuNPi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupHaarProductEqPiLocalImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section
namespace GlobalTheory.MuSPi

theorem muNH_prod_pi : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) (κN κH : ℝ≥0∞), X.muN u = κN • Measure.pi (fun v => muNl C (X.pl v) v) → X.muH u = κH • Measure.pi (fun v => muHl C u (X.pl v) v) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (κN * κH) • Measure.pi (fun v => QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
  intro D X θ C u κN κH hN hH
  have hsN : ∀ v, SigmaFinite (muNl C (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ _ rfl; exact sf_muNl C τ (Formalism.L2.SG.Pf.WuBL.theta_pos C u τ)
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsH : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  have hsM : ∀ v, SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl; exact (invOn_mulMap C u τ).1
    intro v; exact h (X.pl v) v (X.pl.symm_apply_apply v)
  rw [hN, hH, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul _ (measurable_mul.aemeasurable)]
  congr 1
  have mp := Formalism.L2.SG.RealObj.InfCut.ProductExactness.measurePreserving_piProd (fun v => muNl C (X.pl v) v) (fun v => muHl C u (X.pl v) v)
  rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
    mp.measurable]
  haveI : ∀ v, SigmaFinite (((muNl C (X.pl v) v).prod (muHl C u (X.pl v) v)).map
      (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hsM
  exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
    (fun v => measurable_mul.aemeasurable)

end GlobalTheory.MuSPi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselNormSqBruhatProduct
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem weil_bruhatProd_normSq : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (κ : ℝ≥0∞) (M : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (M v)) → ((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = κ • Measure.pi M → ∀ (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞), (∀ v, Measurable (β v)) → (∀ v x, ∫⁻ s, β v (s * x) ∂(M v) = 1) → ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = κ := by
  intro D X u κ M hMs hS β hβm hβ1
  haveI := hMs
  obtain ⟨hNsf, -, hN0, -⟩ := X.muN_haar u
  obtain ⟨hHsf, -, hH0, -⟩ := X.muH_haar u
  haveI := hNsf
  haveI := hHsf
  have hmul : Measurable (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) := measurable_fst.mul measurable_snd
  have hSmeas : MeasurableSet (X.SinfU u) := (Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u).measurableSet
  have hae : ∀ᵐ s ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)), s ∈ X.SinfU u := by
    refine (ae_map_iff (p := fun s => s ∈ X.SinfU u) hmul.aemeasurable hSmeas).2 ?_
    have h1 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.1 ∈ X.NinfU u :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun s => s ∈ X.NinfU u) (by rw [ae_iff]; exact hN0)
    have h2 : ∀ᵐ p ∂((X.muN u).prod (X.muH u)), p.2 ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun s => s ∈ Hset X.B.I
        (Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.eX c)) ∪
          Set.range (fun c => crdOf X.B.I X.ιE X.bas (X.fY c)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}))
        (by rw [ae_iff]; exact hH0)
    filter_upwards [h1, h2] with p hp1 hp2
    exact Formalism.L2.SG.WuDecayPf.mul_mem_sinfU X u p.1 p.2 hp1 hp2
  have hβprod : Measurable (fun x : X.B.I.Ginf => ∏ v, β v (x v)) :=
    Finset.measurable_prod _ fun v _ => (hβm v).comp (measurable_pi_apply v)
  have hWm : Measurable (fun x : X.B.I.Ginf => ‖X.Wu u x‖ₑ ^ 2) :=
    (X.Wu_spec u).2.2.1.enorm.measurable.pow_const 2
  have hfm : Measurable (fun x : X.B.I.Ginf => (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2) := hβprod.mul hWm
  rw [X.nuQ_weil u _ hfm]
  have hin : ∀ x : X.B.I.Ginf, ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
      ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) = κ * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    have e1 : ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u (s * x)‖ₑ ^ 2
        ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) =
        ∫⁻ s, (∏ v, β v ((s * x) v)) * ‖X.Wu u x‖ₑ ^ 2
          ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with s hs
      rw [← enorm_norm (X.Wu u (s * x)), Formalism.L2.SG.Pf.WuDec.norm_Wu_inv X u s hs x, enorm_norm]
    rw [e1, lintegral_mul_const _ (show Measurable (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) from
      hβprod.comp (measurable_mul_const x)), hS, lintegral_smul_measure]
    have e2 : ∫⁻ s, ∏ v, β v ((s * x) v) ∂(Measure.pi M) = 1 := by
      have e3 : (fun s : X.B.I.Ginf => ∏ v, β v ((s * x) v)) = fun s => ∏ v, β v (s v * x v) := rfl
      rw [e3, QPK.lintegral_fintype_prod (fun v s => β v (s * x v))
        (fun v => (hβm v).comp (measurable_mul_const _))]
      simp [hβ1]
    rw [e2, smul_eq_mul, mul_one]
  simp only [hin]
  rw [lintegral_const_mul _ hWm, (X.Wu_spec u).2.2.2.2, mul_one]

end GlobalTheory
end

