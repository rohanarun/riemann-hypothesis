module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.DoubleCosetBesselBoundOfGapConstantLe
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0441
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.NormalizingConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0372
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0440

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
section
namespace GlobalTheory

theorem uniqGap_and_besselOfW : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW :=
  ⟨CompanionTheory.Lime.BM.uniqGap_holds, Formalism.MainNotions.BridgeCS3dBOW.besselOfW_holds⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bp_forms_of_gapIn_thmBpDS : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.pointwiseBound_at_place_of_locBessel hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.ThA.BpDict.bpIneq_of_thmBpAt
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.discreteSeriesCoefficient_smooth_decay_capelliEigen_largeGap hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar
section
open scoped Classical ENNReal
open MeasureTheory

noncomputable section

namespace GlobalTheory.CovNFormulaPf

theorem pi_const_smul' {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : NNReal) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

theorem main : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula :=
  Formalism.MainStatements.RowRest.covariance_formula

end GlobalTheory.CovNFormulaPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeilStatement
section
open GlobalTheory.SnFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFamilyStep_of_siegelWeil : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFamTop.stepFamG_of_SWXS | exact GlobalTheory.SnFamTop.stepFamG_of_SWXS | (intros; apply GlobalTheory.SnFamTop.stepFamG_of_SWXS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalConst

theorem constC : ConstC := by
  intro D X Y u C hB hG hcov
  have hS : ∀ τ, GoodS D (lamD D τ) (locS hB u u τ) := fun τ => (hG.2 u τ).2
  have hc : ∀ τ, 0 < cOf hB u τ := fun τ => (hS τ).2.2.2.2.2.2.2.1
  set d : D.what₂.Tau → ℝ := fun τ => (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) with hd
  set L : D.what₂.Tau → ℝ := fun τ => (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal with hL
  have hcL : ∀ τ, cOf hB u τ = L τ / d τ := fun τ => rfl
  have hdpos : ∀ τ, 0 < d τ := by
    intro τ
    rcases (show (0:ℝ) ≤ d τ by positivity).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, div_zero] at this; exact absurd this (lt_irrefl 0)
  have hLpos : ∀ τ, 0 < L τ := by
    intro τ
    rcases (show (0:ℝ) ≤ L τ from ENNReal.toReal_nonneg).lt_or_eq with h | h
    · exact h
    · have := hc τ; rw [hcL, ← h, zero_div] at this; exact absurd this (lt_irrefl 0)
  refine ⟨fun τ => ⟨hc τ, ?_⟩, ?_⟩
  · have e : cOf hB u τ * (Module.finrank ℂ (X.Vloc u (vOf X τ)) : ℝ) /
        (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal = 1 := by
      change L τ / d τ * d τ / L τ = 1
      field_simp [(hdpos τ).ne', (hLpos τ).ne']
    unfold sclOf
    rw [e, Real.sqrt_one, Complex.ofReal_one]
  ·
    obtain ⟨cN, hN0, hNT, hN⟩ := _root_.GlobalTheory.muN_eq_const_mul_pi_trI D X C hB hG u
    obtain ⟨cH, hH0, hHT, hHu, hH⟩ := _root_.GlobalTheory.PullHaarW.pullH D X C hB hG u
    have hP := _root_.GlobalTheory.UnitW.prod_l2SG_eq D X C hB hG u cN cH hN0 hNT hH0 hHT hN hH
    have hP' : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = cN * cH := by
      rw [← hP]; exact Finset.prod_congr rfl fun τ _ => _root_.GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported D X C hB hG u τ
    have hFN : MeasurableSet (Y.FN u) := (Y.FN_fund u).1
    have hmN : (X.muN u (Y.FN u)).toReal = cN.toReal * (covN C Y u).toReal := by
      rw [hN _ hFN, ENNReal.toReal_mul]; rfl
    have hmH : (X.muH u Set.univ).toReal = cH.toReal := by rw [hHu]
    have hkey : (∏ τ, L τ) * (covN C Y u).toReal =
        (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
      have : (∏ τ, L τ) = (∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ)).toReal := by
        rw [ENNReal.toReal_prod]
      rw [this, hP', ENNReal.toReal_mul, hmN, hmH]; ring
    have hdd : (Module.finrank ℂ (X.Vpi u) : ℝ) = ∏ τ, d τ := by
      rw [Formalism.L2.SG.Pf.finrank_Vpi X u, Nat.cast_prod]
      exact (Fintype.prod_equiv X.pl.symm (fun τ => d τ) _ fun τ => rfl).symm
    have hprod : ∏ τ, cOf hB u τ = (∏ τ, L τ) / ∏ τ, d τ := by
      rw [← Finset.prod_div_distrib]; exact Finset.prod_congr rfl fun τ _ => hcL τ
    unfold Formalism.L2.SG.TermOp.scl Formalism.L2.SG.PoincareInHH.PoincareSetting.c0X
    rw [hprod, ← hdd]
    set mN := (X.muN u (Y.FN u)).toReal
    set mH := (X.muH u Set.univ).toReal
    set dd := (Module.finrank ℂ (X.Vpi u) : ℝ)
    set V := X.volK2
    set cv := (covN C Y u).toReal
    have hdd0 : 0 < dd := by rw [hdd]; exact Finset.prod_pos fun τ _ => hdpos τ
    have hmN0 : 0 ≤ mN := ENNReal.toReal_nonneg
    have hmH0 : 0 ≤ mH := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    have hc0 : 0 ≤ V * mN * mH / dd := by positivity
    rw [Real.sqrt_mul_self hc0]
    by_cases h0 : V * mN * mH = 0
    · rw [h0, zero_div, _root_.inv_zero]; simp
    · have hV : V ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmN : mN ≠ 0 := by intro h; apply h0; rw [h]; ring
      have hmH : mH ≠ 0 := by intro h; apply h0; rw [h]; ring
      have e : (V * mN * mH / dd)⁻¹ * V * ((∏ τ, L τ) / dd) * cv = 1 := by
        field_simp
        linear_combination hkey
      rw [e]

end GlobalTheory.LocalConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductL2Positive
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem prod_lint (D : D7) (X : HidaSetting D) (u : D.what₂.Word)
    (β : ∀ v : InfinitePlace X.B.I.F, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞) (hβm : ∀ v, Measurable (β v)) :
    ∫⁻ x, (∏ v, β v (x v)) * ‖X.Wu u x‖ₑ ^ 2 ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ y, β v y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hW : ∀ x : X.B.I.Ginf, ‖X.Wu u x‖ₑ ^ 2 = ∏ v, ‖X.Wloc u v (x v)‖ₑ ^ 2 := by
    intro x
    have : ‖X.Wu u x‖ₑ = ∏ v, ‖X.Wloc u v (x v)‖ₑ := by
      rw [← ofReal_norm_eq_enorm, Formalism.L2.SG.Pf.WuDec.norm_Wu,
        ENNReal.ofReal_prod_of_nonneg (fun v _ => norm_nonneg _)]
      simp only [ofReal_norm_eq_enorm]
    rw [this, Finset.prod_pow]
  simp_rw [hW, ← Finset.prod_mul_distrib]
  have : ∀ v, SigmaFinite (Formalism.REAL.muG (X.B.I.ε v)) := fun v => inferInstance
  exact QPK.lintegral_fintype_prod (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v y => β v y * ‖X.Wloc u v y‖ₑ ^ 2)
    (fun v => (hβm v).mul ((X.Wloc_cont u v).enorm.measurable.pow_const 2))

theorem muH_univ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    Measure.pi (fun v => muHl C u (X.pl v) v) Set.univ = 1 := by
  haveI : ∀ v, SigmaFinite (muHl C u (X.pl v) v) := fun v => by
    have h : ∀ τ w, vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ _ rfl; exact sf_muHl C u τ
    exact h _ _ (X.pl.symm_apply_apply v)
  rw [Measure.pi_univ]
  refine Finset.prod_eq_one fun v _ => ?_
  have h : ∀ τ w, vOf X τ = w → muHl C u τ w Set.univ = 1 := by
    rintro τ _ rfl
    rw [← Set.preimage_univ (f := eT C τ (vOf X τ)), ← Measure.map_apply (eT_emb C τ _).measurable MeasurableSet.univ,
      map_muHl C u τ, C.muW_one u τ]
  exact h _ _ (X.pl.symm_apply_apply v)

end GlobalTheory.ProductL2

namespace GlobalTheory.ProductL2
open Formalism.L2.SG.Pf.AmpWinLoc

theorem l2prod : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word), 0 < θ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → 0 < (X.muN u (Y.FN u)).toReal → 0 < (X.muH u Set.univ).toReal → (∀ τ, 0 < (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) ∧ (∏ τ, (l2SG (C.nuS u τ) (phiOf hB u τ)).toReal) * (Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (X.muN u (Y.FN u)).toReal * (X.muH u Set.univ).toReal := by
  intro D X Y θ C hB u hθ _ _ _
  have key : ∀ v, ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) = 1) ∧
      (∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) =
        l2SG (C.nuS u (X.pl v)) (phiOf hB u (X.pl v))) ∧
      SigmaFinite (QPK.mulMap (muNl C (X.pl v) v) (muHl C u (X.pl v) v)) := by
    intro v
    have h : ∀ τ w, vOf X τ = w → ∃ β : Formalism.REAL.UJ (X.B.I.ε w) → ℝ≥0∞, Measurable β ∧
        (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ w) (muHl C u τ w)) = 1) ∧
        (∫⁻ y, β y * ‖X.Wloc u w y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε w)) =
          l2SG (C.nuS u τ) (phiOf hB u τ)) ∧
        SigmaFinite (QPK.mulMap (muNl C τ w) (muHl C u τ w)) := by
      rintro τ _ rfl
      obtain ⟨β, h1, h2, h3⟩ := _root_.GlobalTheory.SlocTie.loc_main D X θ C hB u τ
      exact ⟨β, h1, h2, h3, (invOn_mulMap C u τ).1⟩
    exact h (X.pl v) v (X.pl.symm_apply_apply v)
  choose β hβm hβ1 hβl hsf using key
  obtain ⟨κN, hN0, hNt, hN⟩ := _root_.GlobalTheory.MuNPi.muN_eq_pi_muNl D X θ C u
  obtain ⟨κH, hH0, hHt, hH⟩ := _root_.GlobalTheory.MuHPi.muH_eq_pi D X θ C u
  have hS := _root_.GlobalTheory.MuSPi.muNH_prod_pi D X θ C u κN κH hN hH
  have hW := _root_.GlobalTheory.weil_bruhatProd_normSq D X u (κN * κH) _ hsf hS β hβm hβ1
  rw [prod_lint D X u β hβm] at hW
  simp only [hβl] at hW
  have hP : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) = κN * κH := by
    rw [← hW]; exact (Equiv.prod_comp X.pl (fun τ => l2SG (C.nuS u τ) (phiOf hB u τ))).symm
  have hP0 : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := by rw [hP]; exact mul_ne_zero hN0 hH0
  have hPt : ∏ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by rw [hP]; exact ENNReal.mul_ne_top hNt hHt
  have hne0 : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ 0 := fun τ =>
    (Finset.prod_ne_zero_iff.1 hP0) τ (Finset.mem_univ τ)
  have hnet : ∀ τ, l2SG (C.nuS u τ) (phiOf hB u τ) ≠ ⊤ := by
    intro τ ht
    apply hPt
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ht]
    exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun τ' _ => hne0 τ')
  refine ⟨fun τ => ENNReal.toReal_pos (hne0 τ) (hnet τ), ?_⟩
  rw [← ENNReal.toReal_prod, hP, ← _root_.GlobalTheory.pi_muNl_eq_dnB_image D X θ C (Y.FN u) hθ (Y.FN_fund u).1, hN, hH,
    Measure.smul_apply, Measure.smul_apply, muH_univ D X θ C u]
  simp only [smul_eq_mul, mul_one, ENNReal.toReal_mul]
  ring

end GlobalTheory.ProductL2
end

