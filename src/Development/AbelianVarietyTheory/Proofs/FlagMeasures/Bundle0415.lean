module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0412
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0017
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0357
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0407
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqSmulNormalisedAmplitudeLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_eq_smul_normalisedAmplitude_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | exact GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap | (intros; apply GlobalTheory.AmpNormalGap.amp_eq_smul_normalised_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLocalDataMomentPieriHypothesesStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeLocalData_momentPieriHypotheses : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ τ w w' θ (W : LocW D.R.k D.R.rS), HypTT D w w' → 0 < θ → GoodW D τ w w' θ W → ∀ t ∈ GG D.R.k D.R.rS, (∀ n, n ∈ Nset D.R.k D.R.rS ↔ t * n * t⁻¹ ∈ Nset D.R.k D.R.rS) → (∀ z, inWb D.R.k D.R.rS z → (∀ h ∈ UWset D.R.k D.R.rS z, t * h = h * t) ∧ ∀ n ∈ Nset D.R.k D.R.rS, psi D.R.k D.R.rS z cStd n = psiS D z (t * n * t⁻¹)) → ∀ R : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Rep D.R.k D.R.rS, IsFam (lamD D τ) (D.R.k * D.R.m ^ 5) R → haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; ∃ (U U' : ℕ → ℝ) (l : ∀ ν, (R ν).H → W.Wp) (l' : ∀ ν, (R ν).H → W.Wq) (dg : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℝ), Setup (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z W.π W.μW (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l dg ∧ Setup (lamD D τ) U' (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) W.z' W.π' W.μW' (W.μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) W.μG (W.νS'.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) R l' dg := by
  first | exact @GlobalTheory.Amp.LocalSetupGap.exists_setup_both | exact GlobalTheory.Amp.LocalSetupGap.exists_setup_both | (intros; apply GlobalTheory.Amp.LocalSetupGap.exists_setup_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudePieriRelevantCellLargeGap
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellPieriG

open GlobalTheory.CellPieri

variable {k r : ℕ}

theorem amp_eq_orb (hH : GlobalTheory.GapIn.Hyp) (hA : GlobalTheory.GapIn.AmpKF0) (hC : CellConv) (L : LocBessel k r) (R : Rep k r)
    (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H)
    [CompleteSpace L.Wp] [CompleteSpace L.Wq]
    (hR : R.IsDS L.ε mu) (hgap : GapAtLeast L.ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hcell : GapCell k r h)
    (hc : L.c ≠ 0) (hκ : L.κN ≠ ⊤) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hl : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hl' : ∀ x ∈ R.sm, ∀ v ∈ R.TK,
      Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))
    (hw : PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
    (ν : Measure (PairSp k r)) (hD : CellData L μG γ μR νR ν) (v v' : R.H) (hv : R.KFin v) (hv' : R.KFin v')
    (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (coefR R v v' ξ ξ') γ) ν ∧
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) * (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ)) • amp R l l' w νR γ =
        OrbInt L (coefR R v v' ξ ξ') γ ν := by
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  obtain ⟨-, -, -, -, hsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw
  have hle : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp R.σ w, x ∈ R.TK := by
    intro x hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, w, hwK, rfl⟩
  have hD' : CellData (withRep L R mu hR) μG γ μR νR ν := hD
  obtain ⟨b, hb0, hb1, hb2⟩ := hC k r L h μG γ μR νR ν hκ hok hcell hD hD.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hOne : OnePlaceKF (withRep L R mu hR) h μG w l l' :=
    ⟨⟨hgap, hok, hc, hw, hG, fun x hx y hy => hl x (hsm x (hle x hx)) y (hle y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hle y hy)⟩,
      fun x hx y hy => hl x (hsm x (hle x hx)) y (hKT y hy),
      fun x hx y hy => hl' x (hsm x (hle x hx)) y (hKT y hy)⟩
  have h1 := hA k r (withRep L R mu hR) h μG w l l' hOne γ μR νR ν hD' b hb0 hb1 hb2 v v' hv hv' ξ ξ'
  have h2 := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD').2 b hb0 (by linarith)
    hb2 v v' hv hv' ξ ξ'
  refine ⟨h2, ?_⟩
  obtain ⟨c, hc0, hc1⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn, -⟩ := hw
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hDG : R.IsDG L.ε mu := ⟨hR.1, hR.2, h, hgap, hok⟩
  have hf : (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ) ≠ 0 := by
    rw [(hc1 mu R hDG).1 w hw0]
    exact Complex.ofReal_ne_zero.mpr (mul_pos hc0 (fdegHC_pos hR.1.1)).ne'
  have h3 : (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • amp R l l' w νR γ =
      ((PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)⁻¹) • OrbInt L (coefR R v v' ξ ξ') γ ν := h1
  rw [mul_smul, h3, smul_smul, mul_inv_cancel₀ hf, one_smul]

theorem amp_pieri : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  intro hH hA hC k r ι κ _ _ _ _ ρ Γ d L R RI io pr ep mu muI h μG om om' l l' lI lI' w wI κ₀ κ₁
  haveI := FiniteDimensional.complete ℂ L.Wp
  haveI := FiniteDimensional.complete ℂ L.Wq
  intro hR hgap hRI hok hcell hc hκ hG hρ hT hom hom' hl hl' hlI ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hw hwI hκI γ μR νR ν hD
  have hKF : PI.KFinSmooth := hH.1.1.2.2.1
  have hvs : v ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v hv
  have hvs' : v' ∈ R.sm := hKF k r L.ε mu R.H R.σ hR.1 hR.2 v' hv'
  obtain ⟨hK, hsplit⟩ := GlobalTheory.KFinCoefSplit.kfin_coef_mul_split hKF k r ι κ ρ Γ d R RI io pr ep L.ε mu muI om om' v v' hR
    (fun I => (hRI I).1) hρ hT hv hv'
  obtain ⟨-, e0⟩ := amp_eq_orb hH hA hC L R mu h μG l l' w hR hgap hok hcell hc hκ hG hl hl' hw γ μR νR ν hD
    v v' hv hv' (l v) (l' v')
  have eI := fun I => amp_eq_orb hH hA hC L (RI I) (muI I) h μG (lI I) (lI' I) (wI I) (hRI I).1 (hRI I).2 hok hcell
    hc hκ hG (hlI I).1 (hlI I).2 (hwI I) γ μR νR ν hD _ _ (hK I).1 (hK I).2 (l v) (l' v')
  have hae := (GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite hH k r (withRep L R mu hR) h μG γ μR νR ν hgap hok hκ hD).1
  have hc0 : ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ ≠ 0 :=
    mul_ne_zero (inner_self_ne_zero.mpr hv0) (inner_self_ne_zero.mpr hv0')
  have horb : herm Γ (ρ γ *ᵥ om') om • OrbInt L (coefR R v v' (l v) (l' v')) γ ν =
      ∑ I, (ep I : ℂ) • OrbInt L (coefR (RI I) (∑ c, pr I c (tm R om v c)) (∑ c, pr I c (tm R om' v' c))
        (l v) (l' v')) γ ν := by
    unfold OrbInt
    simp only [← integral_smul]
    refine Eq.trans (integral_congr_ae ?_) (integral_finsetSum _ (fun I _ => (eI I).1.smul (ep I : ℂ)))
    filter_upwards [hae] with p hp
    obtain ⟨hm, he⟩ := herm_cell hρ hom hom' hD.1 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    have hs := hsplit _ hm
    rw [he] at hs
    ext x
    simp only [besselIntg, coefR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, map_smul, smul_smul, Pi.smul_apply,
      ← Finset.sum_smul]
    congr 1
    have key : ∀ (D A B C : ℂ) (e f : κ → ℂ), D * C = ∑ I, e I * f I →
        D * A * (B * C) = ∑ I, e I * A * (B * f I) := by
      intro D A B C e f hh
      rw [show D * A * (B * C) = D * C * (A * B) by ring, hh, Finset.sum_mul]
      exact Finset.sum_congr rfl fun I _ => by ring
    exact key _ _ _ _ _ _ hs
  apply smul_right_injective _ hc0
  simp only [Finset.smul_sum, smul_smul]
  rw [mul_comm, mul_assoc, mul_smul, e0, horb]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← (eI I).2, smul_smul, (hκI I v hvs).1, (hκI I v' hvs').2, inner_smul_left, inner_smul_right]
  congr 1
  simp only [RCLike.star_def]
  ring

end GlobalTheory.CellPieriG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselExteriorPowerConstantBoundLargeGap
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapWedgeKappaL

theorem n1_add_eZ_le_add_card' {n : ℕ} (ν : Fin n → ℤ) (I : Finset (Fin n)) : n1 (ν + eZ I) ≤ n1 ν + I.card := by
  unfold n1
  have h1 : ∑ i, (eZ I i).natAbs = I.card := by
    have : ∀ i, (eZ I i).natAbs = if i ∈ I then 1 else 0 := by
      intro i; unfold eZ; split_ifs <;> rfl
    simp [this]
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

theorem eZ_injective' {n : ℕ} : Function.Injective (eZ : Finset (Fin n) → Fin n → ℤ) := by
  intro I J h
  ext i
  have := congrFun h i
  unfold eZ at this
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

theorem kappa_bound : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hyp := hH.1
  have hSG := (_root_.GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hSG
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := n1_add_eZ_le_add_card' ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) l => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r l
  have hdual := fun J : Sub (2 * r + k + 1) l =>
    Gp91.GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (lb ν) hDS hDSJ hF hT hG
      (fun s hs => (_root_.GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length k r l hl z hG.1).1 s hs) (hSF ν hν0).1 hnz J
      (lb (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) l, ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, lb ν (ev (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • lb (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) l, 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg
    ((_root_.GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS)
  obtain ⟨w, hw, hw1, hint⟩ := _root_.GlobalTheory.MomProdGap.product_moment_first_gap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) l) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply eZ_injective'
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := Gp91.GlobalTheory.T.tensor_moment_weighted hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • lb ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • lb (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : lb (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hHs : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hHs] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(_root_.GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length k r l hl z hG.1).2 _ hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.GapWedgeKappaL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapMultipleIsometryLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchurGap

theorem schur_fdeg_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r),
    R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧
    ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : HCFdegG := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨c, hc, hF⟩ := hHC k r ε hQ
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hP hH μG hμ
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q) :=
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R (GlobalTheory.isDS_of_isDG hR) Q hQ
  obtain ⟨hd, hS⟩ := hF mu R.H _ hR.gap hR.hc hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v⟫_ℂ *
          star ⟪w', R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

theorem exists_mass_eq (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B : R.H → Wp} {w : R.H} (hc : c ≠ 0) (hDS : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hS : SideG k r z π u μW μN μG νq)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B) (hw : R.KFin w)
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0)
    (h1 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤) :
    ∃ a : ℝ≥0∞, ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨t, htG, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, htW, htψ⟩ := htz z hS.1
  obtain ⟨hS', hR⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π u c μW μN μG νq t htG htN htW htψ hS
  obtain ⟨hmul, hone, hinn, hsm, hTK, -, hKT, -, hcont⟩ :=
    GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r ε mu R hDS
  have hU : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) R.σ := by
    refine ⟨⟨?_, ?_⟩, fun g hg v => ?_, hcont⟩
    · ext v; simpa using hone v
    · intro a ha b hb; ext v; simpa using hmul a ha b hb v
    · have := hinn g hg v v
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
      have h2 : ‖R.σ g v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hB' := ((hR R hU).1 B).1 hB
  obtain ⟨htu, htinv, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r t htG
  have hdet : IsUnit t.det := (Matrix.isUnit_iff_isUnit_det t).mp htu
  have hae : ∀ {μN νq : Measure (Mt k r)}, SideG k r z π u μW μN μG νq →
      ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := fun hS => by
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
    obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hmove : ∀ v, PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j)
      (fun g => B (R.σ t (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) := fun v => by
    unfold PI.BesselPeriodGGP.l2SG
    rw [(GlobalTheory.BesselSchur.measurableEmbedding_lmul hdet).lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hae hS] with x hx
    have e : R.σ t (R.σ (t⁻¹ * Matrix.of x) v) = R.σ (Matrix.of x) v := by
      rw [← hmul t htG _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul htinv hx), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    exact congrArg (fun y => ((‖B y‖₊ : ℝ≥0∞)) ^ 2) e
  obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u _ _ _ _ hDG hgap hok hS'
  obtain ⟨v₁, hv₁, hlv⟩ := _root_.GlobalTheory.BesselPeriodNonzeroGap.exists_kFin_period_ne_zero hH k r ε mu h R Wp z π u _ _ _ _ _ l w hDS hgap hok hS' hB' hw
    (by rw [hmove]; exact h0) (by rw [hmove]; exact h1) hl
  obtain ⟨c₀, hc₀, hfd⟩ := schur_fdeg_gap hH.1 k r ε μG hS.2.2.2.2.2.2.1
  have hdd : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC mu := mul_pos hc₀ (GlobalTheory.BesselSchur.fdegHC_pos hDS.1.1)
  have hv₁s : v₁ ∈ R.sm := hTK _ (hKT _ hv₁)
  have hiso := Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u _ _ _ _ l _ hDG hgap hok hS' hl
    (hfd mu R hDG).1 ⟨v₁, hv₁s, hlv⟩
  obtain ⟨hb, hiso⟩ := hiso
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.GapLine.bessel_line_gap hH k r ε mu R Wp z π u _ _ _ _ _ _ hDG hS' hb
    ⟨v₁, hv₁s, smul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hdd).ne') hlv⟩ hB'
  refine ⟨(‖a‖₊ : ℝ≥0∞) ^ 2, fun v hv => ?_⟩
  have e : ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; rfl
  rw [← hmove, e, ← hiso v hv]
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae hS'] with x hx
  rw [ha _ (hsm _ hx v hv), nnnorm_smul, ENNReal.coe_mul, mul_pow]

theorem bessel_schur : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl →
    (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) →
    BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl hθ _ hZ τ w w' θ W hW A hA hT v hv
  have hθ0 := hθ τ w w' θ W hW
  have := FiniteDimensional.complete ℂ W.Wp
  have hU : ∀ i : Fin D.R.k, uOne D w τ (i.val + 1) = uS D w τ i := fun i => by
    unfold uOne
    rw [dite_eq_left ⟨by omega, i.isLt⟩]
    rfl
  obtain ⟨hnum, -, heps⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ hU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, hh, -⟩ := hnum
  rw [heps] at hgap
  have hgap' : GapAtLeast (epsSH D.R) (lamD D τ) ((D.R.r : ℝ) ^ 19 / 4) := fun a b hab =>
    le_trans (by have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
                 linarith) (hgap a b hab)
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvpos : 0 < D.host.v := by linarith
  obtain ⟨c1, -, z1, -, t1, -, hG, w1, -, -, -, hN, q1, -⟩ := hW
  obtain ⟨hpar, hds, b1, -, hsm, hv0, ⟨P, hP, hlow⟩, hc, l1, -, -⟩ := hA
  have hTz : 0 < Tz D.R.k D.R.rS W.z := by rw [t1]; exact hT
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.haarLie_isHaarOn_Nset _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hS : SideG D.R.k D.R.rS W.z W.π (uOne D w τ) W.μW W.μN W.μG W.νS :=
    ⟨z1, hTz, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 hTz c1 hU, w1, hNH, hG, q1⟩
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hvpos
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hcne : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hKF : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin A.v0 := by
    obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Formalism.REAL.Kset (epsSH D.R))
      (fun g => A.σ (P⁻¹ * g * P))
      (F := {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) (lowK (epsSH D.R) (lamD D τ)) S})
      (fun S hS => ⟨hS.1, hS.2.1⟩) hlow
    refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
    obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg
    have h := hst _ hK x hx
    simp only at h
    rwa [hback] at h
  have hnt : Nontrivial W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact hnt
  have hrk : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast Module.finrank_pos
  have l1' : PI.BesselPeriodGGP.l2SG W.νS (fun g => A.B (A.σ g A.v0)) =
      ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp) := l1
  obtain ⟨a, ha⟩ := exists_mass_eq hH (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) (B := A.B) (w := A.v0) hcne ⟨hpar, hds⟩
    hgap' hok hS (GlobalTheory.BesselSchur.isBesselMapSm_of b1) hKF
    (by rw [l1']; exact (ENNReal.ofReal_pos.2 (mul_pos hc hrk)).ne') (by rw [l1']; exact ENNReal.ofReal_ne_top)
  have e1 : l2SG W.νS (fun g => A.B (A.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := ha v hv
  have e2 : l2SG W.νS A.Φ = a * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 := ha A.v0 hsm
  rw [e1, e2]
  ring

end GlobalTheory.BesselSchurGap
end

