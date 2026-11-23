module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0407
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursionStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedStepsStatement
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWordGenericBound_of_normalisedSteps : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC → StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_pinned | exact GlobalTheory.SnPos.rowMainEqP_of_pinned | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_pinned <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGoodLocalDatumOfNonzeroPeriodsGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodLocalDatum_of_nonzero_periods_gap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDG (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriodsGap.exists_goodS | exact GlobalTheory.DatumOfPeriodsGap.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriodsGap.exists_goodS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizerStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  first
  | exact GlobalTheory.DblCos.finite_double_cosets
  | intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
    exact GlobalTheory.DblCos.finite_double_cosets D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀.toIsLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCellOrbitalIntegralRankOneKFiniteStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_cellOrbitalIntegral_rankOne_kFinite : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  first | exact @GlobalTheory.CellOrbIntG.orbInt_integrable | exact GlobalTheory.CellOrbIntG.orbInt_integrable | (intros; apply GlobalTheory.CellOrbIntG.orbInt_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralAmplitudeNormSqBigCellGapStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_amplitudeNormSq_bigCell_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  first | exact @GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | exact GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap | (intros; apply GlobalTheory.AmpNormGap.lintegral_hsNormSq_amp_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenus
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanRow

theorem num_mid (a b mk M de N C f : ℝ) (j s : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hmk : 0 < mk) (hde : 1 ≤ de)
    (hN : 1 ≤ N) (hC : 16 ≤ C) (hf : 1 ≤ f) (hs : 2 ≤ s) (hM : mk * N ^ (j + s - 1) ≤ M) :
    a * b * (de ^ 2) ^ ((j : ℝ) / 2) * (de ^ 2 * N ^ 2) ^ ((9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f)) / 2) ≤
      M * ((de / N) ^ (j + s) * (de * N) ^ (C * s + C * Real.log f) * (b * a / mk)) := by
  have hd0 : 0 < de := by linarith
  have hN0 : 0 < N := by linarith
  have hx : 1 ≤ de * N := by nlinarith
  have hx0 : 0 < de * N := by linarith
  have e1 : (de ^ 2) ^ ((j : ℝ) / 2) = de ^ j := by
    rw [← Real.rpow_natCast de 2, ← Real.rpow_mul hd0.le, ← Real.rpow_natCast de j]
    congr 1; push_cast; ring
  have e2 : ∀ E : ℝ, (de ^ 2 * N ^ 2) ^ (E / 2) = (de * N) ^ E := fun E => by
    rw [← mul_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have hl : 0 ≤ Real.log f := Real.log_nonneg hf
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hlb : Real.logb 2 (2 * f) ≤ 1 + 2 * Real.log f := by
    have h2 := Real.log_two_gt_d9
    rw [Real.logb, Real.log_mul (by norm_num) (by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have hE : (9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f)) + 1 ≤ C * s + C * Real.log f := by nlinarith
  have h3 := Real.rpow_le_rpow_of_exponent_le hx hE
  rw [Real.rpow_add_one hx0.ne'] at h3
  rw [e1, e2]
  set X := (de * N) ^ (9 * (s : ℝ) + 8 + 4 * Real.logb 2 (2 * f))
  set Y := (de * N) ^ (C * s + C * Real.log f)
  have hX : 0 ≤ X := Real.rpow_nonneg hx0.le _
  have hY : 0 ≤ Y := Real.rpow_nonneg hx0.le _
  have h4 : X * N ≤ Y := le_trans (mul_le_mul_of_nonneg_left (by nlinarith) hX) h3
  have h5 : de ^ j ≤ de ^ (j + s) := pow_le_pow_right₀ hde (by omega)
  have e3 : N ^ (j + s) = N ^ (j + s - 1) * N := by rw [← pow_succ]; congr 1; omega
  calc a * b * de ^ j * X ≤ a * b * de ^ (j + s) * (Y / N) := by
        have : X ≤ Y / N := (le_div_iff₀ hN0).2 h4
        gcongr
    _ = (mk * N ^ (j + s - 1)) * ((de / N) ^ (j + s) * Y * (b * a / mk)) := by
        rw [div_pow, e3]; field_simp
    _ ≤ _ := by gcongr

theorem num_top (c₀ C L rd HH de N E : ℝ) (k m f : ℕ) (hc : 0 < c₀) (hC : 16 ≤ C) (hC' : 1 / c₀ ≤ C) (hL : 0 ≤ L)
    (hrd : 1 ≤ rd) (hrd' : Real.log rd ≤ L / c₀) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hH : Real.exp L ^ (C * (m : ℝ) ^ 2 * f) ≤ HH) (hde : 1 ≤ de) (hN : 1 ≤ N) (hE : 0 ≤ E) :
    (9 * rd) ^ (k * f) * de ^ k ≤ (de / N) ^ k * (de * N) ^ E * ((C * k) ^ (k * f) * (HH * N) ^ (C * k)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf' : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have hN0 : 0 < N := by linarith
  have h1 : rd ^ f ≤ HH := by
    refine le_trans ?_ hH
    rw [← Real.exp_mul, ← Real.exp_log (show 0 < rd by linarith), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have a1 : L / c₀ ≤ L * C := by
      rw [div_eq_mul_one_div]; gcongr
    have a2 : L * C ≤ L * C * (m : ℝ) ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
    calc (f : ℝ) * Real.log rd ≤ f * (L * C * (m : ℝ) ^ 2) := by gcongr; linarith
      _ = _ := by ring
  have h0 : 1 ≤ rd ^ f := one_le_pow₀ hrd
  have h2 : (rd ^ f * N) ^ k ≤ (HH * N) ^ (C * k) := by
    calc (rd ^ f * N) ^ k ≤ (HH * N) ^ k := by gcongr
      _ = (HH * N) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by nlinarith)
  have h3 : 1 ≤ (de * N) ^ E := Real.one_le_rpow (by nlinarith) hE
  have h4 : (9 : ℝ) ^ (k * f) ≤ (C * k) ^ (k * f) := by gcongr; nlinarith
  calc (9 * rd) ^ (k * f) * de ^ k = (de / N) ^ k * 1 * (9 ^ (k * f) * (rd ^ f * N) ^ k) := by
        rw [div_pow, mul_pow, mul_pow, ← pow_mul, mul_comm f k]; field_simp
    _ ≤ _ := by gcongr

section General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [FiniteDimensional K V] in
theorem disc_of_equiv (h : V →ₗ⋆[K] V →ₗ[K] K) (N : Submodule (𝓞 K) V) (T : ℕ)
    (e : (↥(dual h N) ⧸ N.comap (dual h N).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) :
    discN h N = T ^ Module.finrank ℚ K ∧ Cnt.DiscGen h N 1 := by
  constructor
  · have e1 : discN h N = Nat.card (↥(dual h N) ⧸ N.comap (dual h N).subtype) := rfl
    rw [e1, Nat.card_congr e.toEquiv, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank]
    simp
  · refine ⟨{e.symm 1}, by simp, ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e x)
    rw [Finset.coe_singleton, Submodule.mem_span_singleton]
    refine ⟨r, e.injective ?_⟩
    rw [map_smul, e.apply_symm_apply, ← hr, Algebra.smul_def, mul_one]
    rfl

end General

theorem finrank_E {R : Ranks} (H : Host R) : Module.finrank ℚ H.E = 2 * R.f := by
  rw [H.finrank_cmField]
  simp only [Ranks.f, Ranks.n]
  ring

theorem fDeg_E (D : D7) : fDeg D.host.E = D.R.f := by
  let _ := D.host.cmStar
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := D.host.E)
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
  have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 := by
    rw [NumberField.nrRealPlaces_eq_zero_iff]; infer_instance
  have h4 := finrank_E D.host
  unfold fDeg
  omega

theorem vInv_E (D : D7) : 2 * vInv D.host.E = D.host.rdE := by
  unfold vInv Host.rdE
  rw [fDeg_E, finrank_E]
  push_cast
  ring

theorem one_le_rdE (D : D7) : 1 ≤ D.host.rdE := by
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem main : ∀ c₀ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), c₀ ≤ Cl → UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  intro c₀ hc₀
  refine ⟨max 16 (1 / c₀), fun C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl => ?_⟩
  letI := D.host.cmStar
  intro hyp F0 he hz Λ hΛ reps hreps s hs2 hsk de hde HH hHH
  have hC1 : 16 ≤ C := le_trans (le_max_left _ _) hC
  have hC2 : 1 / c₀ ≤ C := le_trans (le_max_right _ _) hC
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hS0, -, -⟩, ⟨-, hTp, -, -, -, hTs, -⟩, -⟩ := hyp
  have hrd : Real.log D.host.rdE ≤ large₂.sc.L / Cl := hS0.2.2.2.2.2.2.2.2.2.2.1
  have hL : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hrd' : Real.log D.host.rdE ≤ large₂.sc.L / c₀ := hrd.trans (by gcongr)
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ hΛ
  have hM := (GlobalTheory.T.mass_rowLattice_orthogonal_split_prime D u F0 he hz hTp hTs Λ hΛ).2
  have hs := (D.sp.X 0).herm
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  generalize Lat.L0X D Λ (lf D F0) = L₀ at *
  set h := (D.sp.X 0).hT with hh
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = Lat.Tu D u ^ (2 * D.R.f) ∧
      (∃ t : Finset (D.sp.X 0).V, t.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (t : Set (D.sp.X 0).V)) := fun L hL => by
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := disc_of_equiv h L _ e
    exact ⟨a, by rw [b, finrank_E], ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c⟩
  have hlhs : (∑ L' ∈ reps, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h L') : ℝ))⁻¹ *
      (Cnt.cntPrim h L' (D.R.k - s) de : ℝ≥0∞)) =
      orbSum (isom h) (genus h L₀) (fun L => (((primSp h L (D.R.k - s) (de ^ 2)).encard : ℕ∞) : ℝ≥0∞)) := by
    rw [← hsum reps _ hreps fun g M => by
      rw [(GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg g M ⊥ _ _).2]]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD M (hmem M (hreps.1 M hM)).1).2.2.1]
  rw [hlhs]
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.n := D.R.ord_pos
    have h1 : D.R.f = 2 * D.R.n := rfl
    omega
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hde' : (1 : ℝ) ≤ de := by exact_mod_cast hde
  have hde2 : 1 ≤ de ^ 2 := Nat.one_le_pow _ _ hde
  have hN : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  by_cases hmid : s ≤ D.R.k - 2
  · have H := GlobalTheory.Mass.PrimMean.main _root_.GlobalTheory.Mass.MaxFormula.main _ _ h hK hs hPD (_root_.GlobalTheory.Mass.exists_orthoLattice_of_unimodular _ hK) (D.R.k - s) s (by omega)
      (by omega) (by omega) _ _ _ (hU (D.R.k - s)).1 (hU (D.R.k - s)).2.1 _ _ _ (hU s).1 (hU s).2.1 (de ^ 2) _ hde2
      (Nat.one_le_pow _ _ hTp.pos) _ hst hmem
    refine H.trans (ENNReal.ofReal_le_ofReal ?_)
    have e1 : D.R.k - s + s = D.R.k := by omega
    have H2 := num_mid _ _ _ (mass h L₀) de _ C D.R.f (D.R.k - s) s (hU (D.R.k - s)).2.2.1.le (hU s).2.2.1.le
      (hU D.R.k).2.2.1 hde' hN hC1 hf' hs2 (by rw [e1]; exact hM)
    rw [e1] at H2
    have e2 : ((Lat.Tu D u ^ (2 * D.R.f) : ℕ) : ℝ) = Cnt.NT D u ^ 2 := by
      rw [Cnt.NT, ← pow_mul, mul_comm D.R.f]; push_cast; rfl
    rw [e2, finrank_E, Cnt.XiS, Cnt.Xi, if_pos ⟨hs2, hmid⟩]
    push_cast
    exact H2
  · have hk : 1 ≤ D.R.k := by omega
    have H2 := num_top c₀ C large₂.sc.L D.host.rdE HH de (Cnt.NT D u) (C * s + C * Real.log D.R.f) D.R.k D.R.m D.R.f
      hc₀ hC1 hC2 hL (one_le_rdE D) hrd' hk (le_trans one_le_two D.R.two_le_m) hHH hde' hN
      (by have := Real.log_nonneg hf'; positivity)
    obtain ⟨o1, o2, -⟩ := GlobalTheory.Mass.OrbMono.main (isom h) (Submodule (𝓞 D.host.E) (D.sp.X 0).V)
    refine (o1 _ _ _ (fun _ => ENNReal.ofReal ((9 * D.host.rdE) ^ (D.R.k * D.R.f) * (de : ℝ) ^ D.R.k))
      subset_rfl fun L hL => ?_).trans ?_
    · obtain ⟨p1, p0⟩ := GlobalTheory.Mass.PrimCount.main _ _ h hK hs hPD L (hmem L hL).1 _ hde2
      rcases (by omega : D.R.k - s = 1 ∨ D.R.k - s = 0) with e | e
      · rw [e]
        refine p1.trans (le_of_eq ?_)
        rw [vInv_E, fDeg_E, hrk]
        congr 2
        push_cast
        rw [← Real.rpow_natCast (de : ℝ) 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast (de : ℝ) D.R.k]
        congr 1; push_cast; ring
      · rw [e]
        refine le_trans (b := 1) (by exact_mod_cast p0) (ENNReal.one_le_ofReal.2 ?_)
        have := one_le_rdE D
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ hde')
    · rw [o2, ← hm1, mul_comm, ← ENNReal.ofReal_mul hm2.le]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hm2.le)
      rw [Cnt.XiS, Cnt.Xi, if_neg (fun a => hmid a.2), if_pos (by omega)]
      exact H2

end GlobalTheory.Mass.PrimMeanRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstantsStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  first | exact @GlobalTheory.BesselMoveGap.bessel_move_gap | exact GlobalTheory.BesselMoveGap.bessel_move_gap | (intros; apply GlobalTheory.BesselMoveGap.bessel_move_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProductMomentFirstLengthsLowestVector
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomProdGap

theorem product_moment_first_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν hNz
  have hSG := (_root_.GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  obtain ⟨hG, -, -, -⟩ := hH
  have hKS : PI.KFinSmooth := by
    unfold BranchingSupport.HypsG BranchingSupport.InputsG at hG
    exact hG.1.2.2.1
  obtain ⟨hN, hFam, hSd, hSF⟩ := hS
  have hk : 1 ≤ k := by
    unfold BranchingSupport.Num at hN
    exact hN.1
  have hz : Formalism.QuantumDeterminants.inWb k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.1
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := by
    unfold BranchingSupport.SideG at hSd
    exact hSd.2.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  have hDS : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    unfold BranchingSupport.IsFam at hFam
    exact hFam ν' h'
  have hDG : ∀ ν' : Fin (2 * r + k + 1) → ℤ, n1 ν' ≤ q0 →
      (R ν').IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν' a : ℝ)) := by
    intro ν' h'
    have h2 := hSG
    unfold BranchingSupport.SetupG BranchingSupport.IsFamG at h2
    exact h2.2.1 ν' h'
  obtain ⟨Q, hQ⟩ := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).1 hk
  have hQu : IsUnit Q := by
    unfold PI.UpqRep.IsCayleyU at hQ
    exact ⟨⟨Q, star Q, Matrix.mem_unitaryGroup_iff.mp hQ.2, Matrix.mem_unitaryGroup_iff'.mp hQ.2⟩, rfl⟩
  have hEx : ∀ ν' : Fin (2 * r + k + 1) → ℤ, ∃ E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E' ∧ Formalism.REAL.GlRel E' := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E', h1, h2⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hKS k r _ _ (R ν') (hDS ν' h') Q hQu
      exact ⟨E', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hEx
  obtain ⟨w, hw1, -, hKH, hfin⟩ := GlobalTheory.T.exists_lowest_kFinite_vector_discreteSeries hKS k r _ _ (R ν) (hDS ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hMod := Gp91.GlobalTheory.isMod_smooth_of_isDS hG k r _ _ (R ν) hk (hDG ν hν0) Q (E ν) hQ (hE ν hν0).1
  have hLev : BranchingSupport.Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w := by
    unfold BranchingSupport.IsMod at hMod
    exact GlobalTheory.lev_zero_of_kHighest _ _ _ _ _ _ hMod.1 hMod.2.1 hKH hfin
  have hq4 : ∀ q ≤ (r + 1) ^ 2, 0 + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 := by
    intro q hq
    have h1 : (r + 1) ^ 2 ≤ (2 * r + k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hA : ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) *
      (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) ^ q) := by
    intro q hq
    have h1 := Gp91.GlobalTheory.Moment.moment_first_length hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') q ν (le_trans (Nat.add_le_add_left hq _) hν) 0 (hq4 q hq) w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hRr : ∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ /
      lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤
      ENNReal.ofReal ((b ^ 2) ^ (2 * q)) := by
    intro a q hq
    have h1 := Gp91.GlobalTheory.RatioMoment.ratio_moment hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ
      (fun ν' h' => hE ν' h') ν hν0 0 q (hq4 q hq) a w hLev
    rwa [hw1, one_pow, mul_one] at h1
  have hdg : 0 < dg ν := (hSF ν hν0).2.1
  have hmass : ∫⁻ x, ENNReal.ofReal (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ∂νq = 1 := by
    have h1 := ((Gp91.GlobalTheory.MomMass.mom_mass hG k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν0).2
      hNz).2 (w : (R ν).H) w.2
    simp only [one_mul] at h1
    rw [h1]
    have h2 : ‖(w : (R ν).H)‖ = 1 := hw1
    rw [h2, one_pow, ENNReal.ofReal_one]
  obtain ⟨hae, -, hlenM, hbesM⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKS k r _ _ (R ν) Wp z π u μW μN μG νq (hDS ν hν0) hSd
  obtain ⟨hIsBes, -⟩ := (hSF ν hν0).1
  have hPhM : AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) νq :=
    ((hbesM (lb ν) hIsBes (w : (R ν).H) w.2).norm.aemeasurable.pow_const 2).const_mul (dg ν)
  have hpos : ∀ a, ∀ᵐ x ∂νq, 0 < lenA k r z (Matrix.of x) a := fun a =>
    hae.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hz hT (Matrix.of x) hx).2.2.1 a
  have hnf := (GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN).1
  have hb1 : 1 ≤ b := by
    have h1 := hnf.2.2.1
    have h2 : (0 : ℝ) ≤ 2 * r + k := by positivity
    linarith
  have hbv : 0 ≤ bv := by linarith [hnf.2.1]
  have hA0 : 0 ≤ ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hT.le (by positivity))) (pow_nonneg (by linarith) _)
  have key := _root_.GlobalTheory.MomentHolder.initial_product_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r l hl (fun a x => lenA k r z (Matrix.of x) a)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2) ((2 * r + k + 1 : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2) (fun a => hlenM a) hpos hPhM
    (fun x => mul_nonneg hdg.le (sq_nonneg _)) hmass hA0 (one_le_pow₀ hb1) hA hRr
  refine ⟨(w : (R ν).H), w.2, hw1, le_trans key (ENNReal.ofReal_le_ofReal ?_)⟩
  exact pow_le_pow_left₀ (mul_nonneg hA0 (by positivity))
    (_root_.GlobalTheory.MomNum.mom_num k r lam u b bv ga h q0 _ hN hT) l

end GlobalTheory.MomProdGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExistStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevantLift_normalisedData_exist : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' := by
  first | exact @GlobalTheory.pinAll_all | exact GlobalTheory.pinAll_all | (intros; apply GlobalTheory.pinAll_all <;> assumption)
end

