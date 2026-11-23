module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuperposSmooth

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def dl (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (u : RW T S) (F : WO S T → ℂ) :
    WO S T → ℂ :=
  fun y => deriv (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F y) 0

def bas (S T : HSp D) : Module.Basis (Fin (Module.finrank ℝ (RW T S))) ℝ (RW T S) := Module.finBasis ℝ (RW T S)

def coordC (S T : HSp D) (i : Fin (Module.finrank ℝ (RW T S))) : RW T S →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap ((bas S T).coord i)).smulRight (1 : ℂ)

theorem clm_expand (φ : RW T S →L[ℝ] ℂ) : φ = ∑ i, φ (bas S T i) • coordC S T i := by
  ext u
  have e : φ u = ∑ i, (bas S T).repr u i • φ (bas S T i) := by
    conv_lhs => rw [← (bas S T).sum_repr u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

theorem norm_heisO_le (hψ : IsStdChar D ψ (-1)) (x : WO S T) {G : WO S T → ℂ} {C : ℝ} (hC : ∀ y, ‖G y‖ ≤ C)
    (w : WO S T) : ‖heisO ψ S T x G w‖ ≤ C := by
  unfold heisO
  rw [norm_mul, hψ.1.2.1, one_mul]
  exact hC _

theorem theta_dl (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (u : RW T S) : IsThetaFunO ψ S T (dl ψ σ S T u F) := by
  obtain ⟨L, hL, hLe⟩ := (smooth_iff_sm_and_real_lines D θ σ h T S).2.2 u
  have e : dl ψ σ S T u F = dLine ψ S T L F := by
    funext y
    unfold dl dLine
    simp only [hLe]
  rw [e]
  exact theta_dLine h.inf hψ hL hF

def sco (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (F : WO S T → ℂ) (u z : RW T S)
    (w : WO S T) : ℂ :=
  (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * heisO ψ S T (iotaW σ T S z) F w +
    heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) w

theorem hasFDerivAt_pt (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (w : WO S T) (c : ℂ) (z : RW T S) :
    HasFDerivAt (fun z : RW T S => c * heisO ψ S T (iotaW σ T S z) F w)
      (∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i) z := by
  have hs := _root_.GlobalTheory.ThetaTranslate.contDiff_heisO_iota_fderiv D θ σ h ψ hψ S T F hF w
  have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z) z :=
    ((hs.1.differentiable (by simp)) z).hasFDerivAt
  have e : c • fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z =
      ∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i := by
    rw [clm_expand (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hs.2 z (bas S T i)]
    rfl
  rw [← e]
  exact hd.const_mul c

theorem aesm_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (z : RW T S) :
    AEStronglyMeasurable (fun x => heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  exact ((theta_heisO_real h.inf hψ (h.real_iota T S z) hG).cont.measurable.comp hv).aestronglyMeasurable

theorem integrable_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z : RW T S) :
    Integrable (fun x => a x * heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G hG
  exact ha.mul_bdd (aesm_heisO h hψ hG μ hv z) (Filter.Eventually.of_forall fun x => norm_heisO_le hψ _ hC _)

theorem aesm_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (u z : RW T S) :
    AEStronglyMeasurable (fun x => sco ψ σ S T F u z (v x)) μ :=
  ((aesm_heisO h hψ hF μ hv z).const_mul _).add (aesm_heisO h hψ (theta_dl h hψ hF u) μ hv z)

theorem integral_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (u z : RW T S) :
    Integrable (fun x => a x * sco ψ σ S T F u z (v x)) μ ∧
      ∫ x, a x * sco ψ σ S T F u z (v x) ∂μ =
        (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) +
          ∫ x, a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) ∂μ := by
  have e : (fun x => a x * sco ψ σ S T F u z (v x)) = fun x =>
      (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (a x * heisO ψ S T (iotaW σ T S z) F (v x)) +
        a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) := by
    funext x; unfold sco; ring
  have i1 := (integrable_heisO h hψ hF μ hv ha z).const_mul ((Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ))
  have i2 := integrable_heisO h hψ (theta_dl h hψ hF u) μ hv ha z
  rw [e]
  exact ⟨i1.add i2, by rw [integral_add i1 i2, integral_const_mul]⟩

theorem hasFDerivAt_superpos (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z₀ : RW T S) :
    HasFDerivAt (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ)
      (∑ i, ((Real.pi * Complex.I) * ((omO S T z₀ (bas S T i) : ℝ) : ℂ) *
          (∫ x, a x * heisO ψ S T (iotaW σ T S z₀) F (v x) ∂μ) +
        ∫ x, a x * heisO ψ S T (iotaW σ T S z₀) (dl ψ σ S T (bas S T i) F) (v x) ∂μ) • coordC S T i) z₀ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hCd : ∀ i, ∃ C' : ℝ, ∀ y, ‖dl ψ σ S T (bas S T i) F y‖ ≤ C' := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ (theta_dl h hψ hF (bas S T i))
  choose Cd hCd using hCd
  have hM : ∀ i, ∃ M : ℝ, ∀ z ∈ Metric.closedBall z₀ 1, ‖omO S T z (bas S T i)‖ ≤ M := fun i =>
    (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
      (LinearMap.continuous_of_finiteDimensional ((omO S T).flip (bas S T i))).continuousOn
  choose M hM using hM
  have hsco : ∀ i, ∀ z ∈ Metric.ball z₀ 1, ∀ w,
      ‖sco ψ σ S T F (bas S T i) z w‖ ≤ Real.pi * M i * C + Cd i := by
    intro i z hz w
    unfold sco
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_heisO_le hψ _ (hCd i) w))
    rw [norm_mul, norm_mul]
    have h1 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by simp [Real.pi_pos.le]
    have h2 : ‖((omO S T z (bas S T i) : ℝ) : ℂ)‖ ≤ M i := by
      rw [Complex.norm_real]; exact hM i z (Metric.ball_subset_closedBall hz)
    have h3 := norm_heisO_le hψ (iotaW σ T S z) hC w
    rw [h1]
    have hM0 : 0 ≤ M i := (norm_nonneg _).trans h2
    gcongr
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun z x => a x * heisO ψ S T (iotaW σ T S z) F (v x))
    (F' := fun z x => ∑ i, (a x * sco ψ σ S T F (bas S T i) z (v x)) • coordC S T i)
    (bound := fun x => ‖a x‖ * ∑ i, (Real.pi * M i * C + Cd i) * ‖coordC S T i‖) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (ha.aestronglyMeasurable.mul (aesm_heisO h hψ hF μ hv z)))
    (integrable_heisO h hψ hF μ hv ha z₀)
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (ha.aestronglyMeasurable.mul (aesm_sco h hψ hF μ hv (bas S T i) z₀)).smul_const _)
    (Filter.Eventually.of_forall fun x z hz => by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, norm_mul, mul_assoc]
      gcongr
      exact hsco i z hz (v x))
    (ha.norm.mul_const _)
    (Filter.Eventually.of_forall fun x z _ => hasFDerivAt_pt h hψ hF (v x) (a x) z)
  refine key.congr_fderiv ?_
  rw [integral_finsetSum _ fun i _ => (integral_sco h hψ hF μ hv ha (bas S T i) z₀).1.smul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_const, (integral_sco h hψ hF μ hv ha (bas S T i) z₀).2]

theorem contDiff_superpos_nat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ} (ha : Integrable a μ) (n : ℕ) :
    ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
      ContDiff ℝ n (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) := by
  induction n with
  | zero =>
    intro F hF
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
      (hasFDerivAt_superpos h hψ hF μ hv ha z).continuousAt)
  | succ n ih =>
    intro F hF
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, fun z => hasFDerivAt_superpos h hψ hF μ hv ha z⟩
    refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
    have hom : ContDiff ℝ n fun z : RW T S => ((omO S T z (bas S T i) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (LinearMap.toContinuousLinearMap ((omO S T).flip (bas S T i))).contDiff
    exact ((contDiff_const.mul hom).mul (ih F hF)).add (ih _ (theta_dl h hψ hF (bas S T i)))

end GlobalTheory.SuperposSmooth

theorem GlobalTheory.SuperposSmooth.main : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  intro D θ σ h ψ hψ S T F hF Ω _ μ v a hv ha
  exact contDiff_infty.2 fun n => GlobalTheory.SuperposSmooth.contDiff_superpos_nat h hψ μ hv ha n F hF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem closeR_mono {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {u : GA D V} {a a' : ℝ} (h : CloseR θ V u a) (hle : a ≤ a') : CloseR θ V u a' :=
  ⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩

theorem cuspDecayBound : GlobalTheory.Published.CuspDecayBound := by
  intro D θ hθ V U hU A N
  let Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ :=
    fun p f => Rder θ V p.1 p.2 f
  let 𝓒 : Set (GA D V → ℂ) := {φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧
    (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}
  obtain ⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩ := _root_.GlobalTheory.CuspGeo.MeanValue.mean_value D θ hθ V
  obtain ⟨b, Cn, δn, hδn, hnear⟩ := GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀
  have hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒 := by
    rintro ψ ⟨ha, hlev, hs, hg, hc⟩ i hi
    exact _root_.GlobalTheory.CuspStab.rder_stab D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) →
      ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒 := by
    intro l
    induction l with
    | nil => intro _ ψ hψ; exact hψ
    | cons a l ih =>
      intro hl ψ hψ
      exact hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)
  set Cn' := max Cn 0 with hCn'
  have hCn'0 : 0 ≤ Cn' := le_max_right _ _
  set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδn (div_pos hδ₁ (by linarith))
  set K := max (max Cn (Cm * Cn')) (max H 1) with hK
  have hK1 : Cn ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : Cm * Cn' ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : H ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨
      ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧
        GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧
      ∀ ψ ∈ 𝓒, ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ K * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ0, hδ1, hq, hcase⟩ := hnear g
    refine ⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩
    by_cases hδ : δ₀ ≤ δ
    · exact Or.inl hδ
    right
    push_neg at hδ
    have hδn' : ¬ δn ≤ δ := fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)
    obtain ⟨r, C₀, hC₀, hN⟩ := hcase.resolve_left hδn'
    have hsmall : Cn' * δ ≤ δ₁ := by
      have h1 : δ < δ₁ / (Cn' + 1) := hδ.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    refine ⟨(g * ·) '' Ω₀, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hq0 := GlobalTheory.Grow.one_le_quotHeight V g
      have hq1 := GlobalTheory.Grow.one_le_quotHeight V (g * w)
      have hw1 := hH w hw
      constructor
      · calc GlobalTheory.Grow.quotHeight V (g * w) ≤ GlobalTheory.Grow.quotHeight V g * GlobalTheory.Grow.height V w :=
              GlobalTheory.Grow.quotHeight_mul_le V g w
          _ ≤ GlobalTheory.Grow.quotHeight V g * K := mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V g := mul_comm _ _
      · calc GlobalTheory.Grow.quotHeight V g = GlobalTheory.Grow.quotHeight V (g * w * w⁻¹) := by rw [mul_inv_cancel_right]
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * GlobalTheory.Grow.height V w⁻¹ := GlobalTheory.Grow.quotHeight_mul_le V _ _
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * K := by
              rw [GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _
    · rintro ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'
      have hsum : 0 ≤ ∑ i ∈ B, c i := Finset.sum_nonneg fun i hi => (hc' i hi).1
      have hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p := by
        refine _root_.GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_
        obtain ⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩ := hN m hm
        have hval : ψ (m * g) = ψ (g * u) := by
          rw [hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]
        rw [hval]
        refine hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall
          (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_
        exact (hc' p hp).2 _ ⟨w, hw, rfl⟩
      refine hmain.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum
  obtain ⟨L, C', hLB, hL⟩ := _root_.GlobalTheory.iterated_gain_rapid_decay (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B
    (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N
  refine ⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩
  intro φ ha hlev hs hg hc c hcl g
  have hφ : φ ∈ 𝓒 := ⟨ha, hlev, hs, hg, hc⟩
  have h := hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' =>
    GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.CuspGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbFColFormMemMram
section
noncomputable section

namespace GlobalTheory.Core.ColRam

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (u : B.Word) (a : I.ι)


include h in
theorem col_smul (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (g : (I.stp u a 0).G b) (p : (I.stp u a 0).D b) :
    φ.1 ((I.stp u a 0).act b g p).1.1.deco = (I.stp u a 0).rho B.fields.emb (lamT (B.hcW u) 0) b g (φ.1 p.1.1.deco) :=
  StepZero.form_smul ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (StepZero.levGAt_zero (I.Tp a) (h.idx_ok a))
    (StepZero.levQAt_zero (I.Tp a) (h.idx_ok a)) φ b g p

variable (hf : ((I.stp u a 0).fam B.fields.emb (lamT (B.hcW u) 0)).Ok)

def colForm : ColsK I u →ₗ[B.fields.K] (I.stp u a 0).FormsK B.fields.emb (lamT (B.hcW u) 0) hf where
  toFun φ := ⟨fun c => φ.1 ((I.stp u a 0).rep c).1.1.deco, fun c g =>
    (col_smul I h u a φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem colForm_eq_zero (φ : ColsK I u) (h0 : colForm I h u a hf φ = 0) : φ = 0 := by
  apply Subtype.ext
  funext d
  obtain ⟨p, rfl⟩ := StepZero.exists_pt (Q := I.Q a) (StepZero.ysAt_zero (R := B.R) I.sel (I.tup a) (I.cst a)) d
  let b : Idx I.sel (I.tup a) (I.idx a) 0 := (StepZero.idxUnique (h.idx_ok a)).default
  have h1 : φ.1 ((I.stp u a 0).rep ((I.stp u a 0).cl b p)).1.1.deco = 0 :=
    congrFun (congrArg Subtype.val h0) ((I.stp u a 0).cl b p)
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  exact h2.trans ((congrArg _ h1).trans (map_zero _))

theorem trTo_colForm (φ : ColsK I u) (b : Idx I.sel (I.tup a) (I.idx a) 0) (p : (I.stp u a 0).D b) :
    (I.stp u a 0).trTo B.fields.emb B.embLL b p
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ((I.stp u a 0).cl b p)) =
      evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL
        (φ.1 p.1.1.deco) := by
  have h2 := col_smul I h u a φ b ((I.stp u a 0).mv b p) ((I.stp u a 0).rep ((I.stp u a 0).cl b p))
  rw [show (I.stp u a 0).act b _ _ = p from (I.stp u a 0).mv_smul b p] at h2
  refine Eq.trans ?_ (congrArg _ h2).symm
  exact (GStep.evV_rho_eq_tr (I.stp u a 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) b _ _).symm

theorem embF_colForm_diaOp (P : (B.primes X).vT u) (e : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ)) =
      (I.atIn u a).diaLin B.fields.emb B.embLL P e
        ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) := by
  funext c
  refine Eq.trans ?_ (trTo_colForm I h u a hf φ c.1 (((I.atIn u a).A 0).diaPt P e c)).symm
  have e1 : (((I.atIn u a).A 0).diaPt P e c).1.1.deco = DecoSet.dia1 P e ((I.stp u a 0).rep c).1.1.deco :=
    congrArg (fun q => q.1.1.deco) (PtY.mv_dia ((I.stp u a 0).rep c) P e)
  rw [e1]
  exact congrArg (evV B.fields.emb (1 : Matrix (Fin (B.R.N 0)) (Fin (B.R.N 0)) B.fields.E) (lamT (B.hcW u) 0) B.embLL)
    (LocOp.ofMap_op_apply _ _ _ _ _ φ _)

theorem embF_colForm_mem_Mram (l : I.Laws) (φ : ColsK I u) :
    (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ) ∈ (I.atT l u a).Mram ↔
      φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have key : ∀ P : (B.primes X).vT u, (I.atT l u a).Nm P
      ((I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf φ)) =
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf
        (colForm I h u a hf (NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ)) := by
    intro P
    have e : NmOp (Pr := B.primes X) B.wts I.Ch u 0 P φ =
        ∑ e ∈ @Finset.univ _ (Fintype.ofFinite (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ), diaOp (Pr := B.primes X) B.wts I.Ch u 0 P e φ :=
      LinearMap.sum_apply _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, map_sum]
    refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr (Finset.ext fun e => ?_) fun e _ => ?_)
    · exact iff_of_true (@Finset.mem_univ _ (_) _) (@Finset.mem_univ _ (_) _)
    · exact (embF_colForm_diaOp I h u a hf P e φ).symm
  have hz : ∀ ψ : ColsK I u,
      (I.stp u a 0).embF B.fields.emb B.embLL (lamT (B.hcW u) 0) hf (colForm I h u a hf ψ) = 0 ↔ ψ = 0 := fun ψ =>
    (map_eq_zero_iff _ (StepZero.embF_injective _ _ _ _ hf)).trans
      ⟨colForm_eq_zero I h u a hf ψ, fun h0 => by rw [h0]; exact map_zero _⟩
  constructor
  · intro hm
    refine (Submodule.mem_iInf _).2 fun P => (hz _).1 ?_
    exact (key P).symm.trans ((Submodule.mem_iInf _).1 hm.2 P)
  · intro hm
    refine ⟨StepZero.embF_mem_Fi _ _ _ _ hf _, (Submodule.mem_iInf _).2 fun P => ?_⟩
    exact (key P).trans ((hz _).2 ((Submodule.mem_iInf _).1 hm P))

theorem isCol_mem_ramSub_iff {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (_hX : B.fields.Ok) (l : I.Laws)
    (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u) (hc : IsCol I u a l x φ) :
    x ∈ (I.fm l u a).ramSub ↔ φ ∈ MramV (Pr := B.primes X) B.wts I.Ch u := by
  have hx : x = colForm I h u a ((l.fmL u a).fam 0) φ := Subtype.ext (funext hc)
  rw [hx]
  exact embF_colForm_mem_Mram I h u a ((l.fmL u a).fam 0) l φ

end GlobalTheory.Core.ColRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = v)
  have hMsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.exists_integral_trace_idempotent_at_tamePlace D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := GlobalTheory.T.exists_isotropic_dual_columns_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := GlobalTheory.T.exists_unitarySupportedAtPlace_of_dual_isotropic_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := _root_.GlobalTheory.IwaDecomp.selfDual_split D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteVectorsDiscreteSeriesSmoothAbsolutelyIrreStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_vectors_discrete_series_smooth_absolutely_irreducible : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ), GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  first | exact @GlobalTheory.KFinLoc.kFin_smooth_absIrr | exact GlobalTheory.KFinLoc.kFin_smooth_absIrr | (intros; apply GlobalTheory.KFinLoc.kFin_smooth_absIrr <;> assumption)
end

