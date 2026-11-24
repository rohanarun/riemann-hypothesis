module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDiffFderivMul
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.GardingStep

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w v : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = v) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasCompactSupport (D 0) ∧ HasDerivAt (fun s => ρ (e s) v) (∫ y, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) v) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Filter.Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  refine ⟨HasCompactSupport.intro hs.isCompact fun y hy => hzero 0 y (by simpa [he0] using hy), ?_⟩
  rw [hform]
  exact key.2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s v : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, v⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g v⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) v⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply ℝ a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply ℝ a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem contDiff_fderiv_mul {F : (Fin n → Fin n → ℂ) → ℂ} (hF : ContDiff ℝ ∞ F) (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ => fderiv ℝ F y (X * y : Matrix _ _ ℂ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ fun y : Fin n → Fin n → ℂ => fun i j => ∑ k, X i k * y k j :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ k j)
  exact h1.clm_apply h2

theorem garding_step : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s v : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ y : H, ∫ g : UJ ε, α (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v⟫_ℂ) → (∀ y, SmoothOnG ε (fun g => ⟪y, σ g v⟫_ℂ)) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → ∃ (β : Matrix (Fin n) (Fin n) ℂ → ℂ) (v' : H), SmoothOnG ε β ∧ HasCompactSupport (fun g : UJ ε => β (umat g)) ∧ (∀ y : H, ∫ g : UJ ε, β (umat g) * ⟪y, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪y, v'⟫_ℂ) ∧ HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) v' 0 := by
  intro n ε H _ _ _ σ α w v hσ hα hs hw
  refine ⟨smooth_coef hσ hα hs hw, fun X hX => ?_⟩
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = v := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let e : ℝ → UJ ε := fun t =>
    ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
  have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
  have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
    rw [smul_neg, Matrix.exp_neg, ← hev]
    exact Matrix.coe_units_inv _
  have he : Continuous e := by
    rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
    exact GlobalTheory.GardingVec.continuous_exp_curve X
  have he0 : e 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    show umat (e 0) = 1
    rw [hev]; simp
  have hcE := GlobalTheory.GardingVec.continuous_exp_curve (-X)
  have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w v hmul hc _ ha hs hw' e he he0
    (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
      (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
    ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
      (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
    (fun s y => by
      simp only [hFα']
      simp only [hum, hei]
      exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
        (GlobalTheory.GardingVec.hasDerivAt_exp_mul (-X) (umat y) s))
  simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
  have hβ := contDiff_fderiv_mul hF (-X)
  refine ⟨fun y => fderiv ℝ F y (-X * y : Matrix _ _ ℂ), _,
    fun g _ => ⟨Set.univ, _, isOpen_univ, trivial, hβ.contDiffOn, fun _ _ _ => rfl⟩, key.1, fun u => ?_, key.2⟩
  have hβi : Integrable (fun y : UJ ε => fderiv ℝ F (umat y) (-X * umat y : Matrix _ _ ℂ) • σ (umat y) w)
      (muG ε) :=
    ((hβ.continuous.comp hu).smul hc).integrable_of_hasCompactSupport key.1.smul_right
  rw [← integral_inner hβi]
  simp only [inner_smul_right]

end GlobalTheory.GardingStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ g ∈ S, nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by
  first | exact @GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | exact GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | (intros; apply GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPart
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem lat0_eq_img_latIn_Ub (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W)
    (he : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ
      = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  ext w
  rw [GlobalTheory.Mass.Transp.mem_img]
  have hd : ((e (e.symm w) : W) : (VS D).V) - (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
      ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X :=
    (le_sup_right : GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ≤ _) (he (e.symm w))
  rw [LinearEquiv.apply_symm_apply] at hd
  have h1 : w ∈ GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ ↔
      (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  have h2 : e.symm w ∈ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ↔
      (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
        ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  rw [h1, h2]
  constructor
  · intro h
    simpa using Submodule.sub_mem _ h hd
  · intro h
    simpa using Submodule.add_mem _ hd h

end GlobalTheory.RowsOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBound
section
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem decE_dOp_le_floor {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (h : ℝ)
    (hh : 32 * (n : ℝ) ^ 2 * Real.sqrt (rkR ε) ≤ h) (g : UJ ε) :
    decE (rkR ε) h (dOp (uMat g)) ≤ Real.exp (-(2 * (2 * (n : ℝ) ^ 2) * (⌊dOp (uMat g)⌋₊ : ℝ))) := by
  rcases Nat.eq_zero_or_pos (rkR ε) with h0 | hq
  · simp [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g, decE]
  · obtain ⟨ha, hb, -⟩ := shell_sum_majorant n (rkR ε) h hn hq hh
    have hp : 0 ≤ dOp (uMat g) := ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    refine (ha (Set.mem_Ici.2 (Nat.cast_nonneg _)) (Set.mem_Ici.2 hp) (Nat.floor_le hp)).trans ?_
    refine (hb _).trans (le_of_eq ?_)
    congr 2
    ring

theorem norm_phe_le_floor (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hn : 1 ≤ B.I.n) (hl : LocDec B h) (hb : HBig B 32 h) (g : B.I.GA) :
    ‖phe B d g‖ ≤ ((∏ v, d v) * (B.e 1).re) *
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
  obtain ⟨-, he0, he, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have h1 : ‖∏ v, ⟪B.w v, B.σ v (uMat (g.1 v)) (B.w v)⟫_ℂ‖ ≤
      ∏ v, Real.exp (-(2 * (2 * (B.I.n : ℝ) ^ 2) * (⌊dOp (uMat (g.1 v))⌋₊ : ℝ))) := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ =>
      (hl v _).trans (decE_dOp_le_floor hn _ h (hb v) _)
  unfold phe ph
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hd0, mul_assoc, mul_assoc,
    mul_comm (B.e 1).re]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (he _) (norm_nonneg _) ((norm_nonneg _).trans h1)) hd0

theorem kernel_abs_bound : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ x y : B.I.GA, Summable (fun γ : B.I.GFset => ‖phe B d (x⁻¹ * γ.1 * y)‖) ∧ ∑' γ : B.I.GFset, ‖phe B d (x⁻¹ * γ.1 * y)‖ ≤ kerC B d * (tau1 B.I x * tau1 B.I y)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) := by
  intro B d h hd hn hl hb x y
  obtain ⟨-, he0, -, -⟩ := GlobalTheory.rowsAut_idem_elementary B
  have hd0 : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).2.2.2.1.le
  have ht := (_root_.GlobalTheory.TauLipschitz.tauLip B.I hn).1
  have hx := ht x
  have hy := ht y
  have hn' : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have ha : (1 : ℝ) ≤ 2 * (B.I.n : ℝ) ^ 2 := by nlinarith
  have hexp : (2 : ℝ) ≤ Real.exp (2 * (B.I.n : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (2 * (B.I.n : ℝ) ^ 2)
    linarith
  have hA : 0 ≤ (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I y)) ^ (2 * B.I.n ^ 2 * B.I.f) := by positivity
  have hc : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd0 he0
  obtain ⟨hs, hle⟩ := GlobalTheory.summable_and_tsum_le_of_box_count (InfinitePlace B.I.F) B.I.GFset
    (fun γ v => dOp (uMat ((x⁻¹ * γ.1 * y).1 v))) (fun γ => ‖phe B d (x⁻¹ * γ.1 * y)‖)
    (2 * (B.I.n : ℝ) ^ 2) _ _ hA hc
    (by rw [Real.exp_neg, one_div]; exact inv_anti₀ two_pos hexp)
    (fun γ v => ((GlobalTheory.Count.Cartan.cartan_distances B.I.n _).2.1 _ 1 hn).1)
    (fun γ => ⟨norm_nonneg _, norm_phe_le_floor B d h hd hn hl hb _⟩)
    (by
      intro r hr
      obtain ⟨hf, hcnt⟩ := _root_.GlobalTheory.Dec.BoundedDistance.countRat B.I x y r hn hr
      have hsub : Subtype.val '' {γ : B.I.GFset | ‖phe B d (x⁻¹ * γ.1 * y)‖ ≠ 0 ∧
            ∀ v, dOp (uMat ((x⁻¹ * γ.1 * y).1 v)) ≤ r v} ⊆
          {γ ∈ B.I.GFset | (x⁻¹ * γ * y).2 ∈ B.I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * γ * y).1 v)) ≤ r v} := by
        rintro _ ⟨γ, ⟨h1, h2⟩, rfl⟩
        refine ⟨γ.2, B.e_adm.2.2.2.2.1 _ fun h0 => h1 ?_, h2⟩
        unfold phe
        rw [h0, mul_zero, norm_zero]
      refine ⟨Set.Finite.of_finite_image (hf.subset hsub) Subtype.val_injective.injOn, le_trans ?_ hcnt⟩
      rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
      exact_mod_cast Set.ncard_le_ncard hsub hf)
  refine ⟨hs, hle.trans ?_⟩
  have hcard : Fintype.card (InfinitePlace B.I.F) ≤ B.I.f := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank B.I.F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces B.I.F
    unfold AutInst.f
    omega
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hcard) (mul_nonneg hc hA)).trans
    (le_of_eq ?_)
  unfold kerC
  rw [div_eq_mul_inv, mul_pow (3 * Real.sqrt B.I.n)]
  ring

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatumStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)) := by
  first | exact @GlobalTheory.OrbitRel.relEqv | exact GlobalTheory.OrbitRel.relEqv | (intros; apply GlobalTheory.OrbitRel.relEqv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroup
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.AlgCutSubgroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem sign_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem inv_sub_one (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := sign_sq
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hMN : uMat g * uMat g⁻¹ = 1 := by
    unfold uMat
    simp
  have hN : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = (Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g)) * uMat g⁻¹ := by
          rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [hMN, Matrix.mul_one]
  rw [hN, conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJ]

theorem exists_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  intro I xf A h1 h2
  obtain ⟨Γ0, hΓ0⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).1
  have hKmul : ∀ a b : I.Gf, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun a b ha hb =>
    (Formalism.UG.stabGL I.Lf).mul_mem ha hb
  have hKinv : ∀ a : I.Gf, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun a ha =>
    (Formalism.UG.stabGL I.Lf).inv_mem ha
  have hKone : (1 : I.Gf) ∈ I.Kset := (Formalism.UG.stabGL I.Lf).one_mem
  have hUmul : ∀ (v : InfinitePlace I.F) (g h : I.Ginf), uMat ((g * h) v) = uMat (g v) * uMat (h v) :=
    fun _ _ _ => rfl
  have hUinv : ∀ (v : InfinitePlace I.F) (g : I.Ginf), uMat (g⁻¹ v) = uMat (g v)⁻¹ := fun _ _ => rfl
  have hUone : ∀ v : InfinitePlace I.F, uMat ((1 : I.Ginf) v) = 1 := fun _ => rfl
  refine ⟨{ carrier := {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg hh ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      obtain ⟨δ, hδ, rfl, hk'⟩ := hh
      refine ⟨γ * δ, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ hδ ⊢
        exact Γ0.mul_mem hγ hδ
      · have e : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
          simp [mul_assoc]
        rw [e]
        exact hKmul _ _ hk hk'
    · have e : uMat ((g * h) v) - 1 =
          (uMat (g v) - 1) * (uMat (h v) - 1) + (uMat (g v) - 1) + (uMat (h v) - 1) := by
        rw [hUmul]
        noncomm_ring
      rw [e]
      exact add_mem (add_mem (h1 v _ (hgA v) _ (hhA v)) (hgA v)) (hhA v)
  · refine ⟨?_, fun v => ?_⟩
    · unfold latGroup
      refine ⟨1, ?_, rfl, ?_⟩
      · rw [← hΓ0]
        exact Γ0.one_mem
      · simpa using hKone
    · rw [hUone, sub_self]
      exact zero_mem _
  · rintro g ⟨hg, hgA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      refine ⟨γ⁻¹, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ ⊢
        exact Γ0.inv_mem hγ
      · have e : xf⁻¹ * γ⁻¹.2 * xf = (xf⁻¹ * γ.2 * xf)⁻¹ := by
          simp [mul_assoc]
        rw [e]
        exact hKinv _ hk
    · rw [hUinv, inv_sub_one]
      exact h2 v _ (hgA v)

end GlobalTheory.AlgCutSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryUnitriangularizingFlagStabilizerStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_unitriangularizing_flag_stabilizer : ∀ (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (γ : GV D), γ ∈ stabF D F0 → ∃ t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, (∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X) ∧ Adapt (t * γ) (lf D F0) (lf D F0) := by
  first | exact @GlobalTheory.FlagTorus.flag_torus | exact GlobalTheory.FlagTorus.flag_torus | (intros; apply GlobalTheory.FlagTorus.flag_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbabilityStatement
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotentQuotient_invariant_probability : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  first | exact @GlobalTheory.UnipQuot.exists_quot_prob | exact GlobalTheory.UnipQuot.exists_quot_prob | (intros; apply GlobalTheory.UnipQuot.exists_quot_prob <;> assumption)
end

