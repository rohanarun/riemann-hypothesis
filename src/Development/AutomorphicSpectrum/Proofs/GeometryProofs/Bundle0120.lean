module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundEventuallyBounds
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

theorem logBound_term_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) : 0 ≤ Real.log (1 / x ^ 2) := by
  rcases h0.eq_or_lt with h | h
  · subst h
    simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (pow_pos h 2), _root_.one_mul]
    nlinarith

theorem uncentre_recentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) :
    uncentre t₀ ρ π (recentre t₀ ρ π u) = u := by
  funext i
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  simp only [uncentre, recentre, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    Equiv.apply_symm_apply, add_sub_cancel_left]
  rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ', _root_.one_mul]

theorem lipschitz_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) :
    LipschitzWith (Real.toNNReal ρ⁻¹) (uncentre t₀ ρ π) := by
  refine LipschitzWith.of_dist_le_mul fun t s => ?_
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)]
  refine (dist_pi_le_iff (mul_nonneg (inv_nonneg.mpr hρ.le) dist_nonneg)).2 fun i => ?_
  simp only [uncentre, dist_eq_norm]
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le,
    sub_sub_sub_cancel_right]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (t - s) (π.symm i)) (inv_nonneg.mpr hρ.le)

theorem norm_fderiv_comp_uncentre {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : (Fin n → ℂ) → E) (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    ‖fderiv ℝ (fun t' => G (uncentre t₀ ρ π t')) t‖ ≤ ‖fderiv ℝ G (uncentre t₀ ρ π t)‖ * ρ⁻¹ := by
  have hdu : Differentiable ℝ (uncentre t₀ ρ π) := by
    unfold uncentre
    fun_prop
  by_cases hG : DifferentiableAt ℝ G (uncentre t₀ ρ π t)
  · rw [show (fun t' => G (uncentre t₀ ρ π t')) = G ∘ uncentre t₀ ρ π from rfl, fderiv_comp t hG (hdu t)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := t) (lipschitz_uncentre t₀ hρ π)
    rwa [Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)] at h
  · have hnd : ¬ DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t')) t := by
      intro h
      apply hG
      have hdr : Differentiable ℝ (recentre t₀ ρ π) := by
        unfold recentre
        fun_prop
      have h' : DifferentiableAt ℝ (fun t' => G (uncentre t₀ ρ π t'))
          (recentre t₀ ρ π (uncentre t₀ ρ π t)) := by
        rw [recentre_uncentre t₀ hρ π t]
        exact h
      have h2 := h'.comp (uncentre t₀ ρ π t) (hdr _)
      have he : ((fun t' => G (uncentre t₀ ρ π t')) ∘ recentre t₀ ρ π) = G := by
        funext u
        simp only [Function.comp_apply, uncentre_recentre t₀ hρ π u]
      rwa [he] at h2
    rw [fderiv_zero_of_not_differentiableAt hnd, norm_zero]
    exact mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hρ.le)

theorem logBound_weight_le {n a₀ a : ℕ} {t₀ t : Fin n → ℂ} {π : Equiv.Perm (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hπ : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) (ht : ‖t‖ < 1)
    (hu : ∀ i : Fin n, (i : ℕ) < a₀ → uncentre t₀ ρ π t i ≠ 0) :
    (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤
      ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
  have hf : ∀ j : Fin n, 0 ≤ Real.log (1 / ‖t j‖ ^ 2) := fun j =>
    logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t j) ht)
  calc (∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if ((π.symm i : Fin n) : ℕ) < a then Real.log (1 / ‖t (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h1 h2 h2
        · have hj := hπ i h1
          have hne := hu i h1
          have hx : ‖uncentre t₀ ρ π t i‖ = ρ⁻¹ * ‖t (π.symm i)‖ := by
            simp only [uncentre, hj.2, sub_zero, norm_mul, norm_inv, Complex.norm_real,
              Real.norm_of_nonneg hρ.le]
          have htpos : 0 < ‖t (π.symm i)‖ := by
            refine lt_of_le_of_ne (norm_nonneg _) (Ne.symm ?_)
            intro h0
            apply hne
            rw [← norm_eq_zero, hx, h0, mul_zero]
          have hρi : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).mpr hρ1
          rw [hx]
          apply Real.log_le_log (one_div_pos.mpr (pow_pos (mul_pos (inv_pos.mpr hρ) htpos) 2))
          apply one_div_le_one_div_of_le (pow_pos htpos 2)
          exact pow_le_pow_left₀ (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) hρi) 2
        · exact absurd (hπ i h1).1 h2
        · exact hf _
        · exact le_rfl
    _ = ∑ j : Fin n, if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0 :=
        Equiv.sum_comp π.symm (fun j => if (j : ℕ) < a then Real.log (1 / ‖t j‖ ^ 2) else 0)

theorem logBound_recentred : ∀ (n a₀ g r a : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) → (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a ∧ t₀ (π.symm i) = 0) → ∃ ε c C : ℝ, 0 < ε ∧ ε ≤ ρ ∧ 0 < c ∧ 0 < C ∧ ∀ t : Fin n → ℂ, ‖t - t₀‖ < ε → ‖t‖ < 1 → HodgeMetric.uncentre t₀ ρ π t ∈ Flat.punct n a₀ 1 → ((HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ - (c : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by
  intro n a₀ g r a Λ _ L U t₀ π ρ hρ hρ1 hU hli hπ
  obtain ⟨ρ', c, C', hρ', hc, hC', hb⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.logBound_subframe n a₀ g r Λ L U (periodGram L U) hU hli (fun z i j => rfl)
  refine ⟨min ρ (ρ * ρ'), c, C' / ρ, lt_min hρ (mul_pos hρ hρ'), min_le_left _ _, hc, div_pos hC' hρ, ?_⟩
  intro t htε ht hpun
  have hzb : uncentre t₀ ρ π t ∈ Flat.punct n a₀ ρ' := by
    refine ⟨?_, hpun.2⟩
    have h1 := (lipschitz_uncentre t₀ hρ π).dist_le_mul t t₀
    rw [uncentre_self, Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le), dist_eq_norm t t₀] at h1
    have h2 : ‖t - t₀‖ < ρ * ρ' := lt_of_lt_of_le htε (min_le_right _ _)
    rw [Metric.mem_ball]
    calc dist (uncentre t₀ ρ π t) 0 ≤ ρ⁻¹ * ‖t - t₀‖ := h1
      _ < ρ⁻¹ * (ρ * ρ') := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hρ)
      _ = ρ' := by rw [← _root_.mul_assoc, inv_mul_cancel₀ hρ.ne', _root_.one_mul]
  obtain ⟨b1, b2, b3⟩ := hb _ hzb
  have hle := logBound_weight_le hρ hρ1 hπ ht hpun.2
  have hX'0 : 0 ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by
    refine add_nonneg (Real.exp_pos 1).le (Finset.sum_nonneg fun i _ => ?_)
    split_ifs
    · exact logBound_term_nonneg (norm_nonneg _) (lt_of_le_of_lt (norm_le_pi_norm t i) ht)
    · exact le_rfl
  have hS : (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) := by linarith
  have hCρ : C' ≤ C' / ρ := le_div_self hC'.le hρ hρ1
  have hCC : C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) :=
    (mul_le_mul_of_nonneg_left hS hC'.le).trans (mul_le_mul_of_nonneg_right hCρ hX'0)
  refine ⟨b1, ?_, ?_⟩
  · have hd : 0 ≤ C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) := by linarith
    have hsplit : (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹ =
        ((((C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - (HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t))⁻¹) +
          (((C' / ρ * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) - C' * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) : ℝ)) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [hsplit]
    exact b2.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hd))
  · intro p q
    calc ‖fderiv ℝ (fun t' => HodgeMetric.periodGram L U (HodgeMetric.uncentre t₀ ρ π t') p q) t‖
        ≤ ‖fderiv ℝ (fun w => periodGram L U w p q) (uncentre t₀ ρ π t)‖ * ρ⁻¹ :=
          norm_fderiv_comp_uncentre (fun w => periodGram L U w p q) t₀ hρ π t
      _ ≤ C' * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) * ρ⁻¹ :=
          mul_le_mul_of_nonneg_right (b3 p q) (inv_nonneg.mpr hρ.le)
      _ = C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a₀ then Real.log (1 / ‖uncentre t₀ ρ π t i‖ ^ 2) else 0) / 2) := by ring
      _ ≤ C' * ρ⁻¹ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (mul_nonneg hC'.le (inv_nonneg.mpr hρ.le))
      _ = C' / ρ * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖t i‖ ^ 2) else 0) / 2) := by ring

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem spread_slice {n g N : ℕ} {W : Set ((Fin n → ℂ) × (Fin g → ℂ))} (hW : IsOpen W)
    {Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ)} (hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W)
    {b₀ : Fin n → ℂ} {x : Fin g → ℂ} (hmem : (b₀, x) ∈ W)
    {L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)} (hL : AnalyticAt ℂ L (b₀, Φ (b₀, x)))
    {Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop} (hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ (fun b => L (b, Φ (b, x))) (ball b₀ ε) ∧
      ∀ b ∈ ball b₀ ε, (b, x) ∈ W ∧ Q (b, Φ (b, x)) := by
  have hcont : Continuous (fun b : Fin n → ℂ => (b, x)) := continuous_id.prodMk continuous_const
  have hUo : IsOpen ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := hW.preimage hcont
  have hΦd : DifferentiableOn ℂ (fun b => Φ (b, x)) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := by
    rw [differentiableOn_pi]
    intro j
    exact (hΦ j).comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn
      (fun b hb => hb)
  have hFd : DifferentiableOn ℂ (fun b => (b, Φ (b, x))) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) :=
    differentiableOn_id.prodMk hΦd
  have hb₀ : b₀ ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hmem
  have hFc : ContinuousAt (fun b => (b, Φ (b, x))) b₀ :=
    (hFd.differentiableAt (hUo.mem_nhds hb₀)).continuousAt
  have hU' : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hUo.mem_nhds hb₀
  have hev : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W ∧
      AnalyticAt ℂ L (b, Φ (b, x)) ∧ Q (b, Φ (b, x)) :=
    hU'.and (Filter.Tendsto.eventually hFc (hL.eventually_analyticAt.and hQ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun b hb => ?_, fun b hb => ⟨(hball b hb).1, (hball b hb).2.2⟩⟩
  exact ((hball b hb).2.1.differentiableAt.comp b
    (hFd.differentiableAt (hUo.mem_nhds (hball b hb).1))).differentiableWithinAt

theorem per_spreads : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  intro R _ G _ _ g n M B ψ e _ b₀ hb₀ x hx
  have hx1 : e.ex b₀ x = 1 := hx
  have h01 : e.ex b₀ 0 = 1 := by
    have h := e.add b₀ hb₀ 0 0
    rw [add_zero] at h
    exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
  have hx0 : e.ex b₀ x = e.ex b₀ 0 := hx1.trans h01.symm
  obtain ⟨V, N, f, L, hV, hLan, hinv, huniq⟩ := e.log b₀ hb₀
  let W : Set ((Fin n → ℂ) × (Fin g → ℂ)) := {bz | bz ∈ B ×ˢ Set.univ ∧
    ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex bz.1 bz.2)).base).obj V}
  have hWo : IsOpen W := (e.hol V 0).1
  let Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ) :=
    fun bz j => valAt' (Over.Hom.left (e.ex bz.1 bz.2)) V (f j)
  have hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W := fun j => (e.hol V (f j)).2
  have hmemW : (b₀, x) ∈ W := by
    refine ⟨⟨hb₀, Set.mem_univ _⟩, ?_⟩
    show ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b₀ x)).base).obj V
    rw [hx0]
    exact hV
  have hΦx : Φ (b₀, x) = fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j) := by
    show (fun j => valAt' (Over.Hom.left (e.ex b₀ x)) V (f j)) = _
    rw [hx0]
  have hL' : AnalyticAt ℂ L (b₀, Φ (b₀, x)) := by
    rw [hΦx]
    exact hLan
  let Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop := fun p =>
    ∀ y : Over.mk (spMap (ψ p.1)) ⟶ G,
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left y).base).obj V →
        (∀ j, valAt' (Over.Hom.left y) V (f j) = p.2 j) → y = e.ex p.1 (L p)
  have hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p := by
    rw [hΦx]
    exact huniq
  obtain ⟨ε, hε, hdiff, hprop⟩ := spread_slice hWo hΦ hmemW hL' hQ
  have hWmem : ∀ b ∈ ball b₀ ε, b ∈ B ∧
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b x)).base).obj V := by
    intro b hb
    obtain ⟨⟨hbB, -⟩, hcov⟩ := (hprop b hb).1
    exact ⟨hbB, hcov⟩
  refine ⟨ε, fun b => x - L (b, Φ (b, x)), hε, fun b hb => (hWmem b hb).1,
    (differentiableOn_const x).sub hdiff, ?_, ?_⟩
  · show x - L (b₀, Φ (b₀, x)) = x
    have h0 : L (b₀, fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)) = 0 :=
      hinv.self_of_nhds
    rw [hΦx, h0, sub_zero]
  · intro b hb
    obtain ⟨hbB, hcov⟩ := hWmem b hb
    have hyx : e.ex b x = e.ex b (L (b, Φ (b, x))) :=
      (hprop b hb).2 (e.ex b x) hcov (fun j => rfl)
    show e.ex b (x - L (b, Φ (b, x))) = 1
    have hadd := e.add b hbB (x - L (b, Φ (b, x))) (L (b, Φ (b, x)))
    rw [sub_add_cancel, hyx] at hadd
    exact mul_right_cancel (hadd.symm.trans (_root_.one_mul _).symm)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology _root_.Metric

theorem exists_lift_of_mem_range {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (x : Sp ℂ ⟶ X)
    (p : Sp ℂ) (hp : x p ∈ Set.range i) : ∃ t : Sp ℂ ⟶ Z, t ≫ i = x := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hs : Surjective (pullback.snd i x) :=
    ⟨fun q => ⟨w, by rw [hw]; exact Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i x)
  exact ⟨inv (pullback.snd i x) ≫ pullback.fst i x, by simp [pullback.condition]⟩

theorem one_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem mem_per_of_frequently : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  intro R _ G _ _ g n M B ψ e hsep hψ b₀ hb₀ s hs hfr
  haveI := hsep
  by_contra hne
  have hid : η[G].left ≫ G.hom = 𝟙 _ := Over.w _
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp _ G.hom
  let V : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, by
    letI := hη
    exact η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV₀ : ⊤ ≤ (e.ex b₀ (s b₀)).left ⁻¹ᵁ V := by
    intro p _
    show (e.ex b₀ (s b₀)).left p ∉ Set.range η[G].left
    intro hp
    obtain ⟨t, ht⟩ := exists_lift_of_mem_range η[G].left (e.ex b₀ (s b₀)).left p hp
    apply hne
    show e.ex b₀ (s b₀) = 1
    apply Over.OverMorphism.ext
    have h1 : t = spMap (ψ b₀) := by
      have h2 := Over.w (e.ex b₀ (s b₀))
      have h4 : (t ≫ η[G].left) ≫ G.hom = spMap (ψ b₀) := by rw [ht]; exact h2
      rw [Category.assoc, hid] at h4
      exact h4
    rw [one_left_eq, ← ht, h1]
    rfl
  have hopen := (e.hol V 0).1
  have hmem : (b₀, s b₀) ∈ {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ V} :=
    ⟨⟨hb₀, trivial⟩, hV₀⟩
  have hcont : ContinuousAt (fun b => (b, s b)) b₀ := continuousAt_id.prodMk hs
  have hev := hcont.eventually (hopen.mem_nhds hmem)
  obtain ⟨b, ⟨-, hper⟩, -, hb⟩ := (hfr.and_eventually hev).exists
  have hper' : e.ex b (s b) = 1 := hper
  have hb' : ⊤ ≤ (e.ex b (s b)).left ⁻¹ᵁ V := hb
  rw [hper'] at hb'
  let p : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have hp : (1 : Over.mk (spMap (ψ b)) ⟶ G).left p ∉ Set.range η[G].left := hb' (show p ∈ ⊤ from trivial)
  apply hp
  rw [one_left_eq]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectivePointImageReduced
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem isReduced_image_of_quasiCompact {X Y : Scheme.{0}} [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] :
    IsReduced f.image := by
  have : ∀ x : f.image, _root_.IsReduced (f.image.presheaf.stalk x) := fun x => by
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := ⊤) (x := f.imageι x) trivial
    have hV : IsAffineOpen (f.imageι ⁻¹ᵁ U) := hU.preimage f.imageι
    have hx' : x ∈ f.imageι ⁻¹ᵁ U := hx
    have : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U) :=
      isReduced_of_injective (f.toImage.app (f.imageι ⁻¹ᵁ U)).hom
        (f.toImage_app_injective ⟨U, hU⟩)
    letI := f.image.presheaf.algebra_section_stalk (⟨x, hx'⟩ : f.imageι ⁻¹ᵁ U)
    have := hV.isLocalization_stalk ⟨x, hx'⟩
    exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hx'⟩).asIdeal.primeCompl _ ‹_›
  exact isReduced_of_isReduced_stalk f.image

theorem quasiCompact_point {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} (x : Fin (N + 1) → Ω) (hx : x ≠ 0) :
    QuasiCompact (point ℚ x hx) := by
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ℚ N
  have h : QuasiCompact (point ℚ x hx ≫ PSpace.str ℚ N) := by
    rw [point_str]
    infer_instance
  exact .of_comp _ (PSpace.str ℚ N)

theorem closure_reduced_dominant : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (hx : x ≠ 0),
    IsReduced (point ℚ x hx).image ∧ IsDominant (point ℚ x hx).toImage := by
  intro Ω _ _ N x hx
  have := quasiCompact_point x hx
  exact ⟨isReduced_image_of_quasiCompact _, inferInstance⟩

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PuncturedPolydiscOpenConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PunctShape

def factor (a : ℕ) (ρ : ℝ) (n : ℕ) (i : Fin n) : Set ℂ := {w | ‖w‖ < ρ ∧ (i.val < a → w ≠ 0)}

theorem punct_eq_pi (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    punct n a ρ = Set.pi Set.univ (factor a ρ n) := by
  ext z
  simp only [punct, factor, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
    mem_ball_zero_iff, pi_norm_lt_iff hρ]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨h1 i, h2 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem isOpen_factor (n a : ℕ) (ρ : ℝ) (i : Fin n) : IsOpen (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i = Metric.ball 0 ρ ∩ {0}ᶜ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball.inter isOpen_compl_singleton
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isOpen_ball

theorem isConnected_factor (n a : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (i : Fin n) :
    IsConnected (factor a ρ n i) := by
  by_cases h : i.val < a
  · have he : factor a ρ n i =
        (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Set.Ioo 0 ρ ×ˢ Set.univ) := by
      ext w
      simp only [factor, h, true_implies, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
        Set.mem_Ioo, Set.mem_univ, and_true, Prod.exists]
      constructor
      · rintro ⟨hw, hw0⟩
        exact ⟨‖w‖, Complex.arg w, ⟨norm_pos_iff.mpr hw0, hw⟩, Complex.norm_mul_exp_arg_mul_I w⟩
      · rintro ⟨r, θ, ⟨hr0, hrρ⟩, rfl⟩
        have hn : ‖(r : ℂ) * Complex.exp (θ * Complex.I)‖ = r := by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, _root_.mul_one, Complex.norm_real,
            Real.norm_of_nonneg hr0.le]
        refine ⟨by rw [hn]; exact hrρ, ?_⟩
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne') (Complex.exp_ne_zero _)
    rw [he]
    exact ((isConnected_Ioo hρ).prod isConnected_univ).image _ (by fun_prop)
  · have he : factor a ρ n i = Metric.ball 0 ρ := by
      ext w
      simp [factor, h]
    rw [he]
    exact isConnected_ball hρ

theorem punct_open_connected_nonempty : ∀ (n a : ℕ) (ρ : ℝ), 0 < ρ → IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty := by
  intro n a ρ hρ
  rw [punct_eq_pi n a ρ hρ]
  exact ⟨isOpen_set_pi Set.finite_univ fun i _ => isOpen_factor n a ρ i,
    isPreconnected_univ_pi fun i => (isConnected_factor n a ρ hρ i).isPreconnected,
    Set.univ_pi_nonempty_iff.mpr fun i => (isConnected_factor n a ρ hρ i).nonempty⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PunctShape
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSncStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_generic_fibre_of_snc : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y e bd → SmoothGenericFibreM y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel <;> assumption)
end

