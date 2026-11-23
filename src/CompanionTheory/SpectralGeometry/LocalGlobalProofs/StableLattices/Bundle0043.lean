module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0037
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0039
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundary
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GrowthStatement
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathGrowth

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def Lev (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  (Continuous fun g : S7.UJ ε => f (S7.toM g)) ∧ LevelF ε f (-(m : ℝ))

theorem hs_nonneg (h : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem row_le_hs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ∑ i, ‖h j i‖ ^ 2 ≤ Formalism.REAL.hs h :=
  Finset.single_le_sum (f := fun a => ∑ i, ‖h a i‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem row_cs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) :
    ‖∑ i, h j i * a i‖ ^ 2 ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, h j i * a i‖ ≤ ∑ i, ‖h j i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
  have h2 : (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ i, h j i * a i‖ ^ 2 ≤ (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 := h2
    _ ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (row_le_hs h j) (Finset.sum_nonneg fun _ _ => by positivity)

theorem row_bound (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) (m : ℕ) :
    ‖∑ i, h j i * a i‖ ^ 2 * Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) ≤
      ∑ i, ‖a i‖ ^ 2 * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
  have hs0 := hs_nonneg h
  have hT : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hcs := row_cs h j a
  rw [← Finset.sum_mul]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul] at hcs
    have hz : ‖∑ i, h j i * a i‖ ^ 2 = 0 := le_antisymm hcs (by positivity)
    rw [hz, zero_mul]
    exact mul_nonneg hT (Real.rpow_nonneg hs0 _)
  · have e : Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) = Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hpos, Real.rpow_neg_one]
    have hr := Real.rpow_nonneg hs0 (-(m : ℝ))
    rw [e]
    calc ‖∑ i, h j i * a i‖ ^ 2 * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹)
        ≤ (Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2) * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹) :=
          mul_le_mul_of_nonneg_right hcs (by positivity)
      _ = (∑ i, ‖a i‖ ^ 2) * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
          field_simp

theorem enorm_sq_mul (x : ℂ) (r : ℝ) :
    ‖x‖ₑ ^ 2 * ENNReal.ofReal r = ENNReal.ofReal (‖x‖ ^ 2 * r) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem continuous_hs (ε : Fin n → Bool) : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((S7.continuous_toM ε).matrix_elem i j).norm).pow 2

theorem measurable_term (ε : Fin n → Bool) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (s : ℝ)
    (hf : Continuous fun g : S7.UJ ε => f (S7.toM g)) :
    Measurable fun g : S7.UJ ε => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) :=
  (hf.measurable.enorm.pow_const 2).mul
    (ENNReal.measurable_ofReal.comp ((continuous_hs ε).measurable.pow_const s))

theorem lev_row (ε : Fin n → Bool) (m : ℕ) (f : Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : ∀ i, Lev ε m (f i)) (j : Fin n) : Lev ε (m + 1) fun g => ∑ i, g j i * f i g := by
  refine ⟨continuous_finsetSum _ fun i _ =>
    ((S7.continuous_toM ε).matrix_elem j i).mul (hf i).1, ?_⟩
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (b := ∫⁻ g : S7.UJ ε, ∑ i,
    ‖f i (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-(m : ℝ))) ∂Measure.haar) ?_
  · have hr := fun k : ℝ => Real.rpow_nonneg (hs_nonneg (S7.toM g)) k
    simp only [enorm_sq_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg (by positivity) (hr _)]
    exact ENNReal.ofReal_le_ofReal (row_bound _ j _ m)
  · rw [lintegral_finsetSum _ fun i _ => measurable_term ε _ (hf i).1]
    exact ENNReal.sum_lt_top.2 fun i _ => (hf i).2

theorem level_zero_of_memLp (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂Measure.haar < ⊤ := by
  let μ : Measure (S7.UJ ε) := Formalism.REAL.muG ε
  haveI : μ.IsHaarMeasure := Formalism.REAL.instIsHaarMuG n ε
  have h' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ := h
  have h2 : ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂μ < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (p := 2) two_ne_zero ENNReal.ofNat_ne_top h'.eLpNorm_lt_top
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure (S7.UJ ε)) μ, lintegral_smul_measure]
  exact ENNReal.mul_lt_top (by simp) h2

theorem lev_base (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (ξ : H)
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ) (u : D) :
    Lev ε 0 (baseCoef σ D ξ u) := by
  constructor
  · have h1 : Continuous fun g : S7.UJ ε => σ (S7.toM g) (u : H) :=
      (hσ.2.2 (u : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
    exact continuous_const.inner h1
  · unfold LevelF
    have := level_zero_of_memLp ε (baseCoef σ D ξ u) (hsq (u : H) ξ)
    simpa using this

theorem lev_path (ε : Fin n → Bool) : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)) (m : ℕ),
    (∀ u, Lev ε m (c u)) → ∀ u, Lev ε (m + ss.length) (pathCoef X c χ ss js u)
  | [], _, _, _, _, _, h, u => h u
  | s :: ss, X, c, χ, js, m, h, u => by
    have key := lev_path ε ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail (m + 1)
      (fun w => lev_row ε m (fun i => c ((show stepSub X (χ s) from w).1 i)) (fun i => h _) (js.headD s)) u
    rw [show m + (s :: ss).length = m + 1 + ss.length by simp only [List.length_cons]; omega]
    exact key

theorem growth : Growth := by
  intro n ε H _ _ _ σ D E hK χ ss hσ hsq
  refine ⟨(ss.length : ℝ), fun i u => ?_⟩
  have key := lev_path ε ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 0
    (fun u => lev_base ε σ D _ hσ hsq u) u
  rw [zero_add] at key
  exact key.2

end GlobalTheory.CompanionTheory.PathGrowth
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjUOfInjR
section
noncomputable section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem injU_of_injR : CompanionTheory.RgExh.U.InjR → CompanionTheory.RgExh.U.InjU := by
  intro hR n ε γ lev V _ _ E hG hE hU hL hM u y hu hy hd hb
  have hmono := hG.2.1
  have hsingle := _root_.GlobalTheory.CompanionTheory.RgExh.lF_single_omU n ε lev V E γ u hu
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := _root_.GlobalTheory.CompanionTheory.RgExhStableChains.exists_stable n ε lev V E _ y hL hy hd
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := _root_.GlobalTheory.CompanionTheory.FarReg.highest_preimage_of_stable n V
    {pq : Fin n × Fin n // pq.1 < pq.2 ∧ ε pq.1 = ε pq.2 ∧ lev pq.1 = lev pq.2} T
    (fun i => lF E i.1.1 i.1.2) (fun i => lF E i.1.2 i.1.1) (bd (allT n) E) y hTf
    (fun i x z => _root_.GlobalTheory.CompanionTheory.RgExhFarReg.ChainAdj.lF_adjoint n ε V E hU _ _ i.2.2.1 x z)
    (fun i t ht => hTs _ _ i.2.2.1 i.2.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.1.symm i.2.2.2.symm t ht)
    (fun i t ht => _root_.GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm n lev V E hmono hE _ _ i.2.2.2 t (hTS t ht).1)
    (fun i t ht => _root_.GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm n lev V E hmono hE _ _ i.2.2.2.symm t (hTS t ht).1) hyT
    (fun i => by rw [hb]; exact hsingle _ _ i.2.1 i.2.2.1 i.2.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := _root_.GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order n ε lev hmono
  have hlc : ∀ e ∈ l, e.1.1 < e.1.2 ∧ ε e.1.1 = ε e.1.2 ∧ lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨h1, h2⟩ := (hmem e).1 he
    have hc : ε e.1.1 = ε e.1.2 := (Finset.mem_filter.1 h1).2
    refine ⟨e.2, hc, le_antisymm (hmono e.2.le) ?_⟩
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, not_le.1 h3⟩)
  have hbd := _root_.GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod n V E (_root_.GlobalTheory.CompanionTheory.Cartan.cartan n V E) l y' hcl
    (fun e he => hy'0 ⟨e.1, hlc e he⟩)
  obtain ⟨c, hc0, hcw⟩ := _root_.GlobalTheory.CompanionTheory.Chains.prod_cre_single n V l (omU ε lev) u hnd (fun i hi => ((hmem i).1 hi).2)
  have hun : omU ε lev ∪ l.toFinset = om ε := by
    ext i
    simp only [Finset.mem_union, List.mem_toFinset, hmem]
    constructor
    · rintro (h | h)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.1⟩
      · exact h.1
    · intro h
      by_cases h2 : i ∈ omU ε lev
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
  have hcard : (om ε).card = (omU ε lev).card + l.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd]
    exact Finset.disjoint_left.2 fun i h1 h2 => ((hmem i).1 (List.mem_toFinset.1 h2)).2 h1
  obtain ⟨hs1, hs2⟩ := _root_.GlobalTheory.CompanionTheory.RgExh.suppIn_deg_cre_prod n V (inR ε lev) l y' _ (fun i hi => Or.inl (hlc i hi).2.1)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cn n V := ((l.map cre).prod : Module.End ℂ (Cn n V)) y' with hC
  have hsm : ∀ (s : ℂ) (x : Cn n V) (A : Finset (Pos n)), s • x A ≠ 0 → x A ≠ 0 := fun s x A h h0 => h (by rw [h0, smul_zero])
  refine hR n ε γ lev V E hG hE hU hL hM u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu.1 ?_ ?_ ?_
  · exact fun A hA => hs1 A (hsm _ C A hA)
  · intro A hA
    have h3 := hs2 A (hsm _ C A hA)
    refine ⟨Finset.filter_false_of_mem fun _ _ h => h rfl, ?_⟩
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), h3, hcard]
    omega
  · rw [map_smul, hC, hbd, hy'b, hb, hcw, hun, smul_smul, smul_smul]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.RgExh
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LowestData

open Formalism.REAL (KHighest)
open _root_.CompanionTheory.RgExh (GMod AlgDS)
open _root_.CompanionTheory.RgDs (InCone)
open GlobalTheory.LowestKTypeDetermines (lt_of_perm_lt rhoC_perm lowK_add strictAnti_add_rho nsq_add_cone eq_zero_of_nsq nsq_comp)

variable {n : ℕ}

theorem kHighest_renumber {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) {s s' : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hs' : ∀ a b, a < b → ε (s' a) = ε (s' b) → s' a < s' b) {Λ : Fin n → ℝ} {v : V}
    (h : KHighest (ε ∘ s') (fun a b => E (s' a) (s' b)) Λ v) :
    KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (Λ ∘ s'.symm ∘ s) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h1 (s'.symm (s a))
    simpa using this
  · have hlt := hs a b hab he
    have key : s'.symm (s a) < s'.symm (s b) := by
      refine lt_of_perm_lt (s := s') hs' ?_ ?_
      · simpa only [Equiv.apply_symm_apply] using hlt
      · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using he
    have := h2 _ _ key (by simpa using he)
    simpa using this

-- Unfold DataUniq and ConeDS to depend directly on AlgDS and InCone.
theorem dataUniq (n : ℕ) (ε : Fin n → Bool) (X : GMod n)
    (s s' : Equiv.Perm (Fin n)) (mu mu' : Fin n → ℝ)
    (h : AlgDS ε X s mu)
    (hc : ∀ (ν : Fin n → ℝ) (x : X.V), x ≠ 0 →
      KHighest (ε ∘ s) (fun a b => X.E (s a) (s b)) ν x →
      InCone (PI.UpqRep.lowK (ε ∘ s) mu) ν)
    (h' : AlgDS ε X s' mu') : s = s' ∧ mu = mu' := by
  obtain ⟨hl, hs, -, v, hv0, hv⟩ := h
  obtain ⟨hl', hs', hmin', v', hv0', hv'⟩ := h'
  have add : ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      PI.UpqRep.lowK ε lam + (2 : ℝ) • Formalism.REAL.rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := fun ε lam => lowK_add ε lam
  have k1 := kHighest_renumber ε X.E hs hs' hv'
  have k2 := kHighest_renumber ε X.E hs' hs hv
  obtain ⟨c, hc1, e⟩ := hc _ v' hv0' k1
  have m2 := hmin' _ v hv0 k2
  set x := mu + Formalism.QuantumDeterminants.rhoStd n with hx
  set x' := mu' + Formalism.QuantumDeterminants.rhoStd n with hx'
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b with hQ
  have hsx : StrictAnti x := strictAnti_add_rho hl.1
  have hsx' : StrictAnti x' := strictAnti_add_rho hl'.1
  have r1 : x' ∘ s'.symm ∘ s = x + Q := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    have e2 : x' = PI.UpqRep.lowK (ε ∘ s') mu' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := (add _ _).symm
    funext a
    have ea := congrFun e a
    rw [e1, e2, rhoC_perm s hs, rhoC_perm s' hs']
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, Equiv.apply_symm_apply] at ea ⊢
    rw [ea]; ring
  have r2 : x ∘ s.symm ∘ s' =
      PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s' + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s') := by
    have e1 : x = PI.UpqRep.lowK (ε ∘ s) mu + (2 : ℝ) • Formalism.REAL.rhoC (ε ∘ s) := (add _ _).symm
    rw [e1, rhoC_perm s hs, rhoC_perm s' hs']
    funext a
    simp
  have m3 : Formalism.REAL.nsq x' ≤ Formalism.REAL.nsq x := by
    have a1 : Formalism.REAL.nsq x' =
        PI.UpqRep.vNormSq (ε ∘ s') (PI.UpqRep.lowK (ε ∘ s') mu') := by
      rw [hx', ← add]; rfl
    have a2 : Formalism.REAL.nsq x = PI.UpqRep.vNormSq (ε ∘ s')
        (PI.UpqRep.lowK (ε ∘ s) mu ∘ s.symm ∘ s') := by
      have := nsq_comp (s.symm * s') x
      have e3 : x ∘ ⇑(s.symm * s') = x ∘ s.symm ∘ s' := rfl
      rw [e3, r2] at this
      rw [← this]; rfl
    rw [a1, a2]; exact m2
  have m4 : Formalism.REAL.nsq (x + Q) = Formalism.REAL.nsq x' := by
    rw [← r1]
    exact nsq_comp (s'.symm * s) x'
  have h4 := nsq_add_cone hsx.antitone hc1
  have hQ0 : Q = 0 := eq_zero_of_nsq (by linarith)
  rw [hQ0, add_zero] at r1
  have hm : StrictMono (s'.symm * s) := fun a b hab => by
    have h5 := hsx hab
    rw [← r1] at h5
    exact hsx'.lt_iff_gt.1 h5
  have h6 : s'.symm * s = 1 := by
    have := Subsingleton.elim (hm.orderIsoOfSurjective _ (s'.symm * s).surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  have h7 : s = s' := by
    refine Equiv.ext fun a => ?_
    have := congrArg (fun t : Equiv.Perm (Fin n) => s' (t a)) h6
    simpa using this
  subst h7
  refine ⟨rfl, ?_⟩
  have h8 : x' = x := by
    simpa using r1
  exact (add_right_cancel h8).symm

end GlobalTheory.CompanionTheory.LowestData
end
end

