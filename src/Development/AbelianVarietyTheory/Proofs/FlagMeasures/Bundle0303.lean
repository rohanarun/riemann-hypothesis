module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KerDiagBasisIndep
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem kerDiag_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y : Fin D → H) (hy : Orthonormal ℂ y) (v : H) (hv : v ∈ Submodule.span ℂ (Set.range y)) :
    v = ∑ i, ⟪y i, v⟫_ℂ • y i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy.inner_right_fintype]

theorem kerDiag_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y y' : Fin D → H) (hy : Orthonormal ℂ y) (hy' : Orthonormal ℂ y') (a b : Fin D → ℂ)
    (hb : ∀ j, b j = ∑ i, ⟪y i, y' j⟫_ℂ * a i) :
    ∑ j, ‖b j‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu
  have h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖ := by
    intro j
    rw [norm_inner_symm, hb, hu, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_conj, mul_comm]
  have h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    have h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hu, hy.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [inner_self_eq_norm_sq_to_K] at h3
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← h3, Complex.ofReal_pow]
    rfl
  simp only [h1]
  rw [← h2]
  exact hy'.sum_inner_products_le u

theorem kerDiag_add_rep (B : RowsAut) (F F' : B.I.L2 B.μf B.fund) (f f' : B.I.GA → ℂ) (c : ℂ)
    (h : IsContRep B F f) (h' : IsContRep B F' f') :
    IsContRep B (F + c • F') (fun x => f x + c * f' x) := by
  refine ⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩
  · simp only [h.2.1 γ hγ x, h'.2.1 γ hγ x]
  · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem kerDiag_sum_rep (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (f : ι → B.I.GA → ℂ) (c : ι → ℂ) (F : B.I.L2 B.μf B.fund) (g : B.I.GA → ℂ)
    (hg : IsContRep B F g) (h : ∀ i, IsContRep B (y i) (f i)) :
    IsContRep B (F + ∑ i ∈ s, c i • y i) (fun x => g x + ∑ i ∈ s, c i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have := kerDiag_add_rep B _ _ _ _ (c a) ih (h a)
    simp only [Finset.sum_insert ha]
    convert this using 1
    · abel
    · funext x; ring

theorem kerDiag_vals (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund)
    (f f' : Fin D → B.I.GA → ℂ) (hy : Orthonormal ℂ y)
    (hs : Submodule.span ℂ (Set.range y') ≤ Submodule.span ℂ (Set.range y))
    (h : ∀ i, IsContRep B (y i) (f i)) (h' : ∀ i, IsContRep B (y' i) (f' i)) (j : Fin D)
    (x : B.I.GA) : f' j x = ∑ i, ⟪y i, y' j⟫_ℂ * f i x := by
  have e := kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))
  have h1 := kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h
  rw [← e] at h1
  have h2 := kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)
  rw [one_smul] at h2
  have h3 := congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x
  simp only [one_mul, add_right_inj] at h3
  exact h3.symm

theorem kerDiag_basis_indep : ∀ (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund) (f f' : Fin D → B.I.GA → ℂ), Orthonormal ℂ y → Orthonormal ℂ y' → Submodule.span ℂ (Set.range y) = Submodule.span ℂ (Set.range y') → (∀ i, IsContRep B (y i) (f i) ∧ IsContRep B (y' i) (f' i)) → ∀ x, ∑ i, ‖f i x‖ ^ 2 = ∑ i, ‖f' i x‖ ^ 2 := by
  intro B D y y' f f' hy hy' hs h x
  apply le_antisymm
  · exact kerDiag_le y' y hy' hy _ _ fun j =>
      kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x
  · exact kerDiag_le y y' hy hy' _ _ fun j =>
      kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.CovolRat

theorem covol_eq_inter_fund : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  intro I μf _ _ fund A hfund hA hinv
  obtain ⟨hleft, -, -, -, hopen⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  obtain ⟨⟨Γ, hΓ⟩, hcount, -⟩ := GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨hmeas, hcov, hdisj⟩ := hfund

  have hm : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; exact SetLike.mem_coe.symm
  refine ⟨?_, ?_⟩
  · have key := GlobalTheory.covol_eq_measure_inter_fund I.GA Γ (I.muA μf) fund A (by rw [hΓ]; exact hcount)
      (fun γ _ => hleft γ) hmeas
      (fun y => by obtain ⟨γ, hγ, h⟩ := hcov y; exact ⟨γ, (hm γ).2 hγ, h⟩)
      (fun γ hγ h1 => hdisj γ ((hm γ).1 hγ) h1) hA (fun γ hγ x hx => hinv γ ((hm γ).1 hγ) x hx)
    rw [hΓ] at key
    exact key
  ·
    rw [pos_iff_ne_zero]
    intro h0
    have hpre : ∀ γ : I.GA, I.muA μf ((fun y => γ * y) ⁻¹' fund) = 0 := by
      intro γ
      rw [← Measure.map_apply (measurable_const_mul γ) hmeas, hleft γ, h0]
    have hsub : (Set.univ : Set I.GA) ⊆ ⋃ γ ∈ I.GFset, (fun y => γ * y) ⁻¹' fund := by
      intro y _
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact Set.mem_biUnion hγ h
    have hnull : I.muA μf Set.univ = 0 :=
      measure_mono_null hsub ((measure_biUnion_null_iff hcount).2 fun γ _ => hpre γ)
    have hpos := hopen Set.univ isOpen_univ ⟨1, trivial⟩
    rw [hnull] at hpos
    exact lt_irrefl _ hpos

end GlobalTheory.CovolRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslateLeMultiplicityFundamental
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.BoundedUnfold

theorem multiplicity_le (I : AutInst) (g : ℕ) (S : Set I.Ginf) (y z : I.GA) (hn : 1 ≤ I.n)
    (hS : ∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) :
    {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite ∧
    (({γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.ncard : ℕ) : ℝ) ≤
      (1 + 4 * Real.sqrt I.n / tau1 I y ^ 2) ^ (2 * (I.n ^ 2 * I.f)) := by
  classical
  have hτ : 0 < tau1 I y := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y
  rcases Set.eq_empty_or_nonempty
      {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} with h0 | ⟨γ0, hγ0⟩
  · rw [h0]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty, Nat.cast_zero]
    positivity
  · obtain ⟨hCfin, hCcard⟩ :=
      GlobalTheory.RationalCount.count_le I y y (fun _ => Real.log 2) hn (fun _ => (Real.log_pos one_lt_two).le)

    have hf : ∀ γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g},
        (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹) γ ∈
          {a : I.GA | a ∈ I.GFset ∧ (y⁻¹ * a * y).2 ∈ I.Kset ∧
            ∀ v, dOp (uMat ((y⁻¹ * a * y).1 v)) ≤ (fun _ => Real.log 2) v} := by
      intro γ hγ
      have hγ' : y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g := hγ
      have hγ0' : y⁻¹ * (γ0.1 * z) ∈ S ×ˢ I.Kg g := hγ0
      have key : y⁻¹ * (γ.1 * γ0.1⁻¹) * y = (y⁻¹ * (γ.1 * z)) * (y⁻¹ * (γ0.1 * z))⁻¹ := by
        group
      refine ⟨?_, ?_, ?_⟩
      · exact (GlobalTheory.RatDiscrete.ratSub I).mul_mem γ.2 ((GlobalTheory.RatDiscrete.ratSub I).inv_mem γ0.2)
      · rw [key]
        have h1 := hγ'.2.1
        have h2 := hγ0'.2.1
        simp only [AutInst.Kset, Set.mem_ofPred_eq] at h1 h2 ⊢
        rw [Prod.snd_mul, Prod.snd_inv]
        push_cast
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      · intro v
        rw [key, Prod.fst_mul, Prod.fst_inv]
        exact hS _ hγ'.1 _ hγ0'.1 v
    have hinj : Set.InjOn (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹)
        {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} :=
      fun a _ b _ hab => Subtype.ext (mul_right_cancel hab)
    have hAfin : {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite :=
      Set.Finite.of_finite_image (hCfin.subset (Set.image_subset_iff.2 hf)) hinj
    refine ⟨hAfin, ?_⟩
    refine le_trans (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn _ hf hinj hCfin)) (le_trans hCcard ?_)
    have hsum : (∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) = (I.f : ℝ) * Real.log 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, GlobalTheory.RationalCount.card_places]
    have hE : Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) ≤ 2 := by
      rw [hsum]
      rcases Nat.eq_zero_or_pos I.f with hf0 | hfpos
      · rw [hf0]; norm_num
      · have : (I.f : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'
        rw [mul_div_cancel_left₀ _ this, Real.exp_log two_pos]
    apply pow_le_pow_left₀ (by positivity)
    have h2 : 2 * Real.sqrt I.n * Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) /
        (tau1 I y * tau1 I y) ≤ 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by
      gcongr
    calc _ ≤ 1 + 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by linarith
      _ = 1 + 4 * Real.sqrt I.n / tau1 I y ^ 2 := by ring

theorem lintegral_le_multiplicity : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  intro B S y Φ hn hg hSm hS hΦ hΦl hΦr
  classical
  have hL : ∀ a : B.I.GA, Measurable (fun q : B.I.GA => a * q) := fun a =>
    (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf a).measurable
  have hKm : MeasurableSet (B.I.Kg B.g) :=
    ((GlobalTheory.CongTop.adelic_topology B.I).2.2.2.2.2.2 B.g hg).1.measurableSet
  have hUm : MeasurableSet (S ×ˢ B.I.Kg B.g) := hSm.prod hKm

  have step1 : B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) =
      ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) := by
    rw [AutInst.muA, ← Measure.prod_restrict, lintegral_prod (fun p => Φ (y * p)) (hΦ.comp (hL y)).aemeasurable]
    have inner : ∀ a : B.I.Ginf, ∫⁻ k in B.I.Kg B.g, Φ (y * (a, k)) ∂B.μf =
        Φ (y * (a, 1)) * B.μf (B.I.Kg B.g) := by
      intro a
      rw [← setLIntegral_const]
      refine setLIntegral_congr_fun hKm (fun k hk => ?_)
      have e : y * (a, k) = y * (a, 1) * (1, k) := by
        rw [mul_assoc]
        congr 1
        exact Prod.ext (mul_one a).symm (one_mul k).symm
      rw [e, hΦr k hk]
    simp_rw [inner]
    rw [lintegral_mul_const (f := fun a : B.I.Ginf => Φ (y * (a, 1))) _
      (hΦ.comp ((hL y).comp measurable_prodMk_right))]
    exact mul_comm _ _

  have hH : Measurable (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q)) :=
    ((hΦ.comp (hL y)).indicator hUm).comp (hL y⁻¹)
  have step2 : ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) =
      ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
    rw [← lintegral_indicator hUm,
      ← (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf y).lintegral_comp hH]
    congr 1
    funext a
    rw [inv_mul_cancel_left]

  have hfd := GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec
  have : Countable (GlobalTheory.RatDiscrete.ratSub B.I) :=
    Set.Countable.to_subtype (s := (GlobalTheory.RatDiscrete.ratSub B.I : Set B.I.GA))
      (GlobalTheory.RatDiscrete.countable_GFset B.I)
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA := ⟨fun c => hL c.1⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun c s hs => (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf c.1).measure_preimage
      hs.nullMeasurableSet⟩

  have hpt : ∀ z : B.I.GA, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
      (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ≤
        ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * Φ z := by
    intro z
    obtain ⟨hAf, hAc⟩ := multiplicity_le B.I B.g S y z hn hS
    have hHA : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) =
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator
            (fun _ => Φ z) γ := by
      intro γ
      by_cases h : y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
        show Φ (y * (y⁻¹ * (γ.1 * z))) = Φ z
        rw [mul_inv_cancel_left]
        exact hΦl γ.1 γ.2 z
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show γ ∉ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
    have hsum1 : ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
        {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ :=
      tsum_eq_sum (s := hAf.toFinset) (fun γ hγ => Set.indicator_of_notMem (by simpa using hγ) _)
    have hsum2 : ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset, Φ z :=
      Finset.sum_congr rfl (fun γ hγ => Set.indicator_of_mem (by simpa using hγ) _)
    rw [tsum_congr hHA, hsum1, hsum2, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hAf]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hAc
  calc B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I)
      = ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
        rw [step1, step2]
    _ = ∫⁻ z in B.fund, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
          (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ∂(B.I.muA B.μf) := by
        rw [hfd.lintegral_eq_tsum''
          (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q))]
        rw [lintegral_tsum (f := fun (γ : GlobalTheory.RatDiscrete.ratSub B.I) (z : B.I.GA) =>
            (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)))
          (fun γ => (hH.comp (hL γ.1)).aemeasurable)]
        simp only [Subgroup.smul_def]
        rfl
    _ ≤ ∫⁻ z in B.fund, ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^
          (2 * (B.I.n ^ 2 * B.I.f))) * Φ z ∂(B.I.muA B.μf) := lintegral_mono hpt
    _ = _ := lintegral_const_mul _ hΦ

end GlobalTheory.BoundedUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalL2BoundHeight
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff ENNReal

namespace GlobalTheory.LocMass

theorem setLIntegral_le_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ)
    {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) (hinv : ∀ᵐ y ∂μ, ∀ γ : Γ, f ((γ : G) * y) = f y)
    {S : Set G} (hS : MeasurableSet S) (N : ℝ≥0∞) (hN' : N ≠ ⊤)
    (hN : ∀ z : G, (({γ : Γ | (γ : G) * z ∈ S}.encard : ℕ∞) : ℝ≥0∞) ≤ N) :
    ∫⁻ y in S, f y ∂μ ≤ N * ∫⁻ y in D, f y ∂μ := by
  first
  | (rename_i h_1 h_2 h_3 h_4 h_5 h_7 h_9; revert G h_1 h_2 h_3 h_4 h_5 μ h_7 Γ h_9 D hD f hf hinv S hS N hN' hN; exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le)
  | exact @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le
  | (apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndicatorSumEncard.setLIntegral_le_mul_of_encard_le ..)

theorem encard_le {G : Type} [Group G] (Γ : Subgroup G) (U T : Set G) (x z : G)
    (hT : ∀ γ ∈ Γ, ∀ u ∈ U, ∀ u' ∈ U, x⁻¹ * γ * x = u * u'⁻¹ → γ ∈ T) :
    {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U}.encard ≤ T.encard := by
  rcases Set.eq_empty_or_nonempty {γ : Γ | (γ : G) * z ∈ (fun g => x⁻¹ * g) ⁻¹' U} with h | ⟨γ₀, h0⟩
  · rw [h]; simp
  · refine Set.encard_le_encard_of_injOn (f := fun γ : Γ => ((γ * γ₀⁻¹ : Γ) : G)) ?_ ?_
    · intro γ hγ
      refine hT _ (γ * γ₀⁻¹).2 _ hγ _ h0 ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro a _ b _ hab
      exact mul_right_cancel (Subtype.ext hab)

theorem local_mass_le : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  intro B U hn hU hK
  obtain ⟨hT2, hL, hS, -, -, ⟨K, hKK⟩, -⟩ := _root_.GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := _root_.GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have hfund := B.fund_spec
  have hD := hfd B.μf B.fund hfund
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have hr : ∀ y, ∃ γ : Γ, B.I.rep B.fund y = (γ : B.I.GA) * y ∧ B.I.rep B.fund y ∈ B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : B.I.rep B.fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hb : ∀ v : InfinitePlace B.I.F, ∃ r : ℝ, 0 ≤ r ∧ ∀ u ∈ U, ∀ u' ∈ U,
      dOp (uMat ((u * u'⁻¹).1 v)) ≤ r := by
    intro v
    have hc : Continuous fun p : B.I.GA × B.I.GA => dOp (uMat ((p.1 * p.2⁻¹).1 v)) :=
      (GlobalTheory.Count.Cartan.cartan_distances B.I.n (B.I.ε v)).2.2.2.2.comp
        ((continuous_apply v).comp (continuous_fst.comp (continuous_fst.mul continuous_snd.inv)))
    obtain ⟨r, hr⟩ := (hU.prod hU).bddAbove_image hc.continuousOn
    exact ⟨max r 0, le_max_right _ _, fun u hu u' hu' =>
      (hr ⟨(u, u'), ⟨hu, hu'⟩, rfl⟩).trans (le_max_left _ _)⟩
  choose r hr0 hrb using hb
  refine ⟨(3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v),
    by positivity, fun y x => ?_⟩
  obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.Dec.BoundedDistance.countRat B.I x x r hn hr0
  obtain ⟨hinv, hmeas⟩ := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y
  set N : ℝ := (3 * Real.sqrt B.I.n) ^ (2 * B.I.n ^ 2 * B.I.f) *
    Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) with hN
  have hNe : (3 * Real.sqrt B.I.n / (tau1 B.I x * tau1 B.I x)) ^ (2 * B.I.n ^ 2 * B.I.f) *
      Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) = N := by
    rw [hN, div_eq_mul_inv, mul_inv, mul_pow, mul_pow (tau1 B.I x)⁻¹, ← pow_add,
      show 2 * B.I.n ^ 2 * B.I.f + 2 * B.I.n ^ 2 * B.I.f = 4 * B.I.n ^ 2 * B.I.f by ring]
    ring
  rw [hNe] at hcard
  have hN0 : 0 ≤ N := (Nat.cast_nonneg _).trans hcard
  have hUm : MeasurableSet U := hU.measurableSet
  have hSm : MeasurableSet ((fun g => x⁻¹ * g) ⁻¹' U) := measurable_const_mul _ hUm
  have h1 := (measurePreserving_mul_left (B.I.muA B.μf) x⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft x⁻¹) (fun g => (‖B.I.ext y (x * g)‖₊ : ℝ≥0∞) ^ 2) U
  simp only [mul_inv_cancel_left] at h1
  rw [← h1]
  have h2 := setLIntegral_le_mul hD (f := fun g => (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2)
    (hmeas.enorm.pow_const 2)
    (hinv.mono fun z hz γ => by rw [hz γ (hΓ ▸ γ.2)]) hSm (ENNReal.ofReal N) ENNReal.ofReal_ne_top
    (fun z => by
      have := encard_le Γ U {γ ∈ B.I.GFset | (x⁻¹ * γ * x).2 ∈ B.I.Kset ∧
          ∀ v, dOp (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v} x z (fun γ hγ u hu u' hu' e => by
        refine ⟨hΓ ▸ hγ, ?_, fun v => ?_⟩
        · rw [e, ← hKK]
          have h1 : u.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u hu
          have h2 : u'.2 ∈ K := by rw [← SetLike.mem_coe, hKK]; exact hK u' hu'
          exact K.mul_mem h1 (K.inv_mem h2)
        · rw [e]; exact hrb v u hu u' hu')
      refine (ENat.toENNReal_le.2 this).trans ?_
      rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hcard)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hN0]
  congr 1
  have h3 : ∫⁻ g in B.fund, (‖B.I.ext y g‖₊ : ℝ≥0∞) ^ 2 ∂(B.I.muA B.μf) =
      ∫⁻ g in B.fund, ‖(y : B.I.GA → ℂ) g‖ₑ ^ (2 : ℝ) ∂(B.I.muA B.μf) := by
    refine lintegral_congr_ae ((GlobalTheory.RightRegFund.ae_rep_eq_self hD hfund.1 hr).mono fun z hz => ?_)
    simp only [AutInst.ext, hz]
    rw [ENNReal.rpow_two]; rfl
  rw [h3, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, Lp.enorm_def,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num
  exact Lp.aestronglyMeasurable y

end GlobalTheory.LocMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesSecond
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMoment

theorem prod_ratio {r : ℕ} (l : Fin (r + 1) → ℝ) (hl : ∀ a, 0 < l a) (a : Fin (r + 1)) :
    ∏ c ∈ Finset.univ.filter (fun c : Fin r => a.val ≤ c.val), l c.succ / l c.castSucc
      = l (Fin.last r) / l a := by
  induction a using Fin.reverseInduction with
  | last =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.last r).val ≤ c.val) = ∅ := by
      ext c
      have := c.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last, Finset.notMem_empty, iff_false]
      omega
    rw [this, Finset.prod_empty, div_self (hl _).ne']
  | cast i ih =>
    have : Finset.univ.filter (fun c : Fin r => (Fin.castSucc i).val ≤ c.val)
        = insert i (Finset.univ.filter (fun c : Fin r => (Fin.succ i).val ≤ c.val)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.val_succ,
        Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [this, Finset.prod_insert (by simp), ih]
    have h1 := (hl i.succ).ne'
    have h2 := (hl i.castSucc).ne'
    field_simp

end GlobalTheory.InvLenMoment
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoSmallBallDensityOfSqueezeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_small_ball_density_of_squeeze : ∀ (f : ℝ → ENNReal) (d : ℕ) (v : ENNReal), v ≠ ⊤ → (∀ η : ℝ, 0 < η → ∃ b : ℝ → ENNReal, Filter.Tendsto (fun r : ℝ => b r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) ∧ ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), b (r / (1 + η)) ≤ ENNReal.ofReal (1 + η) * f r ∧ f r ≤ ENNReal.ofReal (1 + η) * b ((1 + η) * r)) → Filter.Tendsto (fun r : ℝ => f r / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v) := by
  first | exact @GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | exact GlobalTheory.IwConst.tendsto_div_pow_of_squeeze | (intros; apply GlobalTheory.IwConst.tendsto_div_pow_of_squeeze <;> assumption)
end

