module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import ReciprocityTheory.AdicCompleteness.IsAdicCompleteComapConstantCoeff
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0167
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacter
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.NormSign

open NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

noncomputable def snorm (x : mixedSpace K) : ℝ :=
  (∏ w, x.1 w) * ∏ w, ‖x.2 w‖ ^ 2

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.snorm_mul {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by
  simp only [_root_.GlobalTheory.NormSign.snorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]
  ring

theorem snorm_smul (t : ℝ) (ht : 0 < t) (x : mixedSpace K) :
    ∃ c : ℝ, 0 < c ∧ snorm (t • x) = c * snorm x := by
  refine ⟨(∏ _w : {w : InfinitePlace K // IsReal w}, t) *
    ∏ _w : {w : InfinitePlace K // IsComplex w}, t ^ 2, by positivity, ?_⟩
  simp only [snorm, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, _root_.norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, mul_pow, Finset.prod_mul_distrib]
  ring

theorem continuous_snorm : Continuous (snorm : mixedSpace K → ℝ) := by
  unfold snorm
  fun_prop

theorem abs_snorm (x : mixedSpace K) : |snorm x| = mixedEmbedding.norm x := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod, snorm, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2, abs_of_nonneg (by positivity)]

theorem snorm_mixedEmbedding (x : K) :
    snorm (mixedEmbedding K x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast, ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x)
      (fun φ => φ x) fun _ => by simp [RingHom.equivRatAlgHom_apply]] at h
  rw [Complex.ofReal_ratCast, h, ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x),
    prod_eq_prod_mul_prod, snorm, Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod]
  have key : ∀ w : InfinitePlace K, (Finset.univ.filter fun φ : K →+* ℂ => InfinitePlace.mk φ = w)
      = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    intro w
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [key, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp w.2), Finset.pair_eq_singleton,
      Finset.prod_singleton, mixedEmbedding_apply_isReal, embedding_of_isReal_apply]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have hne : w.1.embedding ≠ ComplexEmbedding.conjugate w.1.embedding := by
      rw [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff]
      exact not_isReal_iff_isComplex.mpr w.2
    rw [key, Finset.prod_pair hne, mixedEmbedding_apply_isComplex,
      ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj, Complex.normSq_eq_norm_sq]

noncomputable def sgn (ε : ℂ) (t : ℝ) : ℂ := if 0 < t then 1 else if t < 0 then ε else 0

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial in
open scoped ContDiff Classical in
open NumberField.InfinitePlace in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.NormSign.sgn_mul {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    _root_.GlobalTheory.NormSign.sgn ε (a * b) = _root_.GlobalTheory.NormSign.sgn ε a * _root_.GlobalTheory.NormSign.sgn ε b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_pos_of_neg_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, hb.not_gt, hε]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_neg_of_neg_of_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, ha.not_gt, h.not_gt]
  · simp [_root_.GlobalTheory.NormSign.sgn]
  · rcases lt_trichotomy b 0 with hb | rfl | hb
    · have h := mul_neg_of_pos_of_neg ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h, hb.not_gt, h.not_gt]
    · simp [_root_.GlobalTheory.NormSign.sgn]
    · have h := mul_pos ha hb
      simp [_root_.GlobalTheory.NormSign.sgn, ha, hb, h]

theorem norm_sgn {ε : ℂ} (hε : ε * ε = 1) {a : ℝ} (ha : a ≠ 0) : ‖sgn ε a‖ = 1 := by
  have h : ‖ε‖ = 1 := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  rcases lt_or_gt_of_ne ha with h' | h'
  · simp [sgn, h', h'.not_gt, h]
  · simp [sgn, h']

theorem exists_normSign (K : Type) [Field K] [NumberField K] (ε : ℂ) (hε : ε * ε = 1) :
    ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧
      (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧
      ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧
      (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧
      ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  have hne : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 → snorm x ≠ 0 := fun x hx => by
    rwa [← abs_snorm, abs_ne_zero] at hx
  refine ⟨fun x => sgn ε (snorm x), fun x y => ?_, fun t x ht => ?_, fun x hx => ?_,
    fun x hx => norm_sgn hε (hne x hx), fun β hβ => ?_⟩
  · simp only [snorm_mul, sgn_mul hε]
  · obtain ⟨c, hc, h⟩ := snorm_smul t ht x
    simp only [h, sgn_mul hε]
    simp [sgn, hc]
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const (c := sgn ε (snorm x))).congr_of_eventuallyEq ?_
    rcases lt_or_gt_of_ne (hne x hx) with h | h
    · filter_upwards [continuous_snorm.continuousAt.eventually (gt_mem_nhds h)] with y hy
      simp [sgn, h, hy, h.not_gt, hy.not_gt]
    · filter_upwards [continuous_snorm.continuousAt.eventually (lt_mem_nhds h)] with y hy
      simp [sgn, h, hy]
  · have h0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    simp only [snorm_mixedEmbedding, ← Algebra.coe_norm_int, Rat.cast_intCast, sgn,
      Int.cast_pos, Int.cast_lt_zero]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [h, h.not_gt]
    · simp [h]

end GlobalTheory.NormSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueEv
section
namespace GlobalTheory.HWL.SeriesEval

open PowerSeries IsLocalRing Filter Topology

section Shift

variable {O : Type*} [CommRing O] [IsLocalRing O]

theorem X_add_C_mem {c : O} (hc : c ∈ maximalIdeal O) : (X + C c : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ := by
  rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
  simpa using hc

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

theorem exists_shift {c : O} (hc : c ∈ maximalIdeal O) :
    ∃ s : O⟦X⟧ →ₐ[O] O⟦X⟧, s X = X + C c := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  exact ⟨GlobalTheory.mvEvalAdic (σ := Unit) O (maximalIdeal O⟦X⟧) (fun _ => X + C c)
    (fun _ => X_add_C_mem hc), GlobalTheory.mvEvalAdic_X (σ := Unit) _ _ _ ()⟩

theorem exists_div {c : O} (hc : c ∈ maximalIdeal O) (b : O⟦X⟧) :
    ∃ (r : O) (q : O⟦X⟧), b = C r + (X - C c) * q := by
  have : IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := ReciprocityTheory.P1.isAdicComplete_ps
  obtain ⟨s, hs⟩ := exists_shift hc
  obtain ⟨s', hs'⟩ := exists_shift (neg_mem hc)
  have hC : ∀ r, s' (C r) = C r := fun r => s'.commutes r
  have hX : (s'.comp s) X = X := by
    rw [AlgHom.comp_apply, hs, map_add (f := _), hs', hC, map_neg]; ring
  have h : s'.comp s = AlgHom.id O O⟦X⟧ :=
    GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (σ := Unit) (maximalIdeal O⟦X⟧)
      (fun _ => by
        change (s'.comp s) X ∈ _
        rw [hX]; simpa using X_add_C_mem (zero_mem (maximalIdeal O)))
      (fun _ => hX)
  refine ⟨constantCoeff (s b), s' (mk fun p => coeff (p + 1) (s b)), ?_⟩
  have h1 : s' (s b) = b := DFunLike.congr_fun h b
  conv_lhs => rw [← h1, eq_X_mul_shift_add_const (s b)]
  rw [map_add (f := _), map_mul, hs', hC, map_neg]
  ring

variable {L : Type*} [CommRing L] [Algebra O L]

theorem exists_ev {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) : ∃ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x := by
  obtain ⟨s, hs⟩ := exists_shift hc
  have hy : HasSubst (x - C (algebraMap O L c)) :=
    HasSubst.of_constantCoeff_zero' (by simp [hx])
  refine ⟨(substAlgHom hy).comp s, ?_⟩
  have hC : (substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧) (C c) = C (algebraMap O L c) :=
    ((substAlgHom hy : O⟦X⟧ →ₐ[O] L⟦X⟧).commutes c).trans (PowerSeries.algebraMap_apply (r := c))
  rw [AlgHom.comp_apply, hs, map_add (f := _), substAlgHom_X, hC]
  ring

theorem ev_div {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) :
    ∃ z : L⟦X⟧, ∀ b : O⟦X⟧, ∃ (r : O) (q : O⟦X⟧), ∀ ev : O⟦X⟧ →ₐ[O] L⟦X⟧, ev X = x →
      ev b = C (algebraMap O L r) + X * (z * ev q) := by
  refine ⟨mk fun p => coeff (p + 1) x, fun b => ?_⟩
  obtain ⟨r, q, rfl⟩ := exists_div hc b
  refine ⟨r, q, fun ev hev => ?_⟩
  have hC : ∀ r, ev (C r) = C (algebraMap O L r) := fun r =>
    (ev.commutes r).trans PowerSeries.algebraMap_apply
  rw [map_add (f := _), map_mul, map_sub, hC, hC, hev, ← hx, ← mul_assoc]
  congr 2
  rw [sub_eq_iff_eq_add]
  exact eq_X_mul_shift_add_const x

theorem ev_unique {c : O} (hc : c ∈ maximalIdeal O) (x : L⟦X⟧)
    (hx : constantCoeff x = algebraMap O L c) (ev ev' : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (h' : ev' X = x) : ev = ev' := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  have key : ∀ (k : ℕ) (b : O⟦X⟧), X ^ k ∣ ev b - ev' b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b
      obtain ⟨r, q, hq⟩ := hz b
      have : ev b - ev' b = X * (z * (ev q - ev' q)) := by rw [hq ev h, hq ev' h']; ring
      rw [this, pow_succ']
      exact mul_dvd_mul_left _ ((ih q).mul_left z)
  refine AlgHom.ext fun b => PowerSeries.ext fun k => ?_
  have := X_pow_dvd_iff.1 (key (k + 1) b) k k.lt_succ_self
  rwa [map_sub, sub_eq_zero] at this

variable {K : Type*} [NormedField K] (i : L →+* K)

theorem ev_bounded (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (k : ℕ) : ∃ B : ℝ, ∀ b, ‖i (coeff k (ev b))‖ ≤ B := by
  obtain ⟨z, hz⟩ := ev_div hc x hx
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · refine ⟨1, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      simpa [hq ev h] using hi r
    · choose! B hB using ih
      refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ‖i (coeff p.1 z)‖ * B p.2, fun b => ?_⟩
      obtain ⟨r, q, hq⟩ := hz b
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hq ev h, map_add (f := _), coeff_succ_X_mul, coeff_C, if_neg k.succ_ne_zero, zero_add, coeff_mul,
        map_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
      rw [map_mul, norm_mul]
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact mul_le_mul_of_nonneg_left (hB _ (by omega) _) (norm_nonneg _)

theorem ev_tendsto (hi : ∀ r : O, ‖i (algebraMap O L r)‖ ≤ 1) {c : O} (hc : c ∈ maximalIdeal O)
    (hc1 : ‖i (algebraMap O L c)‖ < 1)
    (x : L⟦X⟧) (hx : constantCoeff x = algebraMap O L c) (ev : O⟦X⟧ →ₐ[O] L⟦X⟧) (h : ev X = x)
    (a : O⟦X⟧) (k : ℕ) :
    Tendsto (fun m : ℕ => i (coeff k (ev ((trunc m a : Polynomial O) : O⟦X⟧)))) atTop
      (𝓝 (i (coeff k (ev a)))) := by
  obtain ⟨B, hB⟩ := ev_bounded i hi hc x hx ev h k
  have hC : ev (C c) = C (algebraMap O L c) := (ev.commutes c).trans PowerSeries.algebraMap_apply
  rw [← tendsto_add_atTop_iff_nat k, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun n => ‖i (algebraMap O L c)‖ ^ n * B)
    (fun n => ?_) (by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc1).mul_const B)
  obtain ⟨b, hb⟩ : X ^ (n + k) ∣ ((trunc (n + k) a : Polynomial O) : O⟦X⟧) - a :=
    X_pow_dvd_iff.2 fun m hm => by simp [coeff_trunc, hm]
  have hmem : (C c + (X - C c) : O⟦X⟧) ^ (n + (k + 1) - 1) ∈
      Ideal.span {C c ^ n, (X - C c) ^ (k + 1)} :=
    Ideal.add_pow_add_pred_mem_of_pow_mem_of_commute _
      (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)) (Commute.all _ _)
  rw [add_sub_cancel, show n + (k + 1) - 1 = n + k by omega, Ideal.mem_span_pair] at hmem
  obtain ⟨u, v, huv⟩ := hmem
  have hy : X ∣ x - C (algebraMap O L c) := X_dvd_iff.2 (by simp [hx])
  have h0 : coeff k ((x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b)) = 0 :=
    X_pow_dvd_iff.1 ((pow_dvd_pow_of_dvd hy _).mul_right _) k k.lt_succ_self
  have he : ev (X ^ (n + k) * b) = C (algebraMap O L c ^ n) * ev (u * b) +
      (x - C (algebraMap O L c)) ^ (k + 1) * ev (v * b) := by
    rw [← huv]
    simp only [map_mul, map_add (f := _), map_pow, map_sub, hC, h]
    ring
  rw [← map_sub, ← map_sub, ← map_sub, hb, he, map_add (f := _), h0, add_zero, coeff_C_mul, map_mul,
    norm_mul, map_pow, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

end Shift

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem existsUnique_ev : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : PowerSeries ↥LL.1),
    ‖((PowerSeries.constantCoeff x : ↥LL.1) : Om l)‖ < 1 →
    (∃! ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x) ∧
    ∀ ev : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1, ev PowerSeries.X = x →
      ∀ (a : PowerSeries ↥(OL LL)) (k : ℕ), Filter.Tendsto (fun m : ℕ =>
        ((PowerSeries.coeff k (ev ((PowerSeries.trunc m a : Polynomial ↥(OL LL)) :
          PowerSeries ↥(OL LL))) : ↥LL.1) : Om l)) Filter.atTop
        (nhds ((PowerSeries.coeff k (ev a) : ↥LL.1) : Om l)) := by
  intro l _ LL x hx
  obtain ⟨dvr, hcomp, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have : IsLocalRing ↥(OL LL) := dvr.toIsLocalRing
  have hfin := LL.2
  have hn : ∀ y : ↥LL.1, ‖GlobalTheory.DiscEval.fieldEmb LL.1 y‖ = ‖(y : Om l)‖ := fun y => by
    rw [GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hi : ∀ r : ↥(OL LL), ‖algebraMap ↥LL.1 (Om l) (algebraMap ↥(OL LL) ↥LL.1 r)‖ ≤ 1 :=
    fun r => (hn r).ge.trans ((GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 r).1 r.2)
  let c : ↥(OL LL) := ⟨constantCoeff x,
    (GlobalTheory.DiscEval.mem_integralClosure_iff_norm LL.1 _).2 ((hn _).trans_le hx.le)⟩
  have hxc : constantCoeff x = algebraMap ↥(OL LL) ↥LL.1 c := rfl
  have hc : c ∈ maximalIdeal ↥(OL LL) := fun hu =>
    ((hn _).trans_lt hx).ne ((GlobalTheory.DiscEval.isUnit_iff_norm LL.1 c).1 hu)
  have hinst : ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = MvPowerSeries.instAlgebra :=
    Algebra.algebra_ext _ _ fun r =>
      (PowerSeries.algebraMap_apply (R := ↥(OL LL)) (A := ↥LL.1) (r := r)).symm
  generalize ((OL LL).toAlgebra : Algebra ↥(OL LL) (↥LL.1)⟦X⟧) = inst at hinst ⊢
  subst hinst
  refine ⟨?_, fun ev hev a k =>
    ev_tendsto (algebraMap ↥LL.1 (Om l)) hi hc hx x hxc ev hev a k⟩
  obtain ⟨ev, hev⟩ := exists_ev hc x hxc
  exact ⟨ev, hev, fun ev' hev' => ev_unique hc x hxc ev' ev hev' hev⟩

end GlobalTheory.HWL.SeriesEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal ReciprocityTheory.ChartRestriction.T2

namespace GlobalTheory.FinIsoDualLattice

theorem finIso_of_localTateDuality (hT : Formalism.GaloisCohomology.LocalTateDualityK) : FinIso := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hO i D hD
  obtain ⟨hR, hC, hT2, hA, hpm, hp0⟩ := hO
  haveI := hR; haveI := hC; haveI := hT2; haveI := hD.t2'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hFin, hFree⟩ := _root_.GlobalTheory.dualLat_finite_free D.bT D.T hD.lat hD.perf
  haveI := hFin; haveI := hFree
  obtain ⟨hcpl, hsep⟩ := _root_.GlobalTheory.compact_dvr_complete_separated hA ϖ hϖ
  obtain ⟨hcT, hsT⟩ := GlobalTheory.freeModule_adicComplete_separated ϖ hcpl hsep (↥D.T')
  obtain ⟨hcomp, hopen, hemb⟩ := GlobalTheory.T.finite_free_module_compact_adic_dvr hA (M := ↥D.T') ϖ hϖ
  haveI := hcomp
  have hρ : ContAction D.ρTl' := sub_contAction D.contT' D.T' D.stT'
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rwa [← Irreducible.maximalIdeal_eq hϖ]
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.modpi_cocycles_finite_classes hT hK i D.ρTl' hρ ϖ hpϖ hopen
  have hl := GlobalTheory.T.cocycle_eq_add_uniformizer_smul_add_coboundary D.ρTl' hρ ϖ hemb.isEmbedding s hs
  have hd : ∀ t : ↥D.T', d0 D.ρTl' t ∈ Z1 D.ρTl' := fun t => by
    refine ⟨?_, fun g h => ?_⟩
    · exact (hρ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel
  let d : ↥D.T' →ₗ[O] ↥(Z1 D.ρTl') := LinearMap.codRestrict _ (d0 D.ρTl') hd
  have hdN : LinearMap.range d ≤ (B1 D.ρTl').comap (Z1 D.ρTl').subtype := by
    rintro _ ⟨t, rfl⟩; exact ⟨t, rfl⟩
  have hZ : ∀ c : ↥(Z1 D.ρTl'), (∀ n : ℕ, ∃ z : ↥(Z1 D.ρTl'), c = ϖ ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext; funext g
    exact hsT _ fun n => by
      obtain ⟨z, hz⟩ := hc n
      exact ⟨(z : G → ↥D.T') g, by rw [hz]; rfl⟩
  refine GlobalTheory.finite_quotient_of_complete_nakayama ϖ hcpl hcT hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', x, hx⟩ := hl c
  refine ⟨a, c', x, Subtype.ext ?_⟩
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, d, LinearMap.codRestrict_apply]
  exact hx

end GlobalTheory.FinIsoDualLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2TwistFromOpenUnion
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

theorem h2_twist_exists_of_iUnion_open : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (ε : G →* Oˣ) {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul O M] (N : ℕ → Submodule O M), Monotone N → (∀ n, IsOpen (N n : Set M)) → (∀ x, ∃ n, x ∈ N n) →
    ∀ z : H2 (twist ε M), ∃ n, ∃ z' : H2 (twist ε (N n)),
      mapH2 (twist ε (N n)) (twist ε M) (N n).subtype continuous_subtype_val (twist_map ε (N n).subtype) z' = z := by
  intro O _ _ G _ _ _ ε M _ _ _ _ _ N hmono hopen hcov z
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hK : IsCompact (Set.range f.1) := isCompact_range f.2.1
  have hmono' : Monotone (fun n => (N n : Set M)) := fun a b h => SetLike.coe_subset_coe.mpr (hmono h)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover (fun n => (N n : Set M)) hopen
    (fun x _ => Set.mem_iUnion.mpr (hcov x)) hmono'.directed_le
  let f' : G × G → N n := fun x => ⟨f.1 x, hn ⟨x, rfl⟩⟩
  have hc : Continuous f' := f.2.1.subtype_mk _
  have hcoc : f' ∈ Z2 (twist ε (N n)) := by
    refine ⟨hc, fun g h k => ?_⟩
    apply Subtype.ext
    have e := f.2.2 g h k
    have key : ∀ x : N n, ((twist ε (N n) g x : N n) : M) = twist ε M g (x : M) := fun x => rfl
    simpa [f', key] using e
  refine ⟨n, Submodule.Quotient.mk ⟨f', hcoc⟩, ?_⟩
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
section
open ReciprocityTheory.Gal
open Formalism.NG
namespace GlobalTheory

theorem hcLC_exists_pow_smul_eq_zero : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O),
    (∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0) → ∀ x ∈ ReciprocityTheory.ChartRestriction.T2.HcLC ρ, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ G _ _ _ M _ _ ρ ϖ hM x hx
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hx
  have hlc : IsLocallyConstant (c : G → M) := hc
  classical
  let f : M → ℕ := fun m => Classical.choose (hM m)
  have hf : ∀ m, ϖ ^ f m • m = 0 := fun m => Classical.choose_spec (hM m)
  have hfin : (Set.range (c : G → M)).Finite := hlc.range_finite
  obtain ⟨N, hN⟩ := (hfin.image f).bddAbove
  refine ⟨N, ?_⟩
  have hc0 : ϖ ^ N • c = 0 := by
    apply Subtype.ext
    funext g
    have hk : f ((c : G → M) g) ≤ N := hN ⟨_, ⟨g, rfl⟩, rfl⟩
    show ϖ ^ N • (c : G → M) g = 0
    rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hf, smul_zero]
  rw [← LinearMap.map_smul, hc0, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSubSubMemXiOfMonodromyEq
section
open PowerSeries GlobalTheory.BK

theorem GlobalTheory.BK.BKDat.phi_sub_sub_mem_xi : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, ∀ σ : Vec K a ι, D.conn σ = D.zeta y → ∃ d : D.D, D.phi σ - σ - D.phi y = D.xi d := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y hy σ hσ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hyl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hy⟩
  obtain ⟨⟨s, -, -, hs, d, -, hd⟩, -⟩ := _root_.GlobalTheory.BK.BKDat.Mon_mem_range_Lc O K l e a ι η H D y hyl
  have h0 : D.conn (σ - s) = 0 := by rw [map_sub, hσ, hs, sub_self]
  set w := D.xiExt.symm (σ - s) with hw
  have hder : derV w = 0 := by
    have h1 : D.conn (D.xiExt w) = 0 := by rw [hw, LinearEquiv.apply_symm_apply]; exact h0
    rw [PhiMod.conn_apply, PhiMod.nabla_xiExt] at h1
    have h2 : D.xiExt (derV w) = 0 :=
      smul_right_injective (Vec K a ι) (X_ne_zero (R := K)) (by simpa only [smul_zero] using h1)
    exact D.xiExt.map_eq_zero_iff.1 h2
  have hwc : w = cst (red w) := by
    ext τ i n
    have h3 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
    rw [derV_apply, coeff_derivative] at h3
    rcases n with _ | n
    · simp [red_apply, red0]
    · have h4 := congrArg (coeff n) (congrFun (congrFun hder τ) i)
      rw [derV_apply, coeff_derivative] at h4
      simp only [Pi.zero_apply, map_zero, mul_eq_zero] at h4
      rw [cst_apply, coeff_C, if_neg (Nat.succ_ne_zero n)]
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd h4 (by exact_mod_cast Nat.succ_ne_zero n)
  have hxi : σ - s = D.xi (red w) := by
    rw [PhiMod.xi_apply, ← hwc, hw, LinearEquiv.apply_symm_apply]
  refine ⟨d + D.phiD (red w) - red w, ?_⟩
  rw [map_sub, map_add (f := _), ← PhiMod.phi_xi, ← hxi, ← hd, map_sub]
  abel
end

