module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.FlatDisc
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem exists_eq_add (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * Q := by
  have hd : ∀ i ∈ Finset.range bk.Ep.natDegree, ∃ c, bk.Ep.coeff i = (l : Wq l bk.a) * c :=
    fun i hi => bk.dvd_coeff i (Finset.mem_range.1 hi)
  choose d hd using hd
  refine ⟨∑ i ∈ (Finset.range bk.Ep.natDegree).attach, Polynomial.C (d i.1 i.2) * Polynomial.X ^ i.1, ?_⟩
  refine bk.monic.as_sum.trans (congrArg (Polynomial.X ^ bk.Ep.natDegree + ·) ?_)
  rw [Finset.mul_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i.1 i.2, Polynomial.C_mul, mul_assoc]

theorem exists_E_eq (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (Q : bk.S) := by
  obtain ⟨Q, hQ⟩ := exists_eq_add bk
  refine ⟨Q, ?_⟩
  change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  conv_lhs => rw [hQ]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_natCast]

theorem ev_coe (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    bk.ev (p : bk.S) = p.eval₂ (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
  have h : bk.ev.comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
      Polynomial.eval₂RingHom (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun h p

theorem theta_ev_E (bk : BK K) : Per.θ l (bk.ev bk.E) = 0 := by
  have h : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  exact h

theorem natCast_l_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem flat_ne_zero (bk : BK K) : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0, WittVector.teichmuller_zero]
  have h := theta_ev_E bk
  rw [BK.E, ev_coe, hX, Polynomial.eval₂_at_zero, RingHom.comp_apply, bk.ev_C] at h
  obtain ⟨w, hw⟩ := bk.coeff_zero
  rw [hw, map_mul, map_natCast, map_mul, map_natCast] at h
  have hu : IsUnit (Per.θ l (wA l bk.a (w : Wq l bk.a))) := (w.isUnit.map (wA l bk.a)).map (Per.θ l)
  exact natCast_l_ne_zero ((mul_eq_zero.1 h).resolve_right hu.ne_zero)

theorem not_isUnit_flat (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have h := theta_ev_E bk
  rw [hQ, map_add (f := _), map_mul, map_pow, map_natCast, bk.ev_X, map_add (f := _), map_mul, map_pow, map_natCast] at h
  have h1 : IsUnit (Per.θ l (WittVector.teichmuller l bk.flat) ^ bk.Ep.natDegree) :=
    ((hu.map (WittVector.teichmuller l)).map (Per.θ l)).pow _
  rw [eq_neg_of_add_eq_zero_left h, IsUnit.neg_iff] at h1
  exact OC_l_not_unit l (isUnit_of_mul_isUnit_left h1)

theorem rho_spec (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    rw [neg_lt_zero]; positivity), ?_⟩
  rw [BK.ρ₀, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he.ne', NNReal.rpow_neg_one]

theorem J_eq (bk : BK K) :
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have hl : (l : bk.S) * (Q : bk.S) ∈ Ideal.span {(l : bk.S)} := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    have : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (Q : bk.S) := by rw [hQ]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)
  · rw [Ideal.span_singleton_le_iff_mem, hQ]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)

end GlobalTheory.BSP.FlatDisc

theorem GlobalTheory.BSP.flat_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧
    (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J :=
  fun _ _ _ bk => ⟨FlatDisc.flat_ne_zero bk, FlatDisc.not_isUnit_flat bk, FlatDisc.rho_spec bk, FlatDisc.J_eq bk⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem norm_E_le_radius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ ((l : ℝ)⁻¹ ≤ bk.ρ₀) ∧ ‖toDisc l (s X) bk.ρ₀ (s bk.E)‖ ≤ (l : ℝ)⁻¹ := by
  intro l hl K bk A _ s
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ : ((bk.ρ₀ : ℝ≥0) : ℝ) = (l : ℝ) ^ (-(1 / (bk.Ep.natDegree : ℝ))) := by
    simp [BK.ρ₀, NNReal.coe_rpow]
  have hρpos : 0 < bk.ρ₀ := by
    rw [← NNReal.coe_pos, hρ]; exact Real.rpow_pos_of_pos hl0 _
  have hρe : ((bk.ρ₀ : ℝ)) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
    have : -(1 / (bk.Ep.natDegree : ℝ)) * (bk.Ep.natDegree : ℝ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
  refine ⟨hρpos, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, hρ, NNReal.coe_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))
  · rw [hρ, ← Real.rpow_neg_one]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : 1 / (bk.Ep.natDegree : ℝ) ≤ 1 := by
      rw [div_le_one he]; exact_mod_cast bk.deg_pos
    linarith
  · have hE : bk.E = X ^ bk.Ep.natDegree + ∑ i ∈ Finset.range bk.Ep.natDegree, C (bk.Ep.coeff i) * X ^ i := by
      show (bk.Ep : (Wq l bk.a)⟦X⟧) = _
      conv_lhs => rw [bk.monic.as_sum]
      simp only [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp
    have hmem : algebraMap A (PreDisc l (s X) bk.ρ₀) (s bk.E) ∈ ball l (s X) bk.ρ₀ (l : ℝ)⁻¹ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hE, map_add (f := _), map_add (f := _), map_sum, map_sum]
      refine add_mem ?_ (Submodule.sum_mem _ fun i hi => ?_)
      · refine Submodule.subset_span ⟨0, bk.Ep.natDegree, 0, ?_, ?_⟩
        · simp [hρe]
        · simp [map_pow]
      · obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
        have h2 : algebraMap A (PreDisc l (s X) bk.ρ₀) (s (C (bk.Ep.coeff i) * X ^ i)) =
            s (C c * X ^ i) • (algebraMap A (PreDisc l (s X) bk.ρ₀) ((l : A) ^ 1 * (s X) ^ 0) *
              IsLocalization.Away.invSelf (l : A) ^ 0) := by
          rw [hc, Algebra.smul_def]
          simp only [map_mul, map_natCast, map_pow, pow_one, pow_zero, mul_one]
          ring
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], rfl⟩)
    exact (norm_ofPre l (s X) bk.ρ₀ _).trans_le (gauge_le l (s X) bk.ρ₀ (by positivity) hmem)
end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturated
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime]

theorem ainf_exists_l_mul_of_coeff_zero (a : Ainf l) (h : a.coeff 0 = 0) :
    ∃ b : Ainf l, a = (l : Ainf l) * b := by
  have hv := WittVector.eq_iterate_verschiebung (n := 1) (x := a) (fun i hi => by
    rw [Nat.lt_one_iff.1 hi]; exact h)
  have hsurj : Function.Surjective (WittVector.frobenius : Ainf l → Ainf l) := by
    rw [WittVector.frobenius_eq_map_frobenius]
    exact WittVector.map_surjective _ (frobeniusEquiv (OCb l) l).surjective
  obtain ⟨c, hc⟩ := hsurj (a.shift 1)
  refine ⟨c, ?_⟩
  rw [hv, Function.iterate_one, ← hc, WittVector.verschiebung_frobenius, mul_comm]

theorem coeff_zero_l_mul {R : Type} [CommRing R] [CharP R l] (x : WittVector l R) :
    ((l : WittVector l R) * x).coeff 0 = 0 := by
  change WittVector.constantCoeff ((l : WittVector l R) * x) = 0
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem isUnit_inclW_per_and_saturated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → IsUnit (inclW l τ) ∧ (∀ g : GQ l, IsUnit (inclW l (Per.σA g τ))) ∧
      ∀ (k : ℕ) (a : Ainf l), ((l : ℕ) : WCb l) ^ k ∣ inclW l a → ((l : ℕ) : Ainf l) ^ k ∣ a := by
  intro l _ K bk τ hτ
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  have hε1 : ε ≠ 1 := by
    rintro rfl
    obtain ⟨-, hu⟩ := hε
    exact hu (by rw [map_one]; simp)
  have hc0 : τ.coeff 0 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x => WittVector.constantCoeff x) hφ
    change (WittVector.frobenius τ).coeff 0 = _ at h1
    rw [WittVector.coeff_frobenius_charP, h0, zero_pow (Fact.out : l.Prime).ne_zero, map_mul, map_sub, map_one] at h1
    change 0 = WittVector.constantCoeff (η : Ainf l) * ((WittVector.teichmuller l ε).coeff 0 - 1) at h1
    rw [WittVector.teichmuller_coeff_zero] at h1
    have hη : IsUnit (WittVector.constantCoeff (η : Ainf l)) := η.isUnit.map _
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact hη.ne_zero h
    · exact hε1 (sub_eq_zero.1 h)
  have hU : IsUnit (inclW l τ) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change algebraMap (OCb l) (Cb l) (τ.coeff 0) ≠ 0
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hc0
  refine ⟨hU, fun g => ?_, ?_⟩
  · rw [← galW_inclW]
    exact hU.map (galW l g)
  · intro k
    induction k with
    | zero => intro a _; simp
    | succ k ih =>
      intro a ⟨c, hc⟩
      have h0 : a.coeff 0 = 0 := by
        have h1 : (inclW l a).coeff 0 = 0 := by
          rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
        change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
        exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
      obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
      have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
        have h1 := congrArg (fun x : WCb l => x.coeff 1) h
        simp [WittVector.coeff_p] at h1
      have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
        refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
        rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
      exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrimeUniformizerClass
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem prime_mk_X_of_constantCoeff {W : Type} [CommRing W] [IsDomain W] {p : W} (hp : Prime p) (E : W⟦X⟧)
    (w : Wˣ) (hE : constantCoeff E = p * w) :
    Prime (Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧)) := by
  have key : ∀ f : W⟦X⟧, Ideal.Quotient.mk (Ideal.span {E}) (X : W⟦X⟧) ∣ Ideal.Quotient.mk (Ideal.span {E}) f ↔
      p ∣ constantCoeff f := by
    intro f
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      have h := congrArg constantCoeff hd
      simp only [map_sub, map_mul, constantCoeff_X, zero_mul, sub_zero, hE] at h
      exact ⟨w * constantCoeff d, by rw [h, mul_assoc]⟩
    · rintro ⟨c, hc⟩
      have h0 : constantCoeff (f - E * C (((w⁻¹ : Wˣ) : W) * c)) = 0 := by
        simp only [map_sub, map_mul, constantCoeff_C, hE, hc]
        rw [mul_assoc, ← mul_assoc (w : W), Units.mul_inv, one_mul, sub_self]
      obtain ⟨g, hg⟩ := X_dvd_iff.2 h0
      refine ⟨Ideal.Quotient.mk _ g, ?_⟩
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨C (((w⁻¹ : Wˣ) : W) * c), by rw [← hg]; ring⟩
  refine ⟨fun h => ?_, fun h => ?_, fun a b hab => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    have h1 := congrArg constantCoeff hc
    simp only [map_mul, constantCoeff_X, hE] at h1
    have h2 : constantCoeff c = 0 :=
      (mul_eq_zero.1 h1.symm).resolve_left (mul_ne_zero hp.ne_zero w.ne_zero)
    obtain ⟨g, rfl⟩ := X_dvd_iff.2 h2
    have h3 : (1 : W⟦X⟧) = E * g := by
      apply mul_left_cancel₀ (X_ne_zero (R := W))
      rw [mul_one]
      linear_combination hc
    have h4 := congrArg constantCoeff h3
    simp only [map_mul, map_one, hE] at h4
    exact hp.not_isUnit (isUnit_of_dvd_one ⟨w * constantCoeff g, by rw [h4, mul_assoc]⟩)
  · have h1 := (key 1).1 h.dvd
    rw [map_one] at h1
    exact hp.not_isUnit (isUnit_of_dvd_one h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, key, map_mul] at hab
    rw [key, key]
    exact hp.dvd_or_dvd hab

theorem BK.prime_unif (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) :
    Prime (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) ∧
      intToOC K (bk.str.symm (Ideal.Quotient.mk _ (X : bk.S))) = bk.flat.untilt := by
  constructor
  · obtain ⟨w, hw⟩ := bk.coeff_zero
    have : DecompositionMonoid (Wq l bk.a) := UniqueFactorizationMonoid.instDecompositionMonoid
    have hp : Prime (l : Wq l bk.a) := (WittVector.irreducible l).prime
    have hE : constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; exact Polynomial.constantCoeff_coe _
    exact (MulEquiv.prime_iff bk.str.symm).2 (prime_mk_X_of_constantCoeff hp bk.E w hE)
  · rw [← bk.θ_ev _ X (bk.str.apply_symm_apply _).symm, bk.ev_X]
    exact WittVector.fontaineTheta_teichmuller _

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envExt_sub_mem {S A C : Type} [CommRing S] [CommRing A] [CommRing C] (G G' : A →+* C) (s : S →+* A)
    (J : Ideal S) (x a : A) (hs : G.comp s = G'.comp s) (ha : G a = G' a) (hx : x - a ∈ J.map s) :
    G x - G' x ∈ J.map (G.comp s) := by
  have e : G x - G' x = G (x - a) - G' (x - a) := by rw [map_sub, map_sub, ha]; ring
  rw [e]
  refine Ideal.sub_mem _ ?_ ?_
  · rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem G hx
  · rw [hs, ← Ideal.map_map]; exact Ideal.mem_map_of_mem G' hx

theorem envExt_haus {C : Type} [CommRing C] (I : Ideal C) (h : IsHausdorff I C) (z : C) (hz : ∀ n : ℕ, z ∈ I ^ n) :
    z = 0 :=
  h.haus z fun n => by
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hz n


set_option maxHeartbeats 1600000 in
theorem envExt_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  intro l _ K bk B d p En C _ φ F F' hl hF hF' hb hX hd hH

  have hw : F En.w = F' En.w := by
    have h1 := congrArg F En.w_eq
    have h2 := congrArg F' En.w_eq
    rw [map_add (f := _), map_mul] at h1 h2
    have h3 : F (En.inl.f d) * F En.w = F (En.inl.f d) * F' En.w := by
      rw [hb d] at h1 ⊢
      rw [hb p] at h1
      rw [hX] at h1
      rw [h2] at h1
      linear_combination -h1
    exact (mul_cancel_left_mem_nonZeroDivisors hd).1 h3

  have hδ : ∀ a, F a = F' a → F (En.Q.D.δ a) = F' (En.Q.D.δ a) := by
    intro a ha
    have e1 := hF a
    have e2 := hF' a
    rw [En.Q.D.φ_eq, map_add (f := _), map_mul, map_pow, map_natCast] at e1 e2
    rw [← ha] at e2
    have : ((l : ℕ) : C) * (F (En.Q.D.δ a) - F' (En.Q.D.δ a)) = 0 := by
      linear_combination e1 - e2
    exact sub_eq_zero.1 (hl _ this)
  have hit : ∀ i : ℕ, F (En.Q.D.δ^[i] En.w) = F' (En.Q.D.δ^[i] En.w) := by
    intro i
    induction i with
    | zero => exact hw
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hδ _ ih
  have hbasis : ∀ α, F (En.tb.b α) = F' (En.tb.b α) := by
    intro α
    rw [En.tb_b, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [map_pow, map_pow, hit i]
  have hcomp : F.comp En.inl.f = F'.comp En.inl.f := RingHom.ext hb
  have key : ∀ x (n : ℕ), F x - F' x ∈ ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I) ^ n).map (F.comp En.inl.f) := by
    intro x n
    have hfin := En.tb.fin x n
    have happ := En.tb.approx x n hfin.toFinset (fun i hi => by
      by_contra h
      exact hi (hfin.mem_toFinset.2 h))
    have hsum : F (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) =
        F' (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hb, hbasis]
    exact envExt_sub_mem F F' En.inl.f _ _ _ hcomp hsum happ
  ext x
  exact sub_eq_zero.1 (envExt_haus _ hH _ fun n => by rw [← Ideal.map_pow]; exact key x n)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWitt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.PairW

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] {x : A}
    (h : ∀ n : ℕ, x ∈ J ^ n) : x = 0 :=
  IsHausdorff.haus' (I := J) x fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h n

theorem pow_sub_pow_mem_succ {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    {k : ℕ} (h : y - z ∈ J ^ (k + 1)) : y ^ p - z ^ p ∈ J ^ (k + 1 + 1) := by
  have h1 : y - z ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero k) h
  have hs : (∑ i ∈ Finset.range p, y ^ i * z ^ (p - 1 - i)) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hyz : Ideal.Quotient.mk J y = Ideal.Quotient.mk J z := Ideal.Quotient.eq.2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, hyz]
    rw [geom_sum₂_self, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
  have e := geom_sum₂_mul y z p
  rw [← e, mul_comm, pow_succ]
  exact Ideal.mul_mem_mul h hs

theorem pow_pow_sub_mem {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    (h : y - z ∈ J) (n : ℕ) : y ^ p ^ n - z ^ p ^ n ∈ J ^ (n + 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [pow_succ p n, pow_mul, pow_mul]; exact pow_sub_pow_mem_succ p hp ih

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) (hp : (p : A) ∈ J)
    {a : ℕ} (ha : 0 < a) {y z : A} (hy : y ^ p ^ a = y) (hz : z ^ p ^ a = z) (h : y - z ∈ J) : y = z := by
  have hy' : ∀ n, y ^ p ^ (a * n) = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]
  have hz' : ∀ n, z ^ p ^ (a * n) = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  have h2 := pow_pow_sub_mem p hp h (a * n)
  rw [hy', hz'] at h2
  exact Ideal.pow_le_pow_right (Nat.le_succ_of_le (Nat.le_mul_of_pos_left n ha)) h2

theorem padicInt_ringHom_eq {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) ∈ J) (φ ψ : ℤ_[p] →+* A) (u : ℤ_[p]) : φ u = ψ u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : u = ((u.appr n : ℕ) : ℤ_[p]) + v * (p : ℤ_[p]) ^ n := by linear_combination -hv
  have e : φ u - ψ u = (φ v - ψ v) * (p : A) ^ n := by
    rw [hu]; simp only [map_add (f := _), map_mul, map_pow, map_natCast]; ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp n)

end GlobalTheory.BSP.PairW

namespace GlobalTheory.BSP

open GlobalTheory.BSP.PairW

theorem hf_C_eq_of_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  intro l _ K bk B f g w
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hI : ∀ v : Wq l bk.a, BK.hf f (C v) - BK.hf g (C v) ∈ B.I := by
    intro v
    have hr : Ideal.Quotient.mk bk.prism.I (C v : bk.prism.A) =
        bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ (C v))) :=
      (bk.str.apply_symm_apply _).symm
    rw [← Ideal.Quotient.eq]
    exact (f.f_str _ _ hr).trans (g.f_str _ _ hr).symm
  have hT : ∀ x : Fq l bk.a, BK.hf f (C (WittVector.teichmuller l x)) = BK.hf g (C (WittVector.teichmuller l x)) := by
    intro x
    have ht : (WittVector.teichmuller l x) ^ l ^ bk.a = WittVector.teichmuller l x := by
      rw [← map_pow, Fq.pow_card]
    refine eq_of_pow_eq_self (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      ?_ ?_ (Ideal.mem_sup_right (hI _))
    · rw [← map_pow, ← map_pow, ht]
    · rw [← map_pow, ← map_pow, ht]
  have hZ : ∀ u : ℤ_[l], BK.hf f (C (algebraMap ℤ_[l] (Wq l bk.a) u)) = BK.hf g (C (algebraMap ℤ_[l] (Wq l bk.a) u)) :=
    fun u => padicInt_ringHom_eq (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ
      (((BK.hf f).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (((BK.hf g).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a))) u
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact hT y
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [Algebra.smul_def]; simp only [map_mul, hx, hZ]

end GlobalTheory.BSP
end
end

