module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLattice
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatOfTie

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfUnitFrobeniusEqMul
section
noncomputable section

open Polynomial

namespace GlobalTheory.Per.LangUnit

open GlobalTheory.Cyc.FontW

theorem onto_of_cpl' {l : ℕ} {M : Type} [AddCommGroup M] (hM : Cpl l M) (f : M →+ M)
    (h : ∀ y, ∃ x z, f x - y = l • z) : Function.Surjective f := by
  intro y
  have hstep : ∀ (r : ℕ) (x : M), f x - y ∈ Dv l r M →
      ∃ x', f x' - y ∈ Dv l (r + 1) M ∧ x' - x ∈ Dv l r M := by
    intro r x hx
    obtain ⟨u, hu⟩ := mem_Dv.1 hx
    obtain ⟨a, z, haz⟩ := h (-u)
    refine ⟨x + l ^ r • a, mem_Dv.2 ⟨z, ?_⟩, mem_Dv.2 ⟨a, by abel⟩⟩
    rw [pow_succ, mul_smul, ← haz, map_add (f := _), map_nsmul, add_sub_right_comm, ← hu, sub_neg_eq_add,
      smul_add, add_comm]
  choose nx hnx using hstep
  let g : (r : ℕ) → {x // f x - y ∈ Dv l r M} := fun r =>
    Nat.rec ⟨0, mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
      (fun r b => ⟨nx r b.1 b.2, (hnx r b.1 b.2).1⟩) r
  obtain ⟨L, hL⟩ := hM.2 (fun r => (g r).1) fun r => (hnx r (g r).1 (g r).2).2
  refine ⟨L, sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : f L - y = f (L - (g r).1) + (f (g r).1 - y) := by rw [map_sub]; abel
  rw [e]
  exact add_mem (Dv_map f (hL r)) (g r).2

variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [CommRing k] [CharP k p] [PerfectRing k p]

theorem eq_smul_of_coeff_zero {A : WittVector p k} (hA : A.coeff 0 = 0) : ∃ Z, A = p • Z := by
  have h0 : A ∈ Ideal.span {(p : WittVector p k)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]
    exact hA
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨u, by rw [← hu, nsmul_eq_mul, mul_comm]⟩

theorem coeff_zero_frob_sub (ω X : WittVector p k) :
    (WittVector.frobenius X - ω * X).coeff 0 = X.coeff 0 ^ p - ω.coeff 0 * X.coeff 0 := by
  simp only [← WittVector.constantCoeff_apply, map_sub, map_mul]
  rw [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]
  simp only [WittVector.constantCoeff_apply]

theorem lang_unit
    (hroot : ∀ f : k[X], f.Monic → 0 < f.natDegree → ∃ x, f.IsRoot x)
    (ω : WittVector p k) (hω : IsUnit ω) :
    ∃ η : WittVector p k, IsUnit η ∧ WittVector.frobenius η = ω * η := by
  have hp1 : 1 < p := hp.out.one_lt
  haveI : Nontrivial k := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  set ω₀ := ω.coeff 0 with hω₀
  have hu0 : IsUnit ω₀ := by
    rw [hω₀, ← WittVector.constantCoeff_apply]; exact hω.map _
  let f : WittVector p k →+ WittVector p k :=
    (WittVector.frobenius : WittVector p k →+* WittVector p k).toAddMonoidHom -
      AddMonoidHom.mulLeft ω
  have hf : ∀ X, f X = WittVector.frobenius X - ω * X := fun X => rfl

  have hmod : ∀ Y, ∃ X Z, f X - Y = p • Z := by
    intro Y
    obtain ⟨x, hx⟩ := hroot (X ^ p - (C ω₀ * X + C (Y.coeff 0)))
      (monic_X_pow_sub (by
        refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
        · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast hp1)
        · exact (degree_C_le).trans_lt (by exact_mod_cast (by omega : 0 < p))))
      (by
        have hlow : (C ω₀ * X + C (Y.coeff 0)).natDegree < p := by
          refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
          · exact ((natDegree_C_mul_le _ _).trans natDegree_X_le).trans_lt hp1
          · rw [natDegree_C]; omega
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]
        omega)
    refine ⟨WittVector.teichmuller p x, eq_smul_of_coeff_zero ?_⟩
    have hx' : x ^ p - (ω₀ * x + Y.coeff 0) = 0 := by simpa using hx
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hf, coeff_zero_frob_sub, WittVector.teichmuller_coeff_zero,
      ← hω₀]
    rw [← hx']; ring

  obtain ⟨t₀, ht₀⟩ := hroot (X ^ (p - 1) - C ω₀) (monic_X_pow_sub_C _ (by omega))
    (by rw [natDegree_X_pow_sub_C _]; omega)
  have ht₀' : t₀ ^ (p - 1) = ω₀ := by simpa [sub_eq_zero] using ht₀
  have hut : IsUnit t₀ := (isUnit_pow_iff (by omega : p - 1 ≠ 0)).1 (ht₀' ▸ hu0)
  have htp : t₀ ^ p = ω₀ * t₀ := by
    rw [← ht₀', ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
  set t := WittVector.teichmuller p t₀ with ht
  obtain ⟨Y, hY⟩ := eq_smul_of_coeff_zero (A := f t) (by
    rw [hf, coeff_zero_frob_sub, ht, WittVector.teichmuller_coeff_zero, ← hω₀, htp, sub_self])
  obtain ⟨Z, rfl⟩ := onto_of_cpl' (cpl_witt p k) f hmod Y
  refine ⟨t - p • Z, ?_, ?_⟩
  · have hj : -(p • Z) ∈ (⊥ : Ideal (WittVector p k)).jacobson :=
      IsAdicComplete.le_jacobson_bot (Ideal.span {(p : WittVector p k)})
        (neg_mem (Ideal.mem_span_singleton'.2 ⟨Z, by rw [nsmul_eq_mul, mul_comm]⟩))
    obtain ⟨u, hu⟩ : IsUnit t := hut.map (WittVector.teichmuller p)
    have h1 := Ideal.mem_jacobson_bot.1 hj (↑u⁻¹)
    have e : t - p • Z = (-(p • Z) * ↑u⁻¹ + 1) * u := by
      rw [add_mul, mul_assoc, Units.inv_mul, mul_one, one_mul, hu]; abel
    rw [e]
    exact h1.mul u.isUnit
  · rw [← sub_eq_zero, ← hf, map_sub, map_nsmul, hY, sub_self]

end GlobalTheory.Per.LangUnit

namespace GlobalTheory.Per

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc


set_option synthInstance.maxHeartbeats 400000 in
theorem OCb_exists_root (l : ℕ) [Fact l.Prime] (f : (OCb l)[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) : ∃ x, f.IsRoot x := by
  haveI : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  haveI : ValuationRing (OCb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2
  haveI : IsIntegrallyClosed (OCb l) :=
    (ValuationRing.integers (OCb l) (Cb l)).isIntegrallyClosed
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (f.map (algebraMap (OCb l) (Cb l))) (by
    rw [degree_map_eq_of_injective (IsFractionRing.injective (OCb l) (Cb l)),
      degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hd.ne')
  have hint : IsIntegral (OCb l) z := ⟨f, hf, by rwa [IsRoot, eval_map_algebraMap] at hz⟩
  obtain ⟨x, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨x, IsFractionRing.injective (OCb l) (Cb l) ?_⟩
  rw [IsRoot, eval_map_algebraMap, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at hz
  rw [hz, map_zero]

theorem frobenius_eq_mul_solvable :
    ∀ (l : ℕ) [Fact l.Prime] (ω : (Ainf l)ˣ), ∃ η : (Ainf l)ˣ, WittVector.frobenius (η : Ainf l) = ω * η := by
  intro l _ ω
  obtain ⟨η, ⟨u, rfl⟩, h⟩ := GlobalTheory.Per.LangUnit.lang_unit (p := l) (k := OCb l)
    (OCb_exists_root l) (ω : Ainf l) ω.isUnit
  exact ⟨u, h⟩

end GlobalTheory.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ), 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  first | exact @GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | exact GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul | (intros; apply GlobalTheory.ExpImage.exists_cycVal_eq_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller]
  congr 2
  exact (frobeniusEquiv (OCb l) l).apply_symm_apply AI.ε

theorem act_μ {K : FinExt l} {h : GQ l} (hh : h ∈ Hinf K) : AI.actW h AI.μ = AI.μ := by
  have h1 : P.χQ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
  have h2 := GlobalTheory.T.cyclotomic_action_on_root_tower l P AI h 1 (by rw [h1]; simp) 0
  have h3 : AI.actT h AI.ε = AI.ε := by simpa [LocAinf.εroot] using h2
  rw [LocAinf.μ, map_sub, map_one, LocAinf.actW, WittVector.map_teichmuller]
  congr 2

theorem step_dR (T : LocTied l P AI) {g : GQ l} {U : ℤ_[l]} {k : ℕ} {β r : Ainf l} {u : P.R.BdR}
    (hu : io AI AI.π₁ * u = 1) (h : Step AI g U AI.π₁ k β r) :
    qB P (U : ℚ_[l]) * P.actQdR g (io AI β * u ^ k) - io AI β * u ^ k = io AI r * u ^ k := by
  have e := congrArg (io AI) h
  simp only [map_sub, map_mul, map_pow, io_act, io_zl AI T] at e
  have h1 : io AI AI.π₁ ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  have h2 : P.actQdR g (io AI AI.π₁) ^ k * P.actQdR g u ^ k = 1 := by
    rw [← mul_pow, ← map_mul, hu, map_one, one_pow]
  rw [map_mul, map_pow]
  linear_combination (u ^ k * P.actQdR g u ^ k) * e
    - (qB P (U : ℚ_[l]) * P.actQdR g (io AI β) * P.actQdR g u ^ k) * h1
    + (io AI β * u ^ k + io AI r * u ^ k) * h2

theorem limit (T : LocTied l P AI) {M : ℕ} (hM : 1 ≤ M) (g : GQ l) (U : ℤ_[l]) (b v : P.R.BdR)
    (S E : ℕ → P.R.BdR)
    (hb : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - S R ∈ Lat AI M n)
    (hE : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, E R ∈ Lat AI M n)
    (hS : ∀ R, ∃ z : ℤ_[l], v + (qB P (U : ℚ_[l]) * P.actQdR g (S R) - S R) = qB P (z : ℚ_[l]) - E R) :
    NearZ P M (v + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l P AI T M hM _ fun n => ?_
  obtain ⟨R₀, h₀⟩ := hb n
  obtain ⟨R₁, h₁⟩ := hE n
  obtain ⟨z, hz⟩ := hS (max R₀ R₁)
  have a := h₀ _ (le_max_left R₀ R₁)
  have a' := h₁ _ (le_max_right R₀ R₁)
  refine ⟨z, ?_⟩
  have := add_mem (sub_mem a (qB_mul_mem_Lat AI T U (act_mem_Lat AI g a))) a'
  convert this using 1
  rw [map_sub]
  linear_combination -hz

theorem telescope (g : GQ l) (U : ℤ_[l]) (s : ℕ) (B H : ℕ → P.R.BdR)
    (h : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (B k) - B k =
      H k - (l : P.R.BdR) ^ s * H (k + 1) + qB P (z : ℚ_[l])) (R : ℕ) :
    ∃ z : ℤ_[l], -H 0 + (qB P (U : ℚ_[l]) *
        P.actQdR g (∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) -
        ∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) =
      qB P (z : ℚ_[l]) - (l : P.R.BdR) ^ (s * R) * H R := by
  induction R with
  | zero => exact ⟨0, by simp⟩
  | succ R ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := h R
    refine ⟨z + (l : ℤ_[l]) ^ (s * R) * w, ?_⟩
    rw [Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      map_add, map_mul, map_pow, map_natCast, mul_add s R 1, pow_add, mul_one]
    linear_combination hz + (l : P.R.BdR) ^ (s * R) * hw

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (g : GQ l) (U : ℤ_[l]) (M : ℕ), 1 ≤ M → ∀ y : Ainf l, Solv AI K s g U (y - WittVector.frobenius y) → ∃ b ∈ FilB P 0, (∀ h ∈ Hinf K, NearZ P M (P.actQdR h b - b)) ∧ NearZ P M (io AI y + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  intro l _ P AI T K s hs g U M hM y ⟨p, q, hq0, hp, hstep⟩
  have asw := (GlobalTheory.ArtinSchreierWitt.main l).2.2
  choose β hβ using fun k : ℕ => asw (AI.ξ ^ (k + 1)) (p k)
  have hη' : ∀ k : ℕ, ∃ η : Ainf l, WittVector.frobenius η - AI.ξ ^ k * η = q k ∧ (k = 0 → η = -y) := by
    intro k
    rcases k with _ | k
    · exact ⟨-y, by rw [hq0, map_neg]; ring, fun _ => rfl⟩
    · obtain ⟨η, h⟩ := asw (AI.ξ ^ (k + 1)) (q (k + 1))
      exact ⟨η, h, fun h => absurd h (Nat.succ_ne_zero k)⟩
  choose η hη hη0 using hη'
  obtain ⟨u, hu0, hu⟩ := _root_.GlobalTheory.ExpImage.exists_inv_io_pi l P AI T
  have small := GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice l P AI s hs u hu0 hu M
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_series_limit_Lat_alt l P AI M
    (fun k => (l : P.R.BdR) ^ (s * k) * (io AI (β k) * u ^ (k + 1)))
    (fun k => by
      have h1 : (l : P.R.BdR) ^ (s * k) * io AI (β k) ∈ FilB P 0 := by
        simpa using io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * β k)
      have h2 : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu0 (k + 1)
      rw [← mul_assoc]
      exact FilB_zero_mul h1 h2)
    (fun n => by
      obtain ⟨k₀, h⟩ := small n
      exact ⟨k₀, fun k hk => by rw [← mul_assoc]; exact h k hk _⟩)
  have h1 : ∀ k, io AI AI.π₁ ^ k * u ^ k = 1 := fun k => by rw [← mul_pow, hu, one_pow]
  refine ⟨b, hb0, fun h hh => ?_, ?_⟩
  · have key : ∀ k, ∃ z : ℤ_[l], qB P ((1 : ℤ_[l]) : ℚ_[l]) * P.actQdR h (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = (0 : P.R.BdR) - (l : P.R.BdR) ^ s * 0 + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.ExpStep.main l P AI h 1 (k + 1) (β k) 0 (by
        rw [hβ]
        unfold Step
        rw [hp k h hh, act_μ AI hh]
        simp [mul_comm])
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz, zero_add, map_mul, map_pow, io_zl AI T, mul_assoc, h1]
      ring
    have := limit AI T hM h 1 b 0 _ (fun _ => 0) hb (fun n => ⟨0, fun _ _ => zero_mem _⟩)
      (fun R => by
        simpa using telescope h 1 s (fun k => io AI (β k) * u ^ (k + 1)) (fun _ => 0) key R)
    simpa using this
  · have key : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = io AI (η k) * u ^ k -
          (l : P.R.BdR) ^ s * (io AI (η (k + 1)) * u ^ (k + 1)) + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.ExpStep.main l P AI g U (k + 1) (β k)
        (AI.π₁ * η k - ((l : ℕ) : Ainf l) ^ s * η (k + 1)) (by
        rw [hβ]
        convert hstep k using 1
        rw [← hη k, ← hη (k + 1), map_sub, map_mul, map_mul, map_pow, map_natCast, frob_π₁, AI.μ_eq]
        ring)
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz]
      simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, io_zl AI T]
      linear_combination (io AI (η k) * u ^ k) * hu + qB P (z : ℚ_[l]) * h1 (k + 1)
    refine limit AI T hM g U b _ _ (fun R => (l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) hb
      (fun n => ?_) (fun R => ?_)
    · obtain ⟨k₀, h⟩ := small n
      refine ⟨k₀, fun R hR => ?_⟩
      convert h R hR (η R * AI.π₁) using 1
      rw [map_mul]
      linear_combination (-(l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) * hu
    · have := telescope g U s (fun k => io AI (β k) * u ^ (k + 1)) (fun k => io AI (η k) * u ^ k) key R
      simpa only [hη0 0 rfl, map_neg, pow_zero, mul_one, neg_neg] using this

end GlobalTheory.ExpImage.Sum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompletion_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec (D.locA l).actC (D.loc l).χQ K (mN l s (M0 + h0)) M Dm U g ∧ ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K (mN l s (M0 + h0))) := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_decompletion | exact GlobalTheory.Cyc.Decomp.exists_decompletion | (intros; apply GlobalTheory.Cyc.Decomp.exists_decompletion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysWD

theorem exists_descent {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l))
    (hr : Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l))))
    (L : FinExt l)
    (hL : ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin a) ↥L.1,
      Continuous (fun g => ((ρ g : Matrix.GeneralLinearGroup (Fin a) ↥L.1) :
        Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let M : G →* Matrix (Fin a) (Fin a) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hL g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Continuous.subtype_mk ((continuous_apply j).comp ((continuous_apply i).comp hr)) _
  · ext g i j
    rfl

theorem crysIffWD (D : D7) : CrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_unrL i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_unrL i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := _root_.GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := exists_descent r hr L hL
  obtain ⟨h1, h2, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ (h1.1 hc)).1
  refine h2.2 ?_
  unfold IsDR at h3
  unfold LocBridge.IsdRE
  simpa using h3

end GlobalTheory.CrysWD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeOfPowMem
section
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.EtaleExact TensorProduct

namespace GlobalTheory.EtaleSub

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)


include E in
theorem surjective_of_tie (hfl : Module.Flat O RW) {T' T : LocLat G Qp LL O}
    (hfix : ∀ b, TWmap φR T' b = b → ∃ t : ↥T'.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (hone : Function.Injective fun t : ↥T.L.T => (1 : RW) ⊗ₜ[O] t)
    (ι : LatHom T'.L T.L) (hι : Function.Injective ι.f) (m : ℕ) (hm : (m : LL) ≠ 0)
    (hall : ∀ x : W.DD T, ((m : ℕ) : W.EE) • x ∈ LinearMap.range (W.map ι)) :
    Function.Surjective ι.f := by
  have hU := span_range_map E ι
  have hkill : ∀ y : TW RW T, m • y ∈ LinearMap.range ((latMap ι).baseChange RW) := by
    intro y
    have hy : y ∈ Submodule.span RW (Set.range (E.jD T)) := by
      rw [E.jD_span T]; exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← hU]
      refine Submodule.subset_span ⟨_, hall x, ?_⟩
      rw [E.jD_smul, map_natCast, Nat.cast_smul_eq_nsmul]
    | zero => simp
    | add z w _ _ hz hw => rw [smul_add]; exact Submodule.add_mem _ hz hw
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  have hinj : Function.Injective ((latMap ι).baseChange RW) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := RW) (latMap ι)
      (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
  have hcomm : ∀ c : TW RW T', (latMap ι).baseChange RW (TWmap φR T' c) =
      TWmap φR T ((latMap ι).baseChange RW c) := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul r t => simp [TWmap]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ t : ↥T.L.T, ∃ t' : ↥T'.L.T, latMap ι t' = m • t := by
    intro t
    obtain ⟨c, hc⟩ := hkill ((1 : RW) ⊗ₜ[O] t)
    rw [← TensorProduct.tmul_smul] at hc
    have hf : TWmap φR T' c = c := by
      apply hinj
      rw [hcomm, hc]
      simp [TWmap]
    obtain ⟨t', rfl⟩ := hfix c hf
    refine ⟨t', hone ?_⟩
    simpa using hc
  have hle : (T.L.T : Set T.V) ⊆ (LinearMap.range ι.f : Submodule LL T.V) := by
    intro t ht
    obtain ⟨t', h'⟩ := h2 ⟨t, ht⟩
    refine ⟨(m : LL)⁻¹ • (t' : T'.V), ?_⟩
    have h3 : ι.f (t' : T'.V) = m • t := congrArg Subtype.val h'
    rw [map_smul, h3, ← Nat.cast_smul_eq_nsmul LL, smul_smul, inv_mul_cancel₀ hm, one_smul]
  have htop : LinearMap.range ι.f = ⊤ :=
    top_le_iff.1 (T.L.span ▸ Submodule.span_le.2 hle)
  exact LinearMap.range_eq_top.1 htop

end Generic

theorem exists_lattice_of_pow_mem : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitSub D HW F := by
  intro D HW F l _ K LL hA T D' hpow hφ hγ
  obtain ⟨T', ι, hι, hr⟩ := exists_sublattice (D.locA l) (HW l) (F l) K 1 LL hA.2.2 T D' hφ hγ
  obtain ⟨a, ha⟩ := hpow
  refine ⟨T', ι, ⟨hι, ?_⟩, hr⟩
  haveI := flat_RW LL
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hp : (((D.loc l).PD K).p : ℕ) = l := (D.loc l).PD_p K
  refine surjective_of_tie ((F l).E K 1 LL hA.2.2).tie (flat_RW LL)
    (fun b hb => ((GlobalTheory.WittTensorFixed.main l K LL T').2.1 b).1 hb)
    (GlobalTheory.WittTensorFixed.main l K LL T).2.2 ι hι (l ^ a) ?_ ?_
  · exact_mod_cast pow_ne_zero a (Fact.out : l.Prime).ne_zero
  · intro x
    rw [hr]
    have := ha x
    rw [hp] at this
    simpa using this

end GlobalTheory.EtaleSub
end
end

