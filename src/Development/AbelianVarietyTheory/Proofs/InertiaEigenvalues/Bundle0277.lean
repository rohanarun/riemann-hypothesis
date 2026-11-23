module

public import Mathlib
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTilt
section
namespace GlobalTheory.ArtinSchreierTilt

open Formalism.BasicNotions.Loc

namespace Div

open scoped NNReal
open _root_.Ideal

section General

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))] [IsAdicComplete (span {(p : O)}) O]

noncomputable def lift (u : PreTilt O p) (m : ℕ) : O :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[m]) u)

theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

theorem dvd_of_val_le (x y : PreTilt O p)
    (h : PreTilt.val K v O hv p x ≤ PreTilt.val K v O hv p y) : y ∣ x := by
  by_cases hx : x = 0
  · exact hx ▸ dvd_zero y
  by_cases hy : y = 0
  · exfalso
    apply hx
    rw [← PreTilt.map_eq_zero hv]
    rw [hy, map_zero] at h
    exact le_antisymm h zero_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (algebraMap O K) := hv.hom_inj
  rw [val_eq_untilt hv x hx, val_eq_untilt hv y hy] at h
  have hY : ∀ m, lift y m ≠ 0 := by
    intro m h0
    apply hy
    rw [← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0,
      zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]
  have hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m)) := by
    intro m
    have h' := h
    rw [← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow] at h'
    exact (pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'
  choose q hq using fun m => hv.dvd_of_le (hle m)
  have hqs : ∀ m, q (m + 1) ^ p = q m := by
    intro m
    have h1 : lift y m * q (m + 1) ^ p = lift y m * q m := by
      rw [← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]
    have hK : algebraMap O K (lift y m) ≠ 0 := fun h0 => hY m (hinj (h0.trans (map_zero _).symm))
    apply hinj
    have h2 := congrArg (algebraMap O K) h1
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel₀ hK h2
  let e : PreTilt O p :=
    (⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by
      simp only
      rw [← map_pow, hqs]⟩ : Perfection (ModP O p) p)
  refine ⟨e, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n x = PreTilt.coeff n (y * e)
  rw [map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]
  rfl

end General

end Div

section Complete

open scoped NNReal
open _root_.Ideal

variable {p : ℕ} [Fact p.Prime]

theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.FixL

theorem fix_of_mul {R : Type} [CommRing R] (p : ℕ) (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    (f : R →+* R) (x : R) (hx : f ((p : R) * x) = (p : R) * x) : f x = x := by
  have hf : f (p : R) = (p : R) := map_natCast f p
  have h2 : (p : R) * (f x - x) = 0 := by
    rw [mul_sub, ← hf, ← map_mul, hx, hf, sub_self]
  exact sub_eq_zero.mp (h _ h2)

theorem fix_of_sum {R : Type} [CommRing R] (p : ℕ)
    (h : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (f : R →+* R) (x : ℕ → R) (hx : ∀ i, f (x i) = x i) (y : R)
    (hy : ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) :
    f y = y := by
  apply sub_eq_zero.mp
  apply h
  intro k
  obtain ⟨r, hr⟩ := hy k
  have hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_pow, map_natCast, hx]
  have hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r := by
    rw [← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]
  refine ⟨f r - r, ?_⟩
  rw [mul_sub, ← hfy, ← hr]
  ring

theorem frob_comm {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l)
    (g : GQ l) (x : RW LL) : AI.gRW LL g (φRW LL x) = φRW LL (AI.gRW LL g x) := by
  have key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w) := by
    intro w
    unfold LocAinf.actWCbHom frobW
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold mapAlgEquivW
    ext n
    dsimp only [AlgEquiv.ofRingEquiv]
    simp [mapEquivW, WittVector.map_coeff, frobenius_def]
  have hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) =
      (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l) := AlgHom.ext key
  unfold LocAinf.gRW φRW
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, hc]

private theorem mem_fixSub_lemma {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (LL : FinExt l) (H : Set (GQ l)) (x : RW LL) :
    x ∈ fixSub AI LL H ↔ ∀ g ∈ H, AI.gRW LL g x = x := by
  unfold fixSub
  simp [Subring.mem_iInf, RingHom.mem_eqLocus]

theorem fixSub_ladic (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l)
    (H : Set (GQ l)) :
    (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧
    (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧
    ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.Decompl.LAdic.ladic_RW l LL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    exact fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)
  · intro x hx
    rw [mem_fixSub_lemma] at hx ⊢
    intro g hg
    rw [frob_comm, hx g hg]
  · intro x hx
    obtain ⟨s, hs⟩ := h2 x
    refine ⟨s, ?_, hs⟩
    rw [mem_fixSub_lemma]
    intro g hg
    exact fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x
      (fun i => (mem_fixSub_lemma AI LL H (x i)).1 (hx i) g hg) s hs

end GlobalTheory.Decompl.FixL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomial
section
noncomputable section

open Filter Topology
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.GaussMono

theorem eventually_iSup_eq_monomial_left (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≤] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push_neg at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  have hσ0 : 0 < ρ / 2 := by positivity
  have hσρ : ρ / 2 < ρ := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hσ0 j)) hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, OrderDual.toDual n)) ⟨j, Finset.mem_insert_self _ _⟩
  have hpos : ∀ᶠ r in 𝓝[≤] ρ, ρ / 2 < r := (eventually_gt_nhds hσρ).filter_mono nhdsWithin_le_nhds
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≤] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
      have hr : r ≤ ρ := hr
      have hr0 : 0 ≤ r := hσ0.le.trans hr0.le
      simp only at h h'
      have hin : i ≤ n := OrderDual.toDual_le_toDual.1 h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (div_nonneg hr0 hρ.le) ((div_le_one hρ).2 hr) hin)
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  filter_upwards [(eventually_all_finset _).2 key, hpos, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : r ≤ ρ := hr
  have hr0 : 0 ≤ r := hσ0.le.trans hrσ.le
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
        _ ≤ ρ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hρ.le hρ1.le (not_lt.1 hn)
        _ ≤ c j * (ρ / 2) ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem eventually_monomial {R : Type} [CommRing R] (p : R) {L ρ : ℝ} (hL : 0 < L) (hLρ : L ≤ ρ) (hρ1 : ρ < 1)
    (N : ℝ → R → ℝ)
    (hN : ∀ r, L ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, L ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n)
    (f : Filter ℝ) (hf : f ≤ 𝓝 ρ) (hf0 : pure ρ ≤ f) (hfL : ∀ᶠ r in f, L ≤ r ∧ r < 1)
    (hmono : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → (∀ n, c n ≤ 1) → (⨆ n, c n * ρ ^ n) ≠ 0 →
      ∃ i, ∀ᶠ r in f, (⨆ n, c n * r ^ n) = c i * r ^ i) :
    ∃ (c : ℝ) (k : ℤ), 0 < c ∧ ∀ᶠ r in f, N r b = c * r ^ k := by
  have hρ : 0 < ρ := hL.trans_le hLρ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, L ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hL.le.trans hr) _) (e1 z)
  have hbb : ∀ r, L ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨-, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨-, e2, e3, -, -⟩ := hN ρ hLρ hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ hLρ hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ hLρ hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ hLρ hρ1] at ha
  obtain ⟨i, hi⟩ := hmono c h0 h1 ((pow_pos hρ _).trans ha).ne'
  have hiρ : (⨆ n, c n * ρ ^ n) = c i * ρ ^ i := Filter.mem_pure.1 (hf0 hi)
  rw [hiρ] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  refine ⟨c i, (i : ℤ) - k, hci, ?_⟩
  filter_upwards [hi, hf h4, hfL] with r hr1 hr2 hr
  obtain ⟨hr, hr3⟩ := hr
  have hr0 : 0 < r := hL.trans_le hr
  obtain ⟨-, e2, e3, -, -⟩ := hN r hr hr3
  have h6 := hbb r hr hr3
  have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
  rw [hab, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
  rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
  field_simp

end GlobalTheory.GaussMono

namespace GlobalTheory.PMon.Gauss

theorem gC_monomial_near : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ →
    ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧
    ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧
      ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  intro l _ x hx ρ₀ hρl hρ1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ0 : 0 < ρ₀ := hL.trans_le hρl
  have hN : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ y, gC l r y ≤ 1) ∧
      (∀ y z, gC l r (y + z) ≤ max (gC l r y) (gC l r z)) ∧ (∀ y, gC l r (-y) = gC l r y) ∧
      (∀ y z, gC l r (y * z) = gC l r y * gC l r z) ∧ gC l r (l : Formalism.Per.Acris l) = r := by
    intro r hr hr1
    obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_target l r hr hr1
    refine ⟨fun y => (e1 y).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, e5]
    exact GlobalTheory.GaussSlope.gauss_l l (hL.le.trans hr)
  have hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : Formalism.Per.Acris l) (c : ℕ → ℝ),
      (l : Formalism.Per.Acris l) ^ k * x = a + (l : Formalism.Per.Acris l) ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → gC l r a = ⨆ n, c n * r ^ n := by
    intro n
    obtain ⟨s, z, h⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    refine ⟨k, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, z,
      fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (isGauss_gC_target l r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  have hb : 0 < gC l ρ₀ x := _root_.GlobalTheory.PMon.Gauss.gC_pos_target l x hx ρ₀ hρl hρ1
  constructor
  · have hfL : ∀ᶠ r in 𝓝[≥] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hρ1).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hρl.trans hr, hr1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≥] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Ici.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussSlope.eventually_iSup_eq_monomial c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu : ρ₀ < u := hu
    obtain ⟨ρ₂, h2a, h2b⟩ := exists_between (lt_min hu hρ1)
    exact ⟨c, k, ρ₂, hc, h2a, h2b.trans_le (min_le_right _ _),
      fun r hr => hsub ⟨hr.1, hr.2.trans_lt (h2b.trans_le (min_le_left _ _))⟩⟩
  · intro hlt
    have hfL : ∀ᶠ r in 𝓝[≤] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨(hr1 : (l : ℝ)⁻¹ < r).le, (hr : r ≤ ρ₀).trans_lt hρ1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≤] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Iic.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussMono.eventually_iSup_eq_monomial_left c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hev
    have hu : u < ρ₀ := hu
    obtain ⟨ρ₁, h1a, h1b⟩ := exists_between (max_lt hu hlt)
    exact ⟨c, k, ρ₁, hc, (le_max_right _ _).trans h1a.le, h1b,
      fun r hr => hsub ⟨(le_max_left _ _).trans_lt (h1a.trans_le hr.1), hr.2⟩⟩

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionRestrictionIsClassFunction
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

namespace GlobalTheory.GLq.HcClass

variable {g : ℕ} [Fact g.Prime]

theorem hcT_isClass (a b n : ℕ) (Φ : Gn g a → Gn g b → ℂ) : IsClass (hcT a b Φ n) := by
  intro x w
  unfold hcT
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft w⁻¹) _ _ fun y => ?_
  rw [Equiv.coe_mulLeft, show (w⁻¹ * y)⁻¹ * x * (w⁻¹ * y) = y⁻¹ * (w * x * w⁻¹) * y by group]

variable {a b : ℕ}

theorem conj_blk (P P' : Mt g a) (Q Q' : Mt g b) (M : Mt g (a + b)) (hM : InPar a M) :
    InPar a (blkM P 0 Q * M * blkM P' 0 Q') ∧ tl a (blkM P 0 Q * M * blkM P' 0 Q') = P * tl a M * P' ∧
      br a b (blkM P 0 Q * M * blkM P' 0 Q') = Q * br a b M * Q' := by
  rw [← blkM_eq hM, blkM_mul, blkM_mul, tl_blkM, br_blkM, tl_blkM, br_blkM]
  exact ⟨inPar_blkM _ _ _, rfl, rfl⟩

theorem blkM_one : blkM (1 : Mt g a) 0 (1 : Mt g b) = 1 := by
  rw [blkM, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def dg (u : Gn g a) (v : Gn g b) : Gn g (a + b) :=
  ⟨blkM u.val 0 v.val, blkM (u⁻¹).val 0 (v⁻¹).val, by simp [blkM_mul, blkM_one], by simp [blkM_mul, blkM_one]⟩

theorem dg_mul (u u' : Gn g a) (v v' : Gn g b) : dg u v * dg u' v' = dg (u * u') (v * v') := by
  ext : 1
  simp [dg, blkM_mul]

theorem dg_one : dg (1 : Gn g a) (1 : Gn g b) = 1 := by
  ext : 1
  simp [dg, blkM_one]

theorem dg_inv (u : Gn g a) (v : Gn g b) : (dg u v)⁻¹ = dg u⁻¹ v⁻¹ := by
  symm
  rw [eq_inv_iff_mul_eq_one, dg_mul, inv_mul_cancel, inv_mul_cancel, dg_one]

def Cnd (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) : Prop :=
  InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)

theorem cnd_conj (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) (hx : Cnd h₁ h₂ x) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) := by
  obtain ⟨hp, ht, hb⟩ := hx
  rw [dg_inv]
  have e : ((dg u v * x * dg u⁻¹ v⁻¹ : Gn g (a + b)) : Mt g (a + b)) =
      blkM u.val 0 v.val * x.val * blkM (u⁻¹).val 0 (v⁻¹).val := rfl
  have := conj_blk u.val (u⁻¹).val v.val (v⁻¹).val x.val hp
  refine ⟨e ▸ this.1, ?_, ?_⟩
  · rw [e, this.2.1, ht]; simp
  · rw [e, this.2.2, hb]; simp

theorem cnd_iff (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) ↔ Cnd h₁ h₂ x := by
  refine ⟨fun h => ?_, cnd_conj u v h₁ h₂ x⟩
  have := cnd_conj u⁻¹ v⁻¹ _ _ _ h
  simp only [dg_inv] at this
  have key : dg u⁻¹ v⁻¹ * (dg u v * x * dg u⁻¹ v⁻¹) * dg u⁻¹⁻¹ v⁻¹⁻¹ = x := by
    rw [inv_inv, inv_inv, ← dg_inv]; group
  rwa [key, show u⁻¹ * (u * h₁ * u⁻¹) * u⁻¹⁻¹ = h₁ by group,
    show v⁻¹ * (v * h₂ * v⁻¹) * v⁻¹⁻¹ = h₂ by group] at this

theorem res_conj (χ : Gn g (a + b) → ℂ) (hχ : IsClass χ) (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b χ (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) = res a b χ h₁ h₂ := by
  unfold res
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj (dg u v)).toEquiv _ _ fun x => ?_).symm
  have hc := cnd_iff u v h₁ h₂ x
  unfold Cnd at hc
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc, hχ x (dg u v)]

theorem hc_class : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ Φ : Gn g a → Gn g b → ℂ, IsClass (hcT a b Φ n)) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → (∀ h, IsClass (res a b χ h)) ∧ ∀ h, IsClass (fun x => res a b χ x h) := by
  intro g _ a b n hn
  subst hn
  refine ⟨fun Φ => hcT_isClass _ _ _ Φ, fun χ hχ => ⟨fun h x y => ?_, fun h x y => ?_⟩⟩
  · simpa using res_conj χ hχ 1 y h x
  · simpa using res_conj χ hχ y 1 x h

end GlobalTheory.GLq.HcClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariantsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  first | exact @GlobalTheory.Cyc.isCrys_Ks_of_finrank | exact GlobalTheory.Cyc.isCrys_Ks_of_finrank | (intros; apply GlobalTheory.Cyc.isCrys_Ks_of_finrank <;> assumption)
end

