module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProof
section
noncomputable section

namespace GlobalTheory.Pass.JumpDualStep

open _root_.Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem jumpDual_main : StepJumpDual := by
  intro D hD hP i r hr eta s S sg U hs hJ Xs w hw n hsg hF
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 ((U w).image fun b => -b - 1), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨h, -, -⟩ := hU b hb
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : (b : ℚ) ≤ (eta : ℚ) + D.R.t ∧ -((s : ℚ) + S) - 1 ≤ b := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ b := by exact_mod_cast h1
          have h2' : (b : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h
          simp only [Bool.false_eq_true, if_false] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : b ≤ (eta : ℤ) + D.R.t := by exact_mod_cast key.1
      have k2 : -((s : ℤ) + S) - 1 ≤ b := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := U w) (f := fun b : ℤ => -b - 1); omega)
  · intro x τ a ha
    have h1 := (GlobalTheory.JumpDual.jump_dual D hD hP i r hr Xs w hw n hF x τ a).1 ha
    refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-a - 1, hj x τ _ h1, by ring⟩))

end GlobalTheory.Pass.JumpDualStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CrysEval

theorem coeff_natCast_mul_ps {R : Type} [CommRing R] (n i : ℕ) (f : R⟦X⟧) :
    coeff i ((n : R⟦X⟧) * f) = n * coeff i f := by
  rw [← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]

theorem dvd_fP_of_mem_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF
  obtain ⟨w, -, hw⟩ := hF
  have := charZero_K (l := l) (K := K)
  have key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k) := by
    intro i k
    apply embK_injective (K := K) t 0
    have h1 := congrArg (fun G => coeff k (coeff i (G 0))) hnF
    simp only [Pi.mul_apply, Pi.natCast_apply] at h1
    rw [coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP] at h1
    have h2 := hw 0 i k
    change _ = embK K t 0 (w (i, k)) at h2
    rw [map_mul, map_mul, map_natCast, map_natCast]
    push_cast at h2 ⊢
    linear_combination (-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2
  have hμ := ϖ.theta_mu (ϖ.gal_pi a g)
  set T := ainfToAcris l ϖ.teich with hTdef
  have term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k *
      ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)} := by
    intro i k
    obtain ⟨D, hD⟩ := ϖ.exists_dpow_teich (k / e)
    have hm := factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i
    have hk := congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)
    simp only [map_mul, map_natCast] at hk
    push_cast at hk
    rw [Ideal.mem_span_singleton']
    refine ⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩
    have hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hT, ← hD, map_mul, mul_pow, ← hm]
    linear_combination (-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk
  have hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)} := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k := by
      rw [evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
      change ainfToAcris l _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow]
      rfl
    rw [hev, Polynomial.sum_def, Finset.sum_mul]
    exact Ideal.sum_mem _ fun k _ => term i k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [mul_comm]; exact hy⟩

end GlobalTheory.CrysEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RootGal

theorem sub_mem_of_eval_mem {R : Type*} [CommRing R] (J : Ideal R) (P : Polynomial R) (x y : R)
    (hx : P.eval x ∈ J) (hy : P.eval y ∈ J)
    (hu : ∀ k : R, IsUnit ((Polynomial.derivative P).eval x + k * (y - x))) : y - x ∈ J := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion P x (y - x)
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hk
  have hmem : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) ∈ J := by
    have e : (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) = P.eval y - P.eval x := by
      rw [hk]; ring
    rw [e]; exact J.sub_mem hy hx
  obtain ⟨v, hv⟩ := (hu k).exists_right_inv
  have e : y - x = (y - x) * ((Polynomial.derivative P).eval x + k * (y - x)) * v := by
    rw [mul_assoc, hv, mul_one]
  rw [e]; exact J.mul_mem_right _ hmem

variable {l : ℕ} [Fact l.Prime]

theorem ev_algebraMap (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_of_dvd (n : ℕ) (a : Per.Ainf l) (ha : Per.θ l a = 0) (z : Per.BdRp l)
    (hz : aDp l a ^ n ∣ z) : z ∈ Per.FilP l n := by
  obtain ⟨w, rfl⟩ := hz
  have h2 : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := GlobalTheory.RingIface.alg_mem_kerP l ha
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_mul, map_pow, aDp, RingHom.comp_apply, ev_algebraMap, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow h2 n), zero_mul]

end GlobalTheory.BSP.RootGal


open GlobalTheory.BSP.RootGal in
theorem GlobalTheory.BSP.approxRoot_gal_sub_mem_fil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  intro l _ K bk n M q hq hroot g
  have hP := GlobalTheory.MemLoc.thetaD_props l
  set h : bk.S →+* Per.BdRp l := (aDp l).comp bk.ev with hh
  set h' : bk.S →+* Per.BdRp l := (aDp l).comp ((Per.σA (g : GQ l)).comp bk.ev) with hh'
  set f : Wq l bk.a →+* Per.BdRp l := h.comp PowerSeries.C with hf
  have hf' : h'.comp PowerSeries.C = f := by
    refine RingHom.ext fun w => ?_
    simp only [hh', hf, hh, RingHom.comp_apply, bk.ev_C, bk.gal_w]
  have hE : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have hE' : Per.θ l (Per.σA (g : GQ l) (bk.ev bk.E)) = 0 := by rw [GlobalTheory.RingBasics.θ_σA, hE, map_zero]
  have hY : Polynomial.eval₂ f (h q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (bk.ev bk.E) hE _ ?_
    have h1 := map_dvd h hroot
    rw [Polynomial.hom_eval₂, map_pow] at h1
    exact h1
  have hY' : Polynomial.eval₂ f (h' q) (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n := by
    refine mem_filtration_of_dvd n (Per.σA (g : GQ l) (bk.ev bk.E)) hE' _ ?_
    have h1 := map_dvd h' hroot
    rw [Polynomial.hom_eval₂, map_pow, hf'] at h1
    exact h1
  set s : Per.BdRp l := f ((l : Wq l bk.a) ^ M) with hs
  have hs' : s = (l : Per.BdRp l) ^ M := by rw [hs, map_pow, map_natCast]
  have hsu : IsUnit s := hs' ▸ (isUnit_l_BdRp l).pow M
  obtain ⟨r, hr⟩ := hsu.exists_left_inv
  have hsy : ∀ z : Per.BdRp l, z = s * (r * z) := fun z => by rw [← mul_assoc, mul_comm s r, hr, one_mul]

  have hroot' : ∀ z : Per.BdRp l, Polynomial.eval₂ f z (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) ∈ Per.FilP l n →
      (bk.Ep.map f).eval (r * z) ∈ Per.FilP l n := by
    intro z hz
    rw [hsy z, hs, Polynomial.scaleRoots_eval₂_mul, ← hs] at hz
    have h1 := (Per.FilP l n).mul_mem_left (r ^ bk.Ep.natDegree) hz
    rwa [← mul_assoc, ← mul_pow, hr, one_pow, one_mul, ← Polynomial.eval_map] at h1

  have hθh : ∀ x : bk.S, Per.θD l (h x) = ((Per.θ l (bk.ev x) : OC l) : ℂ_[l]) := fun x => hP.2.2.2.1 _
  have hθdiff : Per.θD l (h' q - h q) = 0 := by
    rw [map_sub, hθh, show h' q = aDp l (Per.σA (g : GQ l) (bk.ev q)) from rfl, hP.2.2.2.1,
      GlobalTheory.BKLim.BetaUniq.theta_gal_ev bk g q, sub_self]
  have hθs : Per.θD l s ≠ 0 := (hsu.map (Per.θD l)).ne_zero
  have hθq : Per.θD l (h q) = Per.θD l s * Per.θD l (h X) := by
    obtain ⟨c, hc⟩ := hq
    have h1 : q = (l : bk.S) ^ M * X + bk.E * c := by rw [← hc]; ring
    rw [h1, map_add (f := _), map_mul, map_mul, map_add (f := _), map_mul, map_mul, hθh bk.E, hE, hs', map_pow, map_pow,
      map_natCast, map_natCast]
    simp
  have hθy : Per.θD l (r * h q) = Per.θD l (h X) := by
    have h1 : Per.θD l s * Per.θD l (r * h q) = Per.θD l s * Per.θD l (h X) := by
      rw [← map_mul, ← mul_assoc, mul_comm s r, hr, one_mul, hθq]
    exact mul_left_cancel₀ hθs h1
  have hder : Per.θD l ((Polynomial.derivative (bk.Ep.map f)).eval (r * h q)) ≠ 0 := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.hom_eval₂, hθy, hf, ← RingHom.comp_assoc,
      show Per.θD l (h X) = ((Per.θD l).comp h) X from rfl, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X_eq_coe,
      RingHom.comp_apply, hθh]
    intro h0
    apply GlobalTheory.BKLim.ZNotRoot.theta_deriv_ne bk
    exact Subtype.ext h0
  have key := sub_mem_of_eval_mem (Per.FilP l n) (bk.Ep.map f) (r * h q) (r * h' q) (hroot' _ hY) (hroot' _ hY')
    (fun k => hP.2.2.1 _ (by
      rw [map_add (f := _), map_mul, ← mul_sub, map_mul, hθdiff, mul_zero, mul_zero, add_zero]; exact hder))
  rw [map_sub, show aDp l (Per.σA (g : GQ l) (bk.ev q)) = h' q from rfl, show aDp l (bk.ev q) = h q from rfl,
    hsy (h' q), hsy (h q), ← mul_sub]
  exact (Per.FilP l n).mul_mem_left s key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDivClosedDiscOfTopBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMap_of_map_eq (l : ℕ) [Fact l.Prime] {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A')
    (u : A) (u' : A') (ρ ρ' : ℝ≥0) (h0 : 0 < ρ') (hu : f u = u') (h : ρ' ≤ ρ) :
    ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F := by
  have h1 : ‖toDisc l u' ρ' (f u)‖ ≤ ρ := by
    have := norm_toDisc_pow_le (l := l) (u := u') 1 h0
    rw [pow_one, pow_one] at this
    rw [hu]
    exact this.trans (by exact_mod_cast h)
  exact ⟨_, isDiscMap_map f h1⟩

theorem BK.rho_zero_pos {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ :=
  NNReal.rpow_pos (Nat.cast_pos.2 hl.out.pos)

theorem norm_E_mul_of_topBasis (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (y : Disc l (s X) ρ) :
    ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  have hρ : 0 < ρ := bk.rho_zero_pos.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨cD, -, hmul, hle, -, -, hsup, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  have key : ∀ i, ‖cD i (toDisc l (s X) ρ (s bk.E) * y)‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖cD i y‖ := fun i => by
    rw [← hj.ext, hmul, _root_.GlobalTheory.BSP.BK.norm_toDisc_E_mul l K bk ρ h0 h1]
  refine le_antisymm (hsup _ _ (by positivity) fun i => ?_) ?_
  · rw [key]
    exact mul_le_mul_of_nonneg_left (hle i y) hρ'.le
  · rw [← le_div_iff₀' hρ']
    refine hsup _ _ (by positivity) fun i => ?_
    rw [le_div_iff₀' hρ', ← key]
    exact hle _ _

theorem E_dvd_of_topBasis (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ < 1)
    (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (hR : IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R) (y : Disc l (s X) ρ)
    (hy : toDisc l (s X) bk.ρ₀ (s bk.E) ∣ R y) : toDisc l (s X) ρ (s bk.E) ∣ y := by
  have hρ₀ := bk.rho_zero_pos
  have hρ : 0 < ρ := hρ₀.trans_le h0
  have hρ' : (0 : ℝ) < (ρ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast hρ) _
  obtain ⟨j, hj⟩ := exists_discMap_of_map_eq l s X (s X) ρ ρ hρ rfl le_rfl
  obtain ⟨j₀, hj₀⟩ := exists_discMap_of_map_eq l s X (s X) bk.ρ₀ bk.ρ₀ hρ₀ rfl le_rfl
  obtain ⟨RS, hRS⟩ := exists_discMap_of_map_eq l (RingHom.id bk.S) X X ρ bk.ρ₀ hρ₀ rfl h0
  obtain ⟨cD, hc, hmul, hle, hnull, -, hsup, hex, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ h1 j hj
  obtain ⟨cD₀, hc₀, hmul₀, hle₀, -, -, -, -, -⟩ :=
    GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ hρ₀ (h0.trans_lt h1) j₀ hj₀
  have comm : ∀ i x, cD₀ i (R x) = RS (cD i x) := fun i => by
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.1 (bk.DS bk.ρ₀) (fun z hz => by
        rw [nsmul_eq_mul] at hz
        exact (isUnit_l_disc l (X : bk.S) bk.ρ₀).mul_right_eq_zero.1 hz)
      ((cD₀ i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i))
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hle₀ i (R x)).trans (hR.norm_le x)).trans (one_mul _).ge)
      (AddMonoidHomClass.continuous_of_bound _ 1 fun x =>
        ((hRS.norm_le (cD i x)).trans (hle i x)).trans (one_mul _).ge)
      (fun a => by
        change cD₀ i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
        rw [hR.ext, hc, hRS.ext, RingHom.id_apply, RingHom.id_apply, hc₀])
    exact fun x => DFunLike.congr_fun h x
  obtain ⟨w, hw⟩ := hy
  have hd : ∀ i, ∃ z, cD i y = toDisc l (X : bk.S) ρ bk.E * z := fun i =>
    GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc l K bk ρ h0 h1 RS hRS _ ⟨cD₀ i w, by rw [← comm, hw, ← hj₀.ext, hmul₀]⟩
  choose z hz using hd
  have hzn : Filter.Tendsto z Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_zero_iff_norm_tendsto_zero.1 (hnull y)).div_const ((ρ : ℝ) ^ bk.Ep.natDegree)
    rw [zero_div] at h
    refine h.congr fun i => ?_
    rw [hz, _root_.GlobalTheory.BSP.BK.norm_toDisc_E_mul l K bk ρ h0 h1, mul_div_cancel_left₀ _ hρ'.ne']
  obtain ⟨y', hy'⟩ := hex z hzn
  refine ⟨y', ?_⟩
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine hsup _ 0 le_rfl fun i => ?_
  rw [map_sub, ← hj.ext, hmul, hy', hz, sub_self, norm_zero]

theorem div_E_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, bk.ρ₀ ≤ ρ → ρ < 1 →
    (∀ y : Disc l (s X) ρ, ‖toDisc l (s X) ρ (s bk.E) * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖) ∧
    ∀ R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → ∀ (h : ℕ) (y : Disc l (s X) ρ),
      toDisc l (s X) bk.ρ₀ (s bk.E) ^ h ∣ R y → toDisc l (s X) ρ (s bk.E) ^ h ∣ y := by
  intro l _ K bk A _ s ι TB ρ h0 h1
  refine ⟨norm_E_mul_of_topBasis l K bk A s ι TB ρ h0 h1, fun R hR h => ?_⟩
  have hρ' : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast bk.rho_zero_pos) _
  induction h with
  | zero => intro y _; rw [pow_zero]; exact one_dvd _
  | succ h ih =>
    intro y hy
    obtain ⟨y', rfl⟩ := E_dvd_of_topBasis l K bk A s ι TB ρ h0 h1 R hR y
      ((dvd_pow_self _ (Nat.succ_ne_zero h)).trans hy)
    obtain ⟨w, hw⟩ := hy
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih y' ⟨w, ?_⟩)
    rw [map_mul, hR.ext, RingHom.id_apply, pow_succ', mul_assoc, ← sub_eq_zero, ← mul_sub] at hw
    have h2 := norm_E_mul_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl (h0.trans_lt h1)
      (R y' - toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * w)
    rw [hw, norm_zero] at h2
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h2.symm).resolve_left hρ'.ne'))

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

theorem GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∃ s : ι → ZMod a → invL l (S O K e), (∀ j τ, (s j τ : K⟦X⟧) = E K l e ^ η * σ.1 τ j) ∧ toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • R.jB (toBcris t ϖ D.toPhiMod σ) = ∑ j, ϖ.iB t K (s j) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R σ c hc
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  refine ⟨fun j τ => ⟨E K l e ^ η * σ.1 τ j, mem_tot.1 hσM τ j⟩, fun j τ => rfl, ?_⟩
  set ej : ι → Vec K a ι := fun j _ => Pi.single j 1 with hej
  have hejM : ∀ j, ej j ∈ D.M := fun j => mem_tot.2 fun τ => mem_vecs.2 fun i => by
    simp only [hej]
    rcases eq_or_ne i j with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : ∀ j, E K l e ^ H • ej j ∈ D.L := fun j => D.lower _ (hejM j)
  have hcol : ∀ j τ i, (D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ) i = E K l e ^ H * D.mxInv τ i j := by
    intro j τ i
    simp only [hej, Pi.smul_apply, Matrix.mulVec_smul, Matrix.mulVec_single_one, smul_eq_mul,
      Matrix.col_apply, Matrix.transpose_apply]
  have hℓ : ∀ j i τ, E K l e ^ H * D.mxInv τ i j ∈ A O K := fun j i τ => by
    rw [← hcol]; exact D.mem_extc_iff.1 (mem_tot.1 (hL j) τ) i
  set ℓ : ι → ι → ZMod a → A O K := fun j i τ => ⟨_, hℓ j i τ⟩ with hℓdef
  have hcj : ∀ j, c j = fun i => ϖ.iTot t K (ℓ j i) := by
    intro j
    apply inclL_injective t ϖ D.toPhiMod
    rw [hc j]
    have hv : E K l e ^ H • ej j ∈ ME D.toPhiMod := mem_ME_of_mem_L (hL j)
    have h1 := toW_of_mx t ϖ D.toPhiMod ⟨_, hv⟩ (ℓ j) (fun τ => by
      have h2 : (fun i => ((ℓ j i τ : A O K) : K⟦X⟧)) = D.mxInv τ *ᵥ (E K l e ^ H • ej j) τ :=
        funext fun i => (hcol j τ i).symm
      change (E K l e ^ H • ej j) τ = D.mx τ *ᵥ fun i => ((ℓ j i τ : A O K) : K⟦X⟧)
      rw [h2, Matrix.mulVec_mulVec, D.mx_mul_mxInv, Matrix.one_mulVec])
    rw [← inclL_apply] at h1
    rw [← h1]
    ext1 i
    rw [toW_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej i) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) =
          fun τ => ⟨(((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ : K⟦X⟧),
            le_away _ _ (((fun _ => EIn l e (A O K)) ^ H : ZMod a → A O K) τ).2⟩ :=
        funext fun τ => Subtype.ext (by simp [hej, EIn])
      rw [h3, ϖ.iW_of_mem t K]
      simp only [map_pow, ϖ.iTot_E t K, Pi.single_eq_same, mul_one]
    · have h3 : (fun τ => (⟨(E K l e ^ H • ej j) τ i, mem_tot.1 hv τ i⟩ : invE l e (A O K))) = 0 :=
        funext fun τ => Subtype.ext (by simp [hej, Pi.single_eq_of_ne h])
      rw [h3, map_zero, Pi.single_eq_of_ne h, mul_zero]
  have hB : ∀ f : ZMod a → A O K, toB l O (ϖ.iTot t K f) =
      ϖ.iB t K (fun τ => ⟨f τ, le_away _ _ (A_le_S l e (f τ).2)⟩) := fun f => by
    rw [toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
  have hE : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) =
      toB l O (ϖ.iTot t K (fun _ => EIn l e _)) := by rw [ϖ.iTot_E t K]
  rw [← LinearEquiv.map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← LinearEquiv.map_smul, ← map_sum]
  congr 1
  ext i
  simp only [Pi.smul_apply, Finset.sum_apply, hcj, hB, toBcris_apply, hE, smul_eq_mul,
    ← map_pow, ← map_mul, ← map_sum]
  congr 1
  funext τ
  apply Subtype.ext
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.sum_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
    AddSubmonoidClass.coe_finsetSum, hℓdef]
  change (E K l e) ^ (H + η) * (D.mxInv τ *ᵥ σ.1 τ) i = ∑ j, E K l e ^ η * σ.1 τ j * (E K l e ^ H * D.mxInv τ i j)
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfIsNilpotentOfFinrankEqOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PotCrysRankOne

theorem eq_zero_of_isNilpotent_of_finrank_eq_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (h1 : Module.finrank k V = 1) {f : Module.End k V} (hf : IsNilpotent f) : f = 0 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hv (f v)
  obtain ⟨n, hn⟩ := hf
  have hp : ∀ m : ℕ, (f ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h0 : c ^ n • v = 0 := by rw [← hp, hn]; rfl
  have hc0 : c = 0 := IsNilpotent.eq_zero ⟨n, (smul_eq_zero.mp h0).resolve_right hv0⟩
  ext x
  obtain ⟨a, rfl⟩ := hv x
  rw [map_smul, ← hc, hc0, zero_smul, smul_zero]; rfl

end GlobalTheory.PotCrysRankOne

theorem GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character : DeRhamPotSemistable → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → ∀ (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw → IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) → IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) := by
  intro hB E Ω _ _ _ _ _ l _ P AI hT μ hμ A O _ _ _ Bw _ hd
  obtain ⟨T⟩ := hT
  have hc : Continuous fun g : ↥(Dec (F := E) A) =>
      ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    have e : (fun g : ↥(Dec (F := E) A) =>
        ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) =
        fun g : ↥(Dec (F := E) A) => Matrix.diagonal fun _ : Fin 1 => ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := by
      funext g; rfl
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => (Units.continuous_val.comp hμ).comp continuous_subtype_val)
  obtain ⟨LL', r', hm, hp⟩ := hB.isPstAt T Bw _ hc hd
  haveI := hp.finite
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have h1 : Module.finrank ℂ (WDSpace P ι (Bw.repE LL' r')) = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ LL' _ _ hp, Module.finrank_fin_fun]
  have hN : wdN P ι (Bw.repE LL' r') = 0 :=
    GlobalTheory.PotCrysRankOne.eq_zero_of_isNilpotent_of_finrank_eq_one h1 (isNilpotent_wdN P ι _)
  obtain ⟨K', hK, hcr⟩ := (GlobalTheory.PstLaws.isPotCrys_iff P _ hp).2 ((GlobalTheory.PstLaws.wdN_eq_zero_iff P _ ι).1 hN)
  exact ⟨LL', r', hm, K', hK, hcr⟩
end
end

