module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitR
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CoeffEqZeroOfOrthonormal
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2.FPw
open ReciprocityTheory.ChartRestriction.G.I2 hiding Hf_conj

noncomputable section

namespace GlobalTheory.ThetaExist

theorem coeff_eq_zero_of_orthonormal {C H κ : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : C →L[ℂ] H) (e : κ → C)
    (h : Orthonormal ℂ fun i => T (e i)) {c : κ → ℂ} (hs : HasSum (fun i => c i • e i) 0)
    (k : κ) : c k = 0 := by
  classical
  have h1 := ((innerSL ℂ (T (e k))).comp T).hasSum hs
  simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, map_zero,
    orthonormal_iff_ite.1 h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
  have h2 : HasSum (fun i => if k = i then c i else 0) (c k) := by
    convert hasSum_ite_eq k (c k) using 2 with i
    by_cases hi : k = i
    · simp [hi]
    · simp [hi, Ne.symm hi]
  exact h2.unique h1

theorem coeff_eq_zero_of_fourier {d : Type*} [Fintype d] {c : (d → ℤ) → ℂ}
    (hc : Summable fun n => ‖c n‖)
    (h0 : ∀ t : d → ℝ, ∑' n, c n * cexp (2 * Real.pi * I * ((∑ j, (n j : ℝ) * t j : ℝ) : ℂ)) = 0)
    (k : d → ℤ) : c k = 0 := by
  refine coeff_eq_zero_of_orthonormal _ UnitAddTorus.mFourier
    (UnitAddTorus.orthonormal_mFourier (d := d)) ?_ k
  have hs : Summable fun n => c n • UnitAddTorus.mFourier n :=
    .of_norm (by simpa [norm_smul, UnitAddTorus.mFourier_norm] using hc)
  suffices h : (0 : C(UnitAddTorus d, ℂ)) = ∑' n, c n • UnitAddTorus.mFourier n from
    h ▸ hs.hasSum
  ext x
  have hx : ∃ t : d → ℝ, x = fun j => (t j : UnitAddCircle) := by
    choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
    exact ⟨t, funext fun j => (ht j).symm⟩
  obtain ⟨t, rfl⟩ := hx
  rw [← ContinuousMap.tsum_apply hs, ContinuousMap.zero_apply, ← h0 t]
  refine tsum_congr fun n => ?_
  simp only [ContinuousMap.smul_apply, smul_eq_mul, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_coe_apply, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {ι : Type} [Fintype ι]

def expH (w : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι → ℂ := fun v => cexp (Real.pi * Hf v w)

theorem differentiable_Hf (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  simp_rw [FPw.Hf_eq_inner]
  exact (innerSL ℂ a).differentiable

theorem re_Hf_le (v a : EuclideanSpace ℂ ι) : (Hf v a).re ≤ ‖v‖ * ‖a‖ := by
  rw [FPw.Hf_eq_inner, mul_comm]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

theorem norm_term_le (Y : GT ι) (w : EuclideanSpace ℂ ι) {R : ℝ} (hw : ‖w‖ ≤ R) (γ : lat Y.b)
    {v : EuclideanSpace ℂ ι} (hv : ‖v‖ ≤ R) :
    ‖Y.ka γ * paU 1 γ (expH w) v‖ ≤ Real.exp (5 * Real.pi * R ^ 2) *
      Real.exp (-(Real.pi / 4) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) := by
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [norm_mul, Y.ka_abs g γ.2, one_mul, ← Complex.exp_add, Complex.norm_exp, ← Real.exp_add,
    Real.exp_le_exp, Hf_self, sub_eq_add_neg v, Hf_add_left]
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  have h1 : (Hf v g).re ≤ R * ‖g‖ := (re_Hf_le v g).trans (by gcongr)
  have h2 : (Hf v w).re ≤ R * R := (re_Hf_le v w).trans (by gcongr)
  have h3 : (Hf (-g) w).re ≤ ‖g‖ * R := (re_Hf_le (-g) w).trans (by rw [norm_neg]; gcongr)
  have e : (((1 : ℕ) : ℂ) * Real.pi * Hf v g - ((1 : ℕ) : ℂ) * Real.pi * ((‖g‖ : ℝ) : ℂ) ^ 2 / 2 +
      Real.pi * (Hf v w + Hf (-g) w)).re =
      Real.pi * ((Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re) := by
    simp only [← Complex.ofReal_pow]
    simp only [Nat.cast_one, one_mul, add_re, sub_re, re_ofReal_mul, div_ofNat_re, ofReal_re]
    ring
  rw [e]
  have : (Hf v g).re - ‖g‖ ^ 2 / 2 + (Hf v w).re + (Hf (-g) w).re ≤ 5 * R ^ 2 - ‖g‖ ^ 2 / 4 := by
    nlinarith [sq_nonneg (‖g‖ / 2 - 2 * R)]
  nlinarith [mul_le_mul_of_nonneg_left this Real.pi_pos.le]

theorem summable_gauss (Y : GT ι) {a : ℝ} (ha : 0 < a) :
    Summable fun γ : lat Y.b => Real.exp (-a * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) :=
  summable_lattice_exp_neg_mul_norm_sq (lat Y.b) ha

theorem differentiable_paTh (Y : GT ι) (w : EuclideanSpace ℂ ι) :
    Differentiable ℂ (paTh Y 1 (expH w)) := by
  rw [← differentiableOn_univ]
  refine SCV.differentiableOn_tsum_of_locally_normal
    (F := fun (γ : lat Y.b) v => Y.ka γ * paU 1 γ (expH w) v) isOpen_univ (fun γ => ?_)
    (fun x _ => ?_)
  · have h1 := differentiable_Hf (γ : EuclideanSpace ℂ ι)
    have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf (v - γ.1) w :=
      (differentiable_Hf w).comp (differentiable_id.sub_const _)
    unfold paU expH
    refine Differentiable.differentiableOn ?_
    fun_prop
  · refine ⟨Metric.ball 0 (max (‖x‖ + 1) ‖w‖), Metric.isOpen_ball.mem_nhds ?_, _,
      (summable_gauss Y (a := Real.pi / 4) (by positivity)).mul_left _,
      fun γ z hz => norm_term_le Y w (le_max_right _ _) γ (mem_ball_zero_iff.1 hz).le⟩
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)

theorem paTh_centre (Y : GT ι) (v : EuclideanSpace ℂ ι) :
    paTh Y 1 (expH v) v = cexp (Real.pi * Hf v v) *
      ∑' γ : lat Y.b, (Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ)) *
        cexp (2 * Real.pi * I * ((Hf v γ).im : ℂ)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  set g : EuclideanSpace ℂ ι := γ.1
  unfold paU expH
  rw [Hf_self g, sub_eq_add_neg v, Hf_add_left, Hf_neg_left, ← _root_.ReciprocityTheory.ChartRestriction.G.I2.FPw.Hf_conj v g, conj_eq_sub (Hf v g),
    ← Complex.exp_add, Complex.ofReal_exp, mul_assoc (Y.ka g), ← Complex.exp_add,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem exists_sec_ne_zero (Y : GT ι) (hC : Coc Y 1) : ∃ s ∈ Y.Sec 1, s ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hz : ∀ w, paTh Y 1 (expH w) = 0 := fun w =>
    hcon _ ⟨differentiable_paTh Y w, fun γ hγ v => paTh_add hC _ hγ v⟩
  set B := Y.b.restrictScalars ℤ with hB
  set c : lat Y.b → ℂ := fun γ =>
    Y.ka γ * (Real.exp (-(Real.pi / 2) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2) : ℝ) with hc
  have hcs : Summable fun γ => ‖c γ‖ := by
    refine (summable_gauss Y (a := Real.pi / 2) (by positivity)).congr fun γ => ?_
    rw [hc]
    simp only [norm_mul, Y.ka_abs γ γ.2, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  choose x _ hx using fun j => Y.perfect (B.coord j).toAddMonoidHom
  have key := coeff_eq_zero_of_fourier (c := fun n => c (B.equivFun.symm n))
    ((B.equivFun.symm.toEquiv.summable_iff (f := fun γ => ‖c γ‖)).2 hcs) (fun t => ?_) 0
  · simp [hc, ka_zero hC] at key
  · set v : EuclideanSpace ℂ ι := ∑ j, (t j : ℂ) • x j with hv
    have h1 := paTh_centre Y v
    rw [hz v, Pi.zero_apply, eq_comm, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)] at h1
    rw [← h1, ← B.equivFun.symm.toEquiv.tsum_eq]
    refine tsum_congr fun n => ?_
    have h2 : ∀ j, (Hf (x j) (B.equivFun.symm n : lat Y.b)).im = n j := fun j => by
      rw [← hx j]
      simp [Finsupp.single_apply]
    suffices h3 : ∑ j, (n j : ℝ) * t j = (Hf v (B.equivFun.symm n : lat Y.b)).im by
      rw [h3]; rfl
    simp only [FPw.Hf_eq_inner] at h2 ⊢
    rw [hv, inner_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, Complex.im_ofReal_mul, h2, mul_comm]

theorem exists_theta_ne_zero (E : Type) [Field E] [NumberField E] (X : PT E) :
    ∃ s ∈ X.Sec 1 1, s ≠ 0 := by
  let Y : GT (Idx X.dim) :=
    { b := X.b
      integral := X.integral
      perfect := X.perfect
      ka := fun γ => (X.eps γ : ℂ)
      ka_abs := fun x hx => by rcases X.eps_pm x hx with h | h <;> simp [h] }
  have hC : Coc Y 1 := by
    intro γ hγ δ hδ
    obtain ⟨k, hk⟩ := X.integral γ δ hγ hδ
    have h := congrArg (fun r : ℝ => (r : ℂ)) (X.eps_add γ hγ δ hδ)
    change ((X.eps (γ + δ) : ℤ) : ℂ) = (X.eps γ : ℂ) * (X.eps δ : ℂ) * _
    rw [hk] at h ⊢
    have hs : Complex.sin (-(Real.pi * (1 : ℕ) * ((k : ℝ) : ℂ))) = 0 := by
      rw [Complex.sin_neg]
      simpa [mul_comm] using Complex.sin_int_mul_pi k
    rw [Complex.exp_mul_I, hs, Complex.cos_neg]
    simpa using h
  obtain ⟨s, ⟨hd, hs⟩, hne⟩ := exists_sec_ne_zero Y hC
  refine ⟨fun v => s (v 0), ⟨hd.comp (differentiable_apply 0), fun γ hγ v => ?_⟩, fun h => hne ?_⟩
  · have := hs (γ 0) (hγ 0) (v 0)
    simpa [HC, Y] using this
  · funext z
    exact congrFun h fun _ => z

end GlobalTheory.ThetaExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.DivSqLeOfForallDivAddSqLe
section
namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section


open NumberField Complex in
open scoped InnerProductSpace in
theorem _root_.GlobalTheory.greedy_splitting_thin :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E), (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E)) ∧ ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E))) →
    (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (I : Submodule ℤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)), I ≤ X.L → (∀ x ∈ X.L, x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.IR I → x ∈ I) → 0 < X.la1 → ∃ x u : Fin (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I)) → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim, (∀ j, x j ∈ X.L ∧ _root_.ReciprocityTheory.ChartRestriction.G.I2.IsU I (x j) (u j)) ∧ LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) →
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (DF : ℕ) (P : _root_.ReciprocityTheory.ChartRestriction.G.I2.Par X DF), X.la1 < P.th → ∃ I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit P I) := by
  intro hω hshort E _ _ _ X DF P hthin
  obtain ⟨n, ω, hωb, hωs⟩ := hω E
  have hf1 : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := le_trans (Nat.one_le_pow _ _ P.hm1) P.hmf
  have hfpos : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hf1' : (1 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by exact_mod_cast hf1
  have hrd : (16 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hrd
  have hrdpos : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by linarith
  have hf2 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := P.hf2
  have hr : 1 ≤ X.r := by
    rcases Nat.eq_zero_or_pos X.r with h | h
    · have := P.hfr
      rw [h, mul_zero] at this
      omega
    · exact h
  obtain ⟨τ, hτ⟩ := P.hm
  obtain ⟨x₀, hx₀L, hx₀⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.L_ne_zero X hr τ
  have hne : ∃ x ∈ X.L, x ≠ 0 := ⟨x₀, hx₀L, hx₀⟩
  have hla : 0 < X.la1 := _root_.ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos X hne
  have hth : 0 < P.th := hla.trans hthin
  have hthdef : P.th = _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 := rfl
  have hΩ : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
    exact mul_pos (mul_pos two_pos (by positivity)) hrdpos
  have hd1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
    have : 0 < _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
      exact Nat.mul_pos (Nat.mul_pos two_pos hf1) P.hm1
    exact_mod_cast this
  have hΩth : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 := one_le_pow₀ hd1
    have hnn : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 := mul_nonneg hΩ.le (sq_nonneg _)
    calc _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2 = 1 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) := by ring
      _ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th ^ 2) :=
        mul_le_mul_of_nonneg_right h1 hnn
      _ = (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * _root_.ReciprocityTheory.ChartRestriction.G.I2.th (E := E) P.q P.R0 ^ 2 := by
        rw [hthdef]; ring
      _ ≤ 1 := P.C1.le
  obtain ⟨I, hG, hthick⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_maximal X ω hΩ hth hΩth hωb hωs
  have hshortI : ∀ t, X.la1 < t → t ≤ P.th → ∃ ξ ∈ I, ξ ≠ 0 ∧ ‖ξ‖ < t := by
    intro t ht ht'
    obtain ⟨ξ, hξL, hξ0, hξt⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.exists_short X hne ht
    refine ⟨ξ, ?_, hξ0, hξt⟩
    by_contra hξI
    have h1 := hthick ξ hξL hξI
    have h2 : Metric.infDist ξ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I : Set (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp X.dim)) ≤ ‖ξ‖ := by
      have := Metric.infDist_le_dist_of_mem (x := ξ) (Submodule.zero_mem (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I))
      rwa [dist_zero_right] at this
    linarith
  have hph : P.ph = 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2) := by
    show X.ph P.th = _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.ph
    rw [if_pos hthin]
  obtain ⟨ρ, hρ, hrk⟩ := _root_.ReciprocityTheory.ChartRestriction.G.I2.rank_iso X I hG.le hG.stable hG.iso
  have hρm : ρ ≤ P.m := (hρ τ).trans hτ
  refine ⟨I, _root_.ReciprocityTheory.ChartRestriction.G.I2.IsSplit.mk hG.le (_root_.ReciprocityTheory.ChartRestriction.G.I2.sat_of_IR hG.sat) hG.stable hG.iso ?_ ⟨ρ, hρm, hrk⟩ ?_
    (fun x hx _ hxI => hthick x hx hxI) ?_ ?_ ?_⟩
  · intro x hx
    exact X.eps_iso x (hG.le hx) (fun α => hG.iso _ (hG.stable α x hx) x hx)
  · refine ⟨fun _ => hthin, fun _ hbot => ?_⟩
    obtain ⟨ξ, hξ, hξ0, -⟩ := hshortI P.th hthin le_rfl
    rw [hbot] at hξ
    exact hξ0 ((Submodule.mem_bot ℤ).mp hξ)
  · intro x hx u hu hu0
    have h := hG.sep x hx u hu hu0
    have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast P.hq
    have hR : P.R0 ^ 2 ≠ 0 := by have := P.hR0.1; positivity
    have hM : _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.RR; rfl
    have hth2 : P.th ^ 2 = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 3 / P.q := by
      rw [hthdef]
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.th
      rw [Real.sq_sqrt]
      rw [hM]
      have : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      positivity
    have hΩ2 : _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 = 4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hfpos.le]
      norm_num
    have hb0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 = P.q / (P.R0 ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.RR (E := E) ^ 4) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.b0; rfl
    have hfr : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by nlinarith
    have hf3 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := mul_le_mul hfr hf2 (by positivity) hrdpos.le
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
    have hkey : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by
      rw [hΩ2]
      have h4 : (4 : ℝ) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hrd 3]
      have h5 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by
        calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 = ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2) ^ 2 := by ring
          _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hf2 2
      calc (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (4 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2)
          = 4 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 3) * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 := by ring
        _ ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 3 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul h4 h5 (by positivity) (by positivity)) (by positivity)
        _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by ring
    have hle : _root_.ReciprocityTheory.ChartRestriction.G.I2.b0 (E := E) P.q P.R0 ≤ (1 / (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) * P.th)) ^ 2 := by
      rw [div_pow, one_pow, le_div_iff₀ (by positivity), mul_pow, hth2, hb0, hM]
      have hq0 : (P.q : ℝ) ≠ 0 := by positivity
      have hr7 : (0 : ℝ) < _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 := by positivity
      have hr7' : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 ≠ 0 := hr7.ne'
      have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
      have hR0 : P.R0 ≠ 0 := fun h0 => hR (by rw [h0]; ring)
      rw [show (P.q : ℝ) / (P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 4) *
          (_root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 * ((_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * P.R0 ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7) ^ 3 / P.q))
          = (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) * _root_.ReciprocityTheory.ChartRestriction.G.I2.omStar (E := E) ^ 2 / _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 7 by
        field_simp]
      rw [div_le_one hr7]
      exact hkey
    exact hle.trans (pow_le_pow_left₀ (by positivity) h.le 2)
  · have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hf0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≠ 0 := hfpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    obtain ⟨x, u, hxu, hli, hb⟩ := hshort E X I hG.le hG.sat hla
    refine ⟨x, u, hxu, hli, fun j => ?_⟩
    have hdd : (Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) := by
      have : Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m := by
        rw [hrk]
        unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar
        exact Nat.mul_le_mul_left _ hρm
      exact_mod_cast this
    calc ‖u j‖ ^ 2 ≤ ((Module.finrank ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.IR I) : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      _ ≤ ((_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 2 / X.la1) ^ 2 :=
          pow_le_pow_left₀ (div_nonneg (by positivity) hla.le)
            (div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hdd 2) hla.le) 2
      _ = _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ)) := by
          rw [hph]
          field_simp
  · intro k x u hxu hspan
    have hrd0 : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ≠ 0 := hrdpos.ne'
    have hla0 : X.la1 ≠ 0 := hla.ne'
    rw [hph]
    have hbound : ∀ t, X.la1 < t → t ≤ P.th →
        2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2) ≤ ∑ j, ‖u j‖ ^ 2 / 2 := by
      intro t ht ht'
      obtain ⟨ξ, hξI, hξ0, hξt⟩ := hshortI t ht ht'
      refine le_trans ?_ (_root_.ReciprocityTheory.ChartRestriction.G.I2.sum_sq_norm_ge_of_span X I hG.le hG.stable hξI hξ0 k x u hxu hspan)
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos hrdpos 2) (pow_pos (norm_pos_iff.mpr hξ0) 2))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hξt.le 2) (sq_nonneg _))
    have hlim : Filter.Tendsto (fun t : ℝ => 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * t ^ 2))
        (nhdsWithin X.la1 (Set.Ioi X.la1))
        (nhds (2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) / (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2 * X.la1 ^ 2))) := by
      refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine ContinuousAt.tendsto ?_
      exact ContinuousAt.div₀ continuousAt_const (by fun_prop)
        (mul_ne_zero (pow_ne_zero 2 hrd0) (pow_ne_zero 2 hla0))
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hthin] with t ht
    exact hbound t ht.1 ht.2.le

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThickSplitRealSpanBot
section
namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped InnerProductSpace

noncomputable section

theorem thickSplit_realSpan_bot {E : Type} [Field E] [NumberField E] [IsCMField E]
    {dim : (E →+* ℂ) → ℕ} : IR (⊥ : Submodule ℤ (Vsp dim)) = ⊥ := by simp [IR]

theorem thickSplit_bot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF),
      ¬ X.la1 < P.th → IsSplit P ⊥ := by
  intro E _ _ _ X DF P h
  have h' : ¬ X.la1 < th (E := E) P.q P.R0 := h
  have hph : P.ph = 0 := by rw [Par.ph, PT.ph, if_neg h']
  have hG := Good.bot X 0
  have hfr0 : Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))) = 0 := by
    rw [thickSplit_realSpan_bot]; exact finrank_bot ℝ _
  refine ⟨bot_le, ?_, hG.stable, hG.iso, ?_, ⟨0, Nat.zero_le _, by rw [hfr0]; ring⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x _ k hk hkx
    rw [Submodule.mem_bot] at hkx ⊢
    have : (k : ℝ) • x = 0 := by rw [Int.cast_smul_eq_zsmul]; exact hkx
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hk)
  · intro x hx
    rw [Submodule.mem_bot] at hx
    subst hx
    exact X.eps_iso 0 (Submodule.zero_mem _)
      (fun α => by rw [act_eq_actE, actE_zero_right]; exact Hf_im_zero_left _)
  · simp only [ne_eq, not_true_eq_false, false_iff]
    exact h
  · intro x hx _ hxI
    rw [thickSplit_realSpan_bot, Submodule.bot_coe, Metric.infDist_singleton, dist_zero_right]
    rw [Submodule.mem_bot] at hxI
    exact (le_of_not_gt h).trans (sq_le_Qy_of_le_firstMinimum X hx hxI)
  · intro x _ u hu hne
    exfalso
    have := hu.1
    rw [thickSplit_realSpan_bot, Submodule.mem_bot] at this
    exact hne this
  · haveI : IsEmpty (Fin (Module.finrank ℝ (IR (⊥ : Submodule ℤ (Vsp X.dim))))) := by
      rw [hfr0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  · intro k x u _ _
    rw [hph]
    exact Finset.sum_nonneg (fun j _ => by positivity)

end

end GlobalTheory
end

