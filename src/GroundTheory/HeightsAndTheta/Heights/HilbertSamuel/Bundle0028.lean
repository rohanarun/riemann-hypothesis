module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis hermZpow hermLine_eq_of isSmoothHerm_tensor
  isSmoothHerm_hermZpow fam_update_eq_snoc fam_snoc_zpow isSmoothHerm_ofMetrics_fs)

noncomputable section

set_option linter.unusedSectionVars false

section Scaling

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zcomb_eq_tensor (A X : HermLine ι) (q : ℕ) :
    HermLine.zcomb A X q 1 = (hermZpow A q).tensor X :=
  hermLine_eq_of (by funext k; simp [HermLine.zcomb, HermLine.tensor, hermZpow])
    (by funext z; simp [HermLine.zcomb, HermLine.tensor, hermZpow])

theorem isSmoothHerm_zcomb {A X : HermLine ι} (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A X q 1) := by
  rw [zcomb_eq_tensor]
  exact isSmoothHerm_tensor (isSmoothHerm_hermZpow hA q) hX

theorem isConjInvariantH_zcomb {A B : HermLine ι} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) (p q : ℤ) :
    IsConjInvariantH (HermLine.zcomb A B p q) := by
  intro z
  show A.h _ ^ p * B.h _ ^ q = A.h z ^ p * B.h z ^ q
  rw [hA z, hB z]

theorem isConjInvariantH_fsH : IsConjInvariantH (fsH ι) := by
  intro z
  simp [fsH, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem fam_update_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) :
    I P (n + 1) (Function.update L a (HermLine.zcomb A X q 1)) =
      q * I P (n + 1) (Function.update L a A) + I P (n + 1) (Function.update L a X) := by
  rw [zcomb_eq_tensor]
  have hAq := isSmoothHerm_hermZpow hA (q : ℤ)
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAq hX), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hX, hI.2.1 P n _ _ _ hP hR hAq hX, fam_snoc_zpow hI hP _ hR hA (q : ℤ)]
  push_cast
  ring

theorem fam_eq_famExt_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (q : ℕ) (T : Finset (Fin (n + 1))) (t : Fin (n + 1) → Fin 2) :
    I P (n + 1) (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
      famExt I P (n + 1) ![X, A] (fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (t j) 1) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis ![X, A] t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (w : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then w else F (t j)) =
          Function.update (fun j => if j ∈ T then w else F (t j)) a w := by
      intro β w F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (w : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then w else F (t j)) a (F i) =
          fun j => if j ∈ T then w else F (Function.update t a i j) := by
      intro β w F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hL : ∀ j, IsSmoothHerm ((fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact isSmoothHerm_zcomb hA hX q
      · exact hsm (t j)
    have eL : (fun j => if j ∈ insert a T then HermLine.zcomb A X q 1 else ![X, A] (t j)) =
        Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a
          (HermLine.zcomb A X q 1) :=
      hins _ _
    have eV : (fun j => if j ∈ insert a T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) =
        Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
          ![1, (q : ℝ)] :=
      hins (![1, (q : ℝ)] : Fin 2 → ℝ) fun i => Pi.single i 1
    have hA1 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a A =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 1 j) :=
      hupd _ ![X, A] 1
    have hX0 : Function.update (fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (t j)) a X =
        fun j => if j ∈ T then HermLine.zcomb A X q 1 else ![X, A] (Function.update t a 0 j) :=
      hupd _ ![X, A] 0
    have hV1 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 1 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 1 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 1
    have hV0 : Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a
        (Pi.single 0 1) = fun j => if j ∈ T then ![1, (q : ℝ)] else Pi.single (Function.update t a 0 j) 1 :=
      hupd (![1, (q : ℝ)] : Fin 2 → ℝ) (fun i => Pi.single i 1) 0
    have hw : (![1, (q : ℝ)] : Fin 2 → ℝ) = (q : ℝ) • Pi.single 1 1 + (1 : ℝ) • Pi.single 0 1 := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, fam_update_zcomb hI hP _ hL a hA hX q, hA1, hX0, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then (![1, (q : ℝ)] : Fin 2 → ℝ) else Pi.single (t j) 1) a) hw,
      MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, hV1, hV0,
      smul_eq_mul, smul_eq_mul]
    simp only [RingHom.id_apply]
    ring

theorem tendsto_fam_zcomb (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) :
    Tendsto (fun q : ℕ => I P (n + 1) (fun _ => HermLine.zcomb A X q 1) / (q : ℝ) ^ (n + 1)) atTop
      (𝓝 (I P (n + 1) (fun _ => A))) := by
  have hfull : ∀ q : ℕ, I P (n + 1) (fun _ => HermLine.zcomb A X q 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) := by
    intro q
    simpa using fam_eq_famExt_zcomb hI hP hA hX q Finset.univ (fun _ => 0)
  have hscale : ∀ q : ℕ, q ≠ 0 → famExt I P (n + 1) ![X, A] (fun _ => ![1, (q : ℝ)]) / (q : ℝ) ^ (n + 1) =
      famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1]) := by
    intro q hq
    have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have e : (fun _ : Fin (n + 1) => (![1, (q : ℝ)] : Fin 2 → ℝ)) =
        fun i => (fun _ : Fin (n + 1) => (q : ℝ)) i • (![1 / (q : ℝ), 1] : Fin 2 → ℝ) := by
      funext i j
      fin_cases j <;> simp [hq']
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    field_simp
    simp only [RingHom.id_apply]
    ring
  have hlim : Tendsto (fun q : ℕ => famExt I P (n + 1) ![X, A] (fun _ => ![1 / (q : ℝ), 1])) atTop
      (𝓝 (famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]))) := by
    simp only [famExt_apply]
    refine tendsto_finsetSum _ fun s _ => Tendsto.const_mul _ (tendsto_finsetProd _ fun j _ => ?_)
    generalize s j = i
    fin_cases i
    · simpa using (tendsto_one_div_atTop_nhds_zero_nat : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0))
    · simp
  have hval : famExt I P (n + 1) ![X, A] (fun _ => ![0, 1]) = I P (n + 1) (fun _ => A) := by
    have e : (fun _ : Fin (n + 1) => (![0, 1] : Fin 2 → ℝ)) = fun j => Pi.single ((fun _ => (1 : Fin 2)) j) 1 := by
      funext j i
      fin_cases i <;> simp
    rw [e, famExt_basis]
    rfl
  rw [hval] at hlim
  refine hlim.congr' ((eventually_ge_atTop 1).mono fun q hq => ?_)
  dsimp only
  rw [hfull, hscale q (by omega)]

end Scaling

theorem ArithmeticVolumeNef.proof (hS : MonomialShift.Statement) (hPM : PerturbMonomial.Statement)
    (hU : UpperNormalisation.Statement) : ArithmeticVolumeNef.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II hD hII hY hbir ha hP0 hsemi hmon hconj
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  let f : ℕ → ℝ := fun τ =>
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F)
  show limsup f atTop ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hcnt : ∀ (B : HermLine ι) (La : ℕ → AddSubgroup Ω) (τ : ℕ),
      0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B) La τ := fun B La τ => by
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hf0 : ∀ τ, 0 ≤ f τ := fun τ => div_nonneg (hcnt _ _ _) (div_nonneg (by positivity) hFpos.le)

  have key : ∀ q : ℕ, 1 ≤ q → ∀ ε : ℝ, 0 < ε → limsup f atTop ≤
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) + ε) / (q : ℝ) ^ (D + 1) := by
    intro q hq ε hε
    set B := HermLine.zcomb A (fsH ι) q 1 with hBdef
    set c := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε with hc
    have hsg : IsSmallGeneratedDatum P0 y D B := hPM K ι Ω y D a A P0 q hD hY hbir ha hP0 hsemi hmon hq
    have hBconj : IsConjInvariantH B := isConjInvariantH_zcomb hconj isConjInvariantH_fsH _ _
    have hBa : ∀ k, 1 ≤ B.a k := by
      intro k
      simp only [hBdef, HermLine.zcomb, fsH, HermLine.ofMetrics, ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.one_apply, mul_one]
      nlinarith [show (0 : ℤ) ≤ (q : ℤ) * (a k : ℤ) by positivity]
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hU K ι Ω y D B P0 II hD hII hY hbir hsg hBconj hBa ε hε)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hbound : ∀ᶠ τ : ℕ in atTop, f τ ≤ c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) := by
      filter_upwards [eventually_ge_atTop (q * N + 1)] with τ hτ
      have hτpos : (0 : ℝ) < τ := by exact_mod_cast (show 0 < τ by omega)
      have hdm := Nat.div_add_mod τ q
      have hmod := Nat.mod_lt τ (show 0 < q by omega)
      have hqn : τ ≤ q * (τ / q + 1) := by rw [Nat.mul_add, mul_one]; omega
      have hnN : N ≤ τ / q + 1 := by
        have : N ≤ τ / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; omega)
        omega
      have hnq : (((τ / q + 1 : ℕ) : ℝ)) * q ≤ τ + q := by
        have := Nat.div_mul_le_self τ q
        have h' : (τ / q + 1) * q ≤ τ + q := by rw [Nat.add_mul, one_mul]; omega
        exact_mod_cast h'
      have h1 : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
          c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) :=
        (hS K ι Ω y D a A P0 q τ (τ / q + 1) hY hbir ha hP0 hsemi hmon hq hqn).trans (hN _ hnN)
      have hc0 : 0 ≤ c := by
        have hpos : 0 < (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F := by positivity
        exact (mul_nonneg_iff_of_pos_right hpos).mp ((hcnt _ _ _).trans h1)
      have hnle : (((τ / q + 1 : ℕ) : ℝ)) ≤ (τ + q) / q := by rw [le_div_iff₀ hqpos]; exact hnq
      have h2 : (((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) ≤ ((τ + q) / q) ^ (D + 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hnle _
      have e : c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1) =
          c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) / ((τ : ℝ) ^ (D + 1) / F) := by
        rw [show (1 : ℝ) + q / τ = (τ + q) / τ by field_simp]
        simp only [div_pow]
        field_simp
      show smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ / ((τ : ℝ) ^ (D + 1) / F) ≤ _
      rw [e, div_le_div_iff_of_pos_right (by positivity)]
      calc _ ≤ c * ((((τ / q + 1 : ℕ) : ℝ)) ^ (D + 1) / F) := h1
        _ ≤ c * ((((τ : ℝ) + q) / q) ^ (D + 1) / F) := by gcongr
    have hlim : Tendsto (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop
        (𝓝 (c / (q : ℝ) ^ (D + 1))) := by
      have h0 : Tendsto (fun τ : ℕ => (q : ℝ) / τ) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (c / (q : ℝ) ^ (D + 1))
    calc limsup f atTop ≤ limsup (fun τ : ℕ => c / (q : ℝ) ^ (D + 1) * (1 + q / (τ : ℝ)) ^ (D + 1)) atTop :=
          limsup_le_limsup hbound (isCoboundedUnder_le_of_le atTop hf0) hlim.isBoundedUnder_le
      _ = c / (q : ℝ) ^ (D + 1) := hlim.limsup_eq

  have hT := tendsto_fam_zcomb (hII K ι) hY hsemi.1 (show IsSmoothHerm (fsH ι) from isSmoothHerm_ofMetrics_fs 1)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ q : ℕ in atTop, limsup f atTop - ε ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A (fsH ι) q 1) / (q : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hk := key q hq ε hε
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
    have hεq : ε / (q : ℝ) ^ (D + 1) ≤ ε := div_le_self hε.le hq1
    rw [add_div] at hk
    linarith
  have := ge_of_tendsto hT hev
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem constShift_a (A : HermLine ι) (η : ℝ) : (HermLine.constShift A η).a = A.a := by
  simp [HermLine.constShift, HermLine.tensor, HermLine.ofWeight]

omit [∀ k, Fintype (ι k)] in
theorem constShift_h (A : HermLine ι) (η : ℝ) (z : (Σ k, ι k) → ℂ) :
    (HermLine.constShift A η).h z = A.h z * Real.exp (-η) := rfl

theorem isSmoothHerm_constShift {A : HermLine ι} (hA : IsSmoothHerm A) (η : ℝ) :
    IsSmoothHerm (HermLine.constShift A η) := by
  have : (HermLine.constShift A η).h = fun z => A.h z * Real.exp (-η) := rfl
  unfold IsSmoothHerm at hA ⊢
  rw [this]
  exact hA.mul contDiffOn_const

omit [∀ k, Fintype (ι k)] in
theorem isConjInvariantH_constShift {A : HermLine ι} (hA : IsConjInvariantH A) (η : ℝ) :
    IsConjInvariantH (HermLine.constShift A η) := by
  intro z
  rw [constShift_h, constShift_h, hA z]

theorem leviForm_constShift (A : HermLine ι) (η : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    leviForm (fun x => Real.log ((HermLine.constShift A η).h x)) z w =
      leviForm (fun x => Real.log (A.h x)) z w := by
  have hU : IsOpen {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} := by
    have : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {x | x ⟨k, i⟩ ≠ 0} := by
      ext x
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h1 : (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fun x => Real.log (A.h x) + (-η) := by
    filter_upwards [hU.mem_nhds hz] with x hx
    rw [constShift_h, Real.log_mul (A.pos x hx).ne' (Real.exp_pos _).ne', Real.log_exp]
  have h2 : fderiv ℝ (fun x => Real.log ((HermLine.constShift A η).h x)) =ᶠ[𝓝 z]
      fderiv ℝ (fun x => Real.log (A.h x)) := by
    filter_upwards [h1.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq, fderiv_add_const]
  unfold leviForm
  rw [h2.fderiv_eq]

theorem isSemipositiveRel_constShift {P0 P : Ideal (MRing ι)} {A : HermLine ι}
    (hA : IsSemipositiveRel P0 P A) (η : ℝ) : IsSemipositiveRel P0 P (HermLine.constShift A η) := by
  refine ⟨isSmoothHerm_constShift hA.1 η, fun z hz w hw => ?_⟩
  rw [leviForm_constShift A η hz.1 w]
  exact hA.2 z hz w hw

end Shift

theorem exists_small_section_of_arithmeticVolume_pos {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω}
    {D : ℕ} (h : 0 < arVolP Pr La 1 D) : ∃ n, 1 ≤ n ∧ ∃ s ∈ La n, s ≠ 0 ∧ Pr n s := by
  by_contra hne
  push Not at hne
  have hzero : ∀ k, 1 ≤ k → smallSectionCount Pr La k = 0 := by
    intro k hk
    have hsub : Subsingleton {s : La k // Pr k (s : Ω)} := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha0 : (a : Ω) = 0 := by
        by_contra h0
        exact hne k hk a a.2 h0 ha
      have hb0 : (b : Ω) = 0 := by
        by_contra h0
        exact hne k hk b b.2 h0 hb
      exact Subtype.ext (Subtype.ext (ha0.trans hb0.symm))
    have := hsub
    have hc : Nat.card {s : La k // Pr k (s : Ω)} ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    unfold smallSectionCount
    interval_cases Nat.card {s : La k // Pr k (s : Ω)} <;> simp
  have : arVolP Pr La 1 D = 0 := by
    unfold arVolP
    refine (limsup_congr ?_).trans (limsup_const 0)
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [one_mul, hzero k hk, zero_div]
  linarith

theorem G4.proof (hG6 : ArithmeticVolumeBig.Statement) (hCS : ConstantShift.Statement) : G4.Statement := by
  intro K _ ι _ Ω _ _ y D M P0 II hD hII har hb hM hpos
  obtain ⟨η, hη0, hηlt⟩ : ∃ η : ℝ, 0 < η ∧ ((D : ℝ) + 1) * η * geomDeg (mCoordIdeal y) M D <
      II K ι (mCoordIdeal y) (D + 1) (fun _ => M) := by
    set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => M)
    set g := geomDeg (mCoordIdeal y) M D
    have hden : 0 < 2 * (((D : ℝ) + 1) * |g| + 1) := by positivity
    refine ⟨T / (2 * (((D : ℝ) + 1) * |g| + 1)), div_pos hpos hden, ?_⟩
    set η := T / (2 * (((D : ℝ) + 1) * |g| + 1))
    have hη0 : 0 < η := div_pos hpos hden
    have he : η * (2 * (((D : ℝ) + 1) * |g| + 1)) = T := div_mul_cancel₀ T hden.ne'
    have h1 : ((D : ℝ) + 1) * η * g ≤ ((D : ℝ) + 1) * η * |g| :=
      mul_le_mul_of_nonneg_left (le_abs_self g) (by positivity)
    have h3 : 0 ≤ ((D : ℝ) + 1) * η * |g| := by positivity
    nlinarith
  have hshift := hCS K ι (II K ι) (mCoordIdeal y) D M η (hII K ι) har hM.semipos.1
  have hpos' : 0 < II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.constShift M η) := by
    rw [hshift]
    linarith
  have hvol := hG6 K ι Ω y D (HermLine.constShift M η) P0 II hD hII har hb hM.normalForm_baseLattice_le_dualSpan_sup_line
    (isSemipositiveRel_constShift hM.semipos η) (by rw [constShift_a]; exact hM.nef)
    (isConjInvariantH_constShift hM.conjInv η)
  obtain ⟨n, hn, s, hs, hs0, hsmall⟩ := exists_small_section_of_arithmeticVolume_pos (hpos'.trans_le hvol)
  have hn' : (0 : ℝ) < n * η := mul_pos (by exact_mod_cast hn) hη0
  refine ⟨n, s, hn, by rwa [constShift_a] at hs, hs0, Real.exp (-(n * η)), ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    linarith
  · intro dg dh g h z hg hh hdeg heq hz
    have hle := hsmall dg dh g h z hg hh (by rw [constShift_a]; exact hdeg) heq hz
    have e : Real.exp (-(n * η)) = Real.exp (-η) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    refine hle.trans (le_of_eq ?_)
    rw [constShift_h, mul_pow, e]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LerpSelfZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

theorem Weight.lerp_self_zero {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) : W.lerp W 0 = W := by
  cases W
  simp only [Weight.lerp, zero_mul, add_zero]

theorem SupNormAgainstL2.proof (h : UniformBergmanBound.Statement) : SupNormAgainstL2.Statement := by
  intro D X _ _ _ _ _ A L W dV hW
  obtain ⟨C, hC⟩ := h A L W W dV hW hW
  refine ⟨⟨Real.sqrt C, fun n hn s hs x => ?_⟩, fun n s hs M hM => ?_⟩
  · set V : Submodule ℂ (Fin A.n → X → ℂ) := ℂ ∙ s
    have hV : V ≤ L.sections n := (Submodule.span_singleton_le_iff_mem _ _).2 hs
    have hB := hC n hn 0 ⟨le_rfl, zero_le_one⟩ V hV x
    rw [Weight.lerp_self_zero] at hB
    set r := ptNormSq W n s x / sectionL2NormSq W dV n s
    have hr0 : 0 ≤ r := div_nonneg (ptNormSq_nonneg W n s x) (sectionL2NormSq_nonneg W dV n s)
    have hbdd : BddAbove (range fun v : V => ptNormSq W n (v : Fin A.n → X → ℂ) x /
        sectionL2NormSq W dV n v) := by
      refine ⟨r, ?_⟩
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp only [ptNormSq_smul, sectionL2NormSq_smul]
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hr0
      · rw [mul_div_mul_left _ _ (by positivity)]
    have hle : r ≤ bergman W dV V n x :=
      le_ciSup hbdd (⟨s, Submodule.mem_span_singleton_self s⟩ : V)
    have hrC : r ≤ C * (n : ℝ) ^ D := hle.trans hB
    rcases (sectionL2NormSq_nonneg W dV n s).eq_or_lt with h0 | hpos
    · rw [ptNormSq_eq_zero_of_l2NormSq_eq_zero W dV hs h0.symm x, Real.sqrt_zero]
      positivity
    · have hpt : ptNormSq W n s x ≤ C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s) := by
        rw [← mul_assoc, ← div_le_iff₀ hpos]; exact hrC
      calc Real.sqrt (ptNormSq W n s x)
          ≤ Real.sqrt (C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s)) := Real.sqrt_le_sqrt hpt
        _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s) := by
          rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  · have := dV.isProb
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure dV.μ
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM x₀)
    have hpt : ∀ y, ptNormSq W n s y ≤ M ^ 2 := fun y => by
      have h1 := Real.sq_sqrt (ptNormSq_nonneg W n s y)
      have h2 := hM y
      nlinarith [Real.sqrt_nonneg (ptNormSq W n s y)]
    have hl2 : sectionL2NormSq W dV n s ≤ M ^ 2 := by
      calc sectionL2NormSq W dV n s ≤ ∫ _ : X, M ^ 2 ∂dV.μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => ptNormSq_nonneg W n s y)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = M ^ 2 := by simp
    calc Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hl2
      _ = M := Real.sqrt_sq hM0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

