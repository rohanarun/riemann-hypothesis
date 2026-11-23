module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0197
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CMEqZeroOfNe
section
open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent

section Algebra

variable {F : Type} [Field F] {n : ℕ}

theorem cM_eq_zero_of_ne {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n}
    (h : ¬ ((j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1)) : cM n k x i j = 0 := by
  simp only [cM, Matrix.of_apply]
  rw [dite_eq_right h]

theorem cM_eq_of {k : ℕ} (x : Fin (k + 1) → F) {i j : Fin n} (hj : (j : ℕ) = k + 1)
    (hi : (i : ℕ) < k + 1) : cM n k x i j = x ⟨i, hi⟩ := by
  simp only [cM, Matrix.of_apply]
  rw [dite_eq_left ⟨hj, hi⟩]

theorem col_val (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cM n k x := rfl

theorem col_inv_val (k : ℕ) (x : Fin (k + 1) → F) :
    (((col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 - cM n k x := rfl

theorem col_mem (k : ℕ) (x : Fin (k + 1) → F) : col n k x ∈ unipotent F n := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : (j : ℕ) < i := hij
    rw [col_val, Matrix.add_apply, Matrix.one_apply_ne (by intro e; subst e; omega),
      cM_eq_zero_of_ne x (by omega), add_zero]
  · rw [col_val, Matrix.add_apply, Matrix.one_apply_eq, cM_eq_zero_of_ne x (by omega), add_zero]

theorem superdiagSum_cM {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.superdiagSum (cM n k x) = x (Fin.last k) := by
  unfold Whittaker.superdiagSum
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin n), Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
  · rw [if_pos rfl, cM_eq_of x rfl (by simp)]
    rfl
  · intro j _ hj
    rw [if_neg]
    intro e
    exact hj (Fin.ext (by simpa using e))
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h
    · refine cM_eq_zero_of_ne x fun h' => hi (Fin.ext ?_)
      simp only
      omega
    · rfl
  · simp

theorem psiN_col (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k)) := by
  rw [Whittaker.psiN, col_val, Whittaker.superdiagSum_add, Whittaker.superdiagSum_one, zero_add,
    superdiagSum_cM hk]

theorem mul_cM {k : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ i j : Fin n, (j : ℕ) ≤ k → M i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (x : Fin (k + 1) → F) : M * cM n k x = cM n k x := by
  have h : M * cM n k x = 1 * cM n k x := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ k
    · rw [hM i l hl]
    · rw [cM_eq_zero_of_ne x (i := l) (j := j) (by omega), mul_zero, mul_zero]
  rw [h, one_mul]

theorem conj_expand {M C : Matrix (Fin n) (Fin n) F} (hMC : M * C = C) (hCC : C * C = 0) :
    (1 + C) * M * (1 - C) = M + C * M - C := by
  calc (1 + C) * M * (1 - C) = M + C * M - M * C - C * (M * C) := by noncomm_ring
    _ = M + C * M - C := by rw [hMC, hCC, sub_zero]

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_split (ψ : AddChar F ℂ) {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inU k g) :
    ∃ (g' : GL (Fin n) F) (x : Fin (k + 1) → F), inU (k + 1) g' ∧ g = g' * col n k x ∧
      Whittaker.psiN ψ g = Whittaker.psiN ψ g' * ψ (x (Fin.last k)) := by
  obtain ⟨hu, hc⟩ := hg
  let x : Fin (k + 1) → F := fun i => (g : Matrix (Fin n) (Fin n) F) ⟨i, by omega⟩ ⟨k + 1, hk⟩
  have hv : ((g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, col_inv_val, mul_sub, mul_one, mul_cM hc]
  have hm : g * (col n k x)⁻¹ ∈ unipotent F n :=
    (unipotent F n).mul_mem hu ((unipotent F n).inv_mem (col_mem k x))
  refine ⟨g * (col n k x)⁻¹, x, ⟨hm, fun i j hj => ?_⟩, (inv_mul_cancel_right _ _).symm, ?_⟩
  · rw [hv, Matrix.sub_apply]
    by_cases hjk : (j : ℕ) ≤ k
    · rw [cM_eq_zero_of_ne x (by omega), sub_zero, hc i j hjk]
    · have hj' : (j : ℕ) = k + 1 := by omega
      by_cases hi : (i : ℕ) < k + 1
      · have hx : x ⟨i, hi⟩ = (g : Matrix (Fin n) (Fin n) F) i j := by
          have e : j = ⟨k + 1, hk⟩ := Fin.ext hj'
          subst e
          rfl
        rw [cM_eq_of x hj' hi, hx, sub_self, Matrix.one_apply_ne (by intro e; subst e; omega)]
      · rw [cM_eq_zero_of_ne x (by omega), sub_zero]
        by_cases e : i = j
        · subst e
          rw [hu.2, Matrix.one_apply_eq]
        · have hlt : id j < id i := by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun h => e (Fin.ext h)
              omega
            exact this
          rw [hu.1 hlt, Matrix.one_apply_ne e]
  · have h : Whittaker.psiN ψ g = Whittaker.psiN ψ (g * (col n k x)⁻¹ * col n k x) := by
      rw [inv_mul_cancel_right]
    rw [h, Whittaker.psiN_mul ψ hm (col_mem k x), psiN_col ψ hk]

theorem inU_conj (ψ : AddChar F ℂ) {k : ℕ} (g : GL (Fin n) F) (hg : inU (k + 1) g)
    (x : Fin (k + 1) → F) :
    ∃ g' : GL (Fin n) F, inU (k + 1) g' ∧ col n k x * g = g' * col n k x ∧
      Whittaker.psiN ψ g' = Whittaker.psiN ψ g := by
  obtain ⟨hu, hc⟩ := hg
  have hcol : col n k x ∈ unipotent F n := col_mem k x
  have hcg := (unipotent F n).mul_mem hcol hu
  have hinv := (unipotent F n).inv_mem hcol
  have hv : ((col n k x * g * (col n k x)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F) + cM n k x * (g : Matrix (Fin n) (Fin n) F) - cM n k x := by
    rw [Units.val_mul, Units.val_mul, col_val, col_inv_val]
    exact conj_expand (mul_cM (fun i j hj => hc i j (by omega)) x) (cM_mul k x x)
  refine ⟨col n k x * g * (col n k x)⁻¹, ⟨(unipotent F n).mul_mem hcg hinv, fun i j hj => ?_⟩,
    (inv_mul_cancel_right _ _).symm, ?_⟩
  · have hC : (cM n k x * (g : Matrix (Fin n) (Fin n) F)) i j = cM n k x i j := by
      rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => by rw [hc l j hj], ← Matrix.mul_apply,
        mul_one]
    rw [hv, Matrix.sub_apply, Matrix.add_apply, hC, hc i j hj, add_sub_cancel_right]
  · have h0 := Whittaker.psiN_ne_zero ψ (col n k x)
    rw [Whittaker.psiN_mul ψ hcg hinv, Whittaker.psiN_mul ψ hcol hu, Whittaker.psiN_inv ψ hcol]
    field_simp

end Local

theorem main : ColumnsUnipotent := by
  intro F _ _ _ _ _ _ μ _ ψ _ n k hk
  exact ⟨fun g hg => inU_split ψ hk g hg, fun g hg x => inU_conj ψ g hg x⟩

end GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem sk_skew {n : ℕ} (p : Ix n) : (sk p)ᴴ = -sk p := by
  obtain ⟨b, i, j⟩ := p
  have hc : ∀ (a b : Fin n) (c : ℂ), (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
    intro a b c
    ext x y
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]
  cases b
  · simp [sk, Matrix.conjTranspose_add, hc, Matrix.single_neg, add_comm]
  · simp [sk, Matrix.conjTranspose_sub, hc]

theorem Rd_Rd_of_act {n : ℕ} (E : KMod n) (Y : Mat n) (B : E.V →L[ℂ] E.V)
    (hB : ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) (f : Mat n → E.V) (hf : f ∈ CE E)
    (g : Mat n) (hg : g ∈ GLs n) : Rd Y (Rd Y f) g = B (B (f g)) := by
  have hnhds : GLs n ∈ nhds g := isOpen_GLs.mem_nhds hg
  have hev : Rd Y f =ᶠ[nhds g] (B.restrictScalars ℝ) ∘ f := by
    filter_upwards [hnhds] with y hy
    simpa using hB f hf y hy
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt hnhds).differentiableAt (by simp)
  have hfd : fderiv ℝ (Rd Y f) g = (B.restrictScalars ℝ).comp (fderiv ℝ f g) := by
    rw [hev.fderiv_eq]
    exact ((B.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have h1 : Rd Y (Rd Y f) g = B (Rd Y f g) := by
    change fderiv ℝ (Rd Y f) g (g * Y) = B (fderiv ℝ f g (g * Y))
    rw [hfd]
    rfl
  rw [h1, hB f hf g hg]

theorem om_section {n : ℕ} (E : KMod n) : ∃ A : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g) := by
  choose B hB using fun p : Ix n => rd_skew_eq_const E (sk p) (sk_skew p)
  refine ⟨-(1 / 4 : ℂ) • ∑ p, B p * B p, fun f hf g hg => ?_⟩
  rw [OmDec.Om_eq_squares f hf.1 g hg, sub_eq_add_neg]
  congr 1
  have h : ∀ p, Rd (sk p) (Rd (sk p) f) g = B p (B p (f g)) := fun p =>
    Rd_Rd_of_act E (sk p) (B p) (hB p) f hf g hg
  simp only [h, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.neg_apply, neg_smul]
  rfl

end GlobalTheory.CompanionTheory.WaveSpd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffEqPowOfMulOneSub
section
open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

open PowerSeries Filter _root_.Topology

theorem tendsto_coeff_mul_one_sub (G : ℂ⟦X⟧) (b : ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * (1 - C b * X))) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : ∀ j : ℕ, coeff (j + 1) (G * (1 - C b * X)) = coeff (j + 1) G - b * coeff j G := by
    intro j
    have : G * (1 - C b * X) = G - C b * (G * X) := by ring
    rw [this, map_sub, coeff_C_mul, coeff_succ_mul_X]
  simp only [e]
  have h1 := (tendsto_add_atTop_iff_nat 1).2 h
  simpa using h1.sub (h.const_mul b)

theorem tendsto_coeff_mul_prod (G : ℂ⟦X⟧) {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * ∏ k ∈ s, (1 - C (β k) * X))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : G * ((1 - C (β a) * X) * ∏ k ∈ s, (1 - C (β k) * X)) =
        (G * ∏ k ∈ s, (1 - C (β k) * X)) * (1 - C (β a) * X) := by ring
    rw [this]
    exact tendsto_coeff_mul_one_sub _ _ ih

theorem coeff_eq_pow_of_mul_one_sub (H : ℂ⟦X⟧) (b : ℂ) (h : H * (1 - C b * X) = 1) (j : ℕ) :
    coeff j H = b ^ j := by
  have e : H = 1 + C b * (H * X) := by
    calc H = H * (1 - C b * X) + C b * (H * X) := by ring
      _ = 1 + C b * (H * X) := by rw [h]
  induction j with
  | zero =>
    rw [e]; simp
  | succ j ih =>
    rw [e, map_add (f := _), coeff_C_mul, coeff_succ_mul_X, ih, pow_succ]
    simp [coeff_one, mul_comm]

theorem coeff_prod_one_sub {n : ℕ} (β : Fin n → ℂ) (r : ℕ) :
    coeff r (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) =
      (-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i := by
  classical
  have e : ∀ t : Finset (Fin n), ∏ i ∈ t, (-(C (β i) * X) : ℂ⟦X⟧) =
      C ((-1) ^ t.card * ∏ i ∈ t, β i) * X ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
  have e2 : (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) = ∏ i, (1 + -(C (β i) * X)) := by
    simp only [sub_eq_add_neg]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : r = t.card
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

theorem mk_mul_prod_eq_one {n : ℕ} (β : Fin n → ℂ) (g : ℕ → ℂ) (h0 : g 0 = 1)
    (hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
      ((-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i) * g (j - r) = 0) :
    (PowerSeries.mk g : ℂ⟦X⟧) * ∏ i, (1 - C (β i) * X) = 1 := by
  ext j
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_sub, coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0, coeff_one]
  · rw [hrec j hj, coeff_one, if_neg (by omega)]

end GlobalTheory.CompanionTheory.SatakeBound

theorem GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton := by
  intro n β g h0 hrec hg i
  classical
  have hG := GlobalTheory.CompanionTheory.SatakeBound.mk_mul_prod_eq_one β g h0 hrec
  have hc : Filter.Tendsto (fun j => PowerSeries.coeff j (PowerSeries.mk g : PowerSeries ℂ))
      Filter.atTop (nhds 0) := by
    simpa [PowerSeries.coeff_mk] using hg
  have hH := GlobalTheory.CompanionTheory.SatakeBound.tendsto_coeff_mul_prod _ (Finset.univ.erase i) β hc
  have hone : ((PowerSeries.mk g : PowerSeries ℂ) *
      ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) *
      (1 - PowerSeries.C (β i) * PowerSeries.X) = 1 := by
    have hs := Finset.mul_prod_erase Finset.univ
      (fun k => (1 - PowerSeries.C (β k) * PowerSeries.X : PowerSeries ℂ)) (Finset.mem_univ i)
    calc _ = (PowerSeries.mk g : PowerSeries ℂ) * ((1 - PowerSeries.C (β i) * PowerSeries.X) *
          ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) := by ring
      _ = 1 := by rw [hs, hG]
  have hp := GlobalTheory.CompanionTheory.SatakeBound.coeff_eq_pow_of_mul_one_sub _ _ hone
  simp only [hp] at hH
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 hH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageHermitianPositive
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.JSBoundStep

theorem column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive := by
  intro h0 h3 h3c
  unfold FormHermitianPositive ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm l k B B' hk hW hI hC
  unfold L0 ForF at h0
  unfold L3 ForR ForF at h3
  unfold ColumnsMirabolic ForF at h3c
  obtain ⟨-, hlat⟩ := h0 F μ ψ hψ
  obtain ⟨hlatM, hcv⟩ := hlat (k + 1)
  have h3' := h3 F μ ψ hψ n V ρ hsm
  obtain ⟨hcadd, hc0, hcP, -, -, -⟩ := h3c F μ ψ hψ n k hk
  obtain ⟨herm, psd, null, quasi, -⟩ := hI
  clear h0 h3 h3c hlat
  have hψinv : ∀ t : F, ψ (-t) * ψ t = 1 := fun t => by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hψconj : ∀ t : F, conj (ψ (-t)) = ψ t := by
    intro t
    have hn : ‖ψ (-t)‖ = 1 := hψ.2.2 (-t)
    calc conj (ψ (-t)) = conj (ψ (-t)) * (ψ (-t) * ψ t) := by rw [hψinv, mul_one]
      _ = (conj (ψ (-t)) * ψ (-t)) * ψ t := by ring
      _ = ψ t := by rw [Complex.conj_mul', hn]; simp
  have hinv : ∀ (x : Fin (k + 1) → F) (b : V),
      ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) = b := by
    intro x b
    have h1 : PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x) = 1 := by
      rw [← hcadd, add_neg_cancel, hc0]
    calc ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
        = (ρ (PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x))) b := by rw [map_mul]; rfl
      _ = b := by rw [h1, map_one]; rfl
  have hB : ∀ (x : Fin (k + 1) → F) (a b : V),
      B (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a) b = B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) := by
    intro x a b
    have hq := quasi (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).1 a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
    rw [hinv, (hcP x).2.2.1, map_one] at hq
    simpa using hq

  have hnegS : ∀ (M : ℕ), ∀ x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, -x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
    intro M x hx
    simp only [PositivityTheory.JacquetShalikaLocal.lat, Set.mem_setOf_eq, Pi.neg_apply, mul_neg] at hx ⊢
    exact fun i => neg_mem (hx i)
  have hvol : ∀ M : ℕ, 0 < (Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) :=
    fun M => (hlatM M).2.2.2
  have hmeas : ∀ M : ℕ, MeasurableSet (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) := fun M => (hlatM M).2.2.1
  have hvol' : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)
      = (((Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) : ℝ) : ℂ) := by
    intro M
    rw [setIntegral_const]
    simp
  have hv : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) ≠ 0 := by
    intro M
    rw [hvol' M]
    exact Complex.ofReal_ne_zero.mpr (hvol M).ne'
  have hmv : ∀ x : Fin (k + 1) → F,
      (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x = -x := by
    intro x
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hcvS : ∀ (M : ℕ) (f : (Fin (k + 1) → F) → ℂ),
      ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f (-x) ∂(Measure.pi fun _ => μ)
        = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f x ∂(Measure.pi fun _ => μ) := by
    intro M f
    have himg : (fun x => (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x)
        '' PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M = PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [hmv]
        exact hnegS M y hy
      · intro hx
        exact ⟨-x, hnegS M x hx, by simp only [hmv, neg_neg]⟩
    have e1 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) (fun _ => (1 : ℂ)) (hmeas M)
    have e2 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) f (hmeas M)
    rw [himg] at e1 e2
    simp only [hmv] at e2
    have alg : ∀ c v I J : ℂ, v ≠ 0 → v = c * v → I = c * J → J = I := by
      intro c v I J hv0 h1 h2
      have hc : c = 1 := by
        have : c * v = 1 * v := by rw [← h1, one_mul]
        exact mul_right_cancel₀ hv0 this
      rw [h2, hc, one_mul]
    exact alg _ _ _ _ (hv M) e1 e2

  have hξ : ∀ x : Fin (k + 1) → F, Pi.single (Fin.last k) (1 : F) ⬝ᵥ x = x (Fin.last k) := by
    intro x
    simp [dotProduct, Pi.single_apply]
  choose P hP1 hP2 using fun (M : ℕ) (u : V) => h3' k M (Pi.single (Fin.last k) (1 : F)) u
  simp only [hξ] at hP1 hP2
  have hSA : ∀ (M : ℕ) (a b : V), B (P M a) b = B a (P M b) := by
    intro M a b
    calc B (P M a) b = conj (B b (P M a)) := (herm b (P M a)).symm
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            conj (ψ (-x (Fin.last k)) * B b (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a)) ∂(Measure.pi fun _ => μ) := by
          rw [hP1 M a (B b), integral_conj]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-(-x) (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) ∂(Measure.pi fun _ => μ) := by
          congr 1
          funext x
          rw [map_mul, hψconj, herm, hB x a b]
          simp only [Pi.neg_apply, neg_neg]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b) ∂(Measure.pi fun _ => μ) :=
          hcvS M (fun x => ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b))
      _ = B a (P M b) := (hP1 M b (B a)).symm
  have hE : ∀ (M : ℕ) (u v : V),
      (∀ y ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ρ (PositivityTheory.JacquetShalikaLocal.col n k y) v = ψ (y (Fin.last k)) • v) →
      B u (P M v) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u v := by
    intro M u v hv0
    rw [hP1 M v (B u), ← integral_mul_const]
    refine setIntegral_congr_fun (hmeas M) ?_
    intro x hx
    beta_reduce
    rw [hv0 x hx, map_smul, smul_eq_mul, ← mul_assoc, hψinv]
  have hL : ∀ (M : ℕ) (u : V),
      l (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * l u := by
    intro M u
    rw [hP1 M u l, ← integral_mul_const]
    congr 1
    funext x
    rw [hW (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).2.1.1 u, (hcP x).2.2.2, ← mul_assoc, hψinv]
  have hrel : ∀ (M : ℕ) (u : V), B (P M u) (P M u)
      = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u (P M u) := by
    intro M u
    rw [hSA M u (P M u), hE M u (P M u) (hP2 M u)]
  have hchar : ∀ u u' : V, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u = B u' (P M u) := by
    intro u u'
    obtain ⟨M₀, h⟩ := hC u u'
    exact ⟨M₀, fun M hM => by rw [h M hM, hP1 M u (B u')]⟩
  refine ⟨fun u u' => ?_, fun u => ?_, fun u hu => ?_⟩
  · obtain ⟨M1, h1⟩ := hchar u u'
    obtain ⟨M2, h2⟩ := hchar u' u
    rw [h2 (max M1 M2) (le_max_right _ _), h1 (max M1 M2) (le_max_left _ _), herm, hSA]
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl]
    have hp := psd (P M1 u)
    rw [hrel M1 u, hvol' M1, Complex.re_ofReal_mul] at hp
    exact (mul_nonneg_iff_of_pos_left (hvol M1)).mp hp
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl] at hu
    have h0' : B (P M1 u) (P M1 u) = 0 := by rw [hrel, hu, mul_zero]
    have hl0 := null (P M1 u) h0'
    rw [hL M1 u] at hl0
    exact (mul_eq_zero.mp hl0).resolve_left (hv M1)

end GlobalTheory.CompanionTheory.JSBoundStep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_action_formula : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm → GlobalTheory.CompanionTheory.KerFc.ActFormula := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.actFormula | exact GlobalTheory.CompanionTheory.KerFc.actFormula | (intros; apply GlobalTheory.CompanionTheory.KerFc.actFormula <;> assumption)
end

