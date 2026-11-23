module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZetaProdSphereVolumeBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBound

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

namespace ConstBd

theorem dimN_le (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) ≤ 2 * ((∑ i, j i : ℕ) : ℝ) * n := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).2.2
  have h2 : (dimN n j : ℤ) ≤ 2 * ((∑ i, j i : ℕ) : ℤ) * n := by
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · unfold dimN
      push_cast [Nat.cast_sub h, Finset.sum_filter]
      rfl
    · push_cast; rfl
  exact_mod_cast h2

theorem rpow_le (v x : ℝ) (hv : 3 / 4 ≤ v) (hx : 0 ≤ x) : v ^ (-x) ≤ Real.exp (x / 3) := by
  have hv0 : 0 < v := by linarith
  rw [Real.rpow_def_of_pos hv0]
  apply Real.exp_le_exp.2
  have h1 := Real.one_sub_inv_le_log_of_pos hv0
  have h2 : v⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ hv0 (by norm_num)]; linarith
  nlinarith

theorem inv_sph_le (J : ℕ) (s : ℝ) (hJ : (J : ℝ) ≤ s) (hJ1 : 1 ≤ J) :
    (sphV J)⁻¹ ≤ Real.exp (J * (s / 2 * Real.log s)) := by
  refine (_root_.GlobalTheory.sphV_ratio_and_inv_bounds.2 J).2.trans ?_
  have h1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h0 : (0 : ℝ) < J := by linarith
  rw [← Real.exp_log (pow_pos h0 _), Real.log_pow]
  apply Real.exp_le_exp.2
  have h2 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ J * (s / 2) := by
    have h3 : ((J * (J - 1) / 2 : ℕ) : ℝ) ≤ ((J * (J - 1) : ℕ) : ℝ) / (2 : ℕ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_sub hJ1] at h3
    push_cast at h3
    nlinarith
  have h4 : Real.log J ≤ Real.log s := Real.log_le_log h0 hJ
  have h5 : 0 ≤ Real.log J := Real.log_nonneg h1
  calc _ ≤ (J * (s / 2)) * Real.log s := mul_le_mul h2 h4 h5 (by nlinarith)
    _ = _ := by ring

theorem zeta_prod (E : Type) [Field E] [NumberField E] (J : ℕ) :
    0 ≤ ∏ l ∈ Finset.Icc 2 J, zetaE E l ∧
      ∏ l ∈ Finset.Icc 2 J, zetaE E l ≤ Real.exp (Module.finrank ℚ E) := by
  have h0 : ∀ l ∈ Finset.Icc 2 J, 0 ≤ zetaE E l := fun l hl =>
    zero_le_one.trans (_root_.GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le E l (Finset.mem_Icc.1 hl).1).1
  refine ⟨Finset.prod_nonneg h0, ?_⟩
  refine (Finset.prod_le_prod₀ h0 fun l hl => (_root_.GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le E l (Finset.mem_Icc.1 hl).1).2).trans ?_
  rw [Finset.prod_pow, ← Real.exp_one_pow]
  apply pow_le_pow_left₀ (Finset.prod_nonneg fun l _ => GlobalTheory.ZetaProd.zeta_nonneg l)
  have := GlobalTheory.zetaProd_sphereVolume_bounds.1 J
  have := Real.exp_one_gt_d9
  linarith

theorem numeric (N s L c : ℝ) (hs : 100 ≤ s) (hN : N = s * s) (hL : 15 ≤ L) (hc0 : 0 ≤ c) (hc : c ≤ 2) :
    N / 3 + (c - (N - 2 * s) * (L - (c + 1)) + 3.49 + s / 2 * (L / 2)) + 2 * (3 + N) + 2 + 1 ≤
      -(1 / 2 * N * L) := by
  have h1 : 100 * s ≤ N := by nlinarith
  have h2 : (N - 2 * s) * (c + 1) ≤ N * 3 := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have h3 : 100 * s * L ≤ N * L := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h4 : N * 15 ≤ N * L := mul_le_mul_of_nonneg_left hL (by linarith)
  nlinarith

end ConstBd


set_option maxHeartbeats 1000000 in
open ConstBd in
theorem constantBound : ConstantBound := by
  intro E _ _ _ hE p q a j hj1 hjq hL hq hrd _
  obtain ⟨hdeg, hf1, hv, -⟩ := _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex E hE.1
  obtain ⟨hres0, hres⟩ := _root_.GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow E hE.1
  unfold kapBd
  have haJ : a ≤ ∑ i, j i := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hj1 i)
  have hjJ : ∀ i, j i ≤ ∑ i, j i := fun i =>
    Finset.single_le_sum (f := j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hD := dimN_le (p + q) a j
  have hcast : ((∑ i, j i : ℕ) : ℝ) = ∑ i, (j i : ℝ) := by push_cast; rfl
  generalize hJ : ∑ i, j i = J at *
  have hp : ((p + q : ℕ) : ℝ) = p + q := by push_cast; rfl
  generalize hn : p + q = n at *
  generalize hf : Formalism.HermitianLatticesTheory.fDeg E = f at *
  have hn0 : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num at hL
    · exact_mod_cast h
  have hN : (10000 : ℝ) ≤ n := by
    rw [Real.le_log_iff_exp_le hn0] at hL
    have h1 : Real.exp 15 = Real.exp 1 ^ 15 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
      pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
    norm_num at h2
    linarith
  set s := Real.sqrt n with hs
  have hss : (n : ℝ) = s * s := (Real.mul_self_sqrt hn0.le).symm
  have hs100 : 100 ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hqs : (q : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by exact_mod_cast hq)
  have hJq : (J : ℝ) ≤ q := by exact_mod_cast hjq
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hf0 : (0 : ℝ) ≤ f := Nat.cast_nonneg f
  have haJ' : (a : ℝ) ≤ J := by exact_mod_cast haJ
  have h100 : 100 * s ≤ n := by nlinarith
  have h2J : 2 * J + 2 ≤ n := by
    have : (2 : ℝ) * J + 2 ≤ n := by linarith
    exact_mod_cast this
  have hJp : J ≤ p := by
    have : (J : ℝ) ≤ p := by linarith
    exact_mod_cast this
  have hlogs : Real.log s = Real.log n / 2 := Real.log_sqrt hn0.le
  have hpos : ∀ i, 0 < sphV i := fun i => (_root_.GlobalTheory.sphV_ratio_and_inv_bounds.2 i).1
  have hpi := Real.pi_pos
  have hc0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
  have hc2 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [Real.exp_one_pow]; norm_num
    have := Real.exp_one_gt_d9
    have := Real.pi_lt_d2
    nlinarith

  have T1 : Formalism.HermitianLatticesTheory.vInv E ^ (-((f : ℝ) * dimN n j / 2)) ≤ Real.exp (f * J * (n / 3)) := by
    refine (rpow_le _ _ (by linarith) (by positivity)).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_left (hD (by omega)) hf0
    linarith

  have T2 : (2 : ℝ) ^ (-((f : ℝ) * ((n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) * J - (J : ℝ) ^ 2 + (J : ℝ) / 2 := by nlinarith
    have := mul_nonneg hf0 this
    linarith

  have hA := _root_.GlobalTheory.SphRatio.log_sphV_ratio_le n p J (by exact_mod_cast (by linarith : (18 : ℝ) ≤ n)) hJp (by omega)
    (by linarith) (by linarith)
  rw [Real.log_div hn0.ne' (by positivity), Real.log_mul (x := 2 * Real.pi) (by positivity) (by positivity),
    Real.log_exp,
    Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hA
  have hB := _root_.GlobalTheory.sphV_ratio_and_inv_bounds.1 q J hjq
  rw [Real.log_le_iff_le_exp (div_pos (hpos _) (hpos _))] at hB
  have hC : (∏ i, sphV (j i))⁻¹ ≤ Real.exp (J * (s / 2 * (Real.log n / 2))) := by
    rw [← Finset.prod_inv_distrib, hcast, Finset.sum_mul, Real.exp_sum, ← hlogs]
    apply Finset.prod_le_prod₀ (fun i _ => (inv_pos.2 (hpos _)).le)
    intro i _
    apply inv_sph_le _ _ _ (hj1 i)
    have : (j i : ℝ) ≤ J := by exact_mod_cast hjJ i
    linarith
  have hP : 0 < ∏ i, sphV (j i) := Finset.prod_pos fun i _ => hpos _
  have T3 : (sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i))) ^ f ≤
      Real.exp (f * J * (Real.log (2 * Real.pi) - (n - 2 * s) * (Real.log n - (Real.log (2 * Real.pi) + 1)) +
        3.49 + s / 2 * (Real.log n / 2))) := by
    rw [mul_assoc (f : ℝ), Real.exp_nat_mul]
    have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
    apply pow_le_pow_left₀ (by positivity)
    have e : sphV p * sphV q / (sphV (p - J) * sphV (q - J) * ∏ i, sphV (j i)) =
        sphV p / sphV (p - J) * (sphV q / sphV (q - J)) * (∏ i, sphV (j i))⁻¹ := by
      field_simp
    rw [e]
    refine (mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC (by positivity)
      (by positivity)).trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

  have T4 : dedekindZeta_residue E ^ a ≤ Real.exp (f * J * (2 * (3 + n))) := by
    have h16 : (16 : ℝ) ≤ Real.exp 3 := by
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [Real.exp_one_pow]; norm_num
      have h2 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) _
      norm_num at h2
      linarith
    have hl0 : 0 ≤ Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) := Real.log_nonneg (by linarith)
    have h3 : 16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv E) ≤ Real.exp (3 + n) := by
      rw [Real.exp_add]
      exact mul_le_mul h16 hrd hl0 (by positivity)
    have h4 := hres.trans (pow_le_pow_left₀ (by positivity) h3 _)
    refine (pow_le_pow_left₀ hres0.le h4 a).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    have : (a : ℝ) * (2 * f * (3 + n)) ≤ J * (2 * f * (3 + n)) :=
      mul_le_mul_of_nonneg_right haJ' (by positivity)
    linarith

  have T5 : ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l ≤ Real.exp (f * J * 2) := by
    refine (Finset.prod_le_prod₀ (fun i _ => (zeta_prod E (j i)).1)
      (fun i _ => (zeta_prod E (j i)).2)).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul, hdeg]
    apply Real.exp_le_exp.2
    push_cast
    have := mul_le_mul_of_nonneg_right haJ' hf0
    linarith
  have T5' : 0 ≤ ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l :=
    Finset.prod_nonneg fun i _ => (zeta_prod E (j i)).1

  obtain ⟨hL1, hL0⟩ := _root_.GlobalTheory.FlagMeas.LProd.neg_log_prod_le E hE (n - 2 * J) n (by omega)
  rw [hf] at hL1
  have FreeQuotientRank : (∏ M ∈ Finset.Ioc (n - 2 * J) n, Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ ≤ Real.exp (f * J * 1) := by
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp
    · rw [← Real.log_le_iff_le_exp (inv_pos.2 hL0), Real.log_inv]
      refine hL1.trans ?_
      have h1 : (2 : ℝ) ^ ((1 : ℤ) - (n - 2 * J : ℕ)) ≤ 1 :=
        zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      have h2 : (1 : ℝ) ≤ J := by exact_mod_cast h
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (h1.trans h2) hf0
  have hv0 : 0 < Formalism.HermitianLatticesTheory.vInv E := by linarith
  have := hpos p; have := hpos q; have := hpos (p - J); have := hpos (q - J)
  rw [div_eq_mul_inv]
  refine (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul T1 T2 (by positivity) (by positivity))
    T3 (by positivity) (by positivity)) T4 (by positivity) (by positivity)) T5 T5' (by positivity)) FreeQuotientRank
    (by positivity) (by positivity)).trans ?_
  rw [mul_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left (numeric n s _ _ hs100 hss hL hc0 hc2) (mul_nonneg hf0 hJ0)
  linarith

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.FrameDual

section Det

variable {A : Type} [CommRing A]

end Det

section Ideals

variable {E : Type} [Field E] [NumberField E]

def Stab (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) : Prop := ∀ x ∈ I, σ x ∈ I

theorem stab_one (σ : E →+* E) : Stab σ 1 := by
  intro x hx
  obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  exact (FractionalIdeal.mem_one_iff _).2 ⟨RingOfIntegers.mapRingHom σ d, rfl⟩

theorem Stab.mul {σ : E →+* E} {I J : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (hJ : Stab σ J) :
    Stab σ (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hI i hi) (hJ j hj)
  · rw [map_add (f := _)]; exact Submodule.add_mem (I * J).coeToSubmodule ha hb

theorem Stab.pow {σ : E →+* E} {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I) (j : ℕ) :
    Stab σ (I ^ j) := by
  induction j with
  | zero => simpa using stab_one σ
  | succ j ih => rw [pow_succ]; exact ih.mul hI

theorem Stab.inv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : Stab σ I)
    (h0 : I ≠ 0) : Stab σ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at hx ⊢
  intro y hy
  have := stab_one σ _ (hx _ (hI y hy))
  rwa [map_mul, hσ] at this

theorem diff_ne_zero : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem dInv_ne_zero (j : ℕ) : dInv E j ≠ 0 := pow_ne_zero _ (inv_ne_zero diff_ne_zero)

theorem stab_dInv {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (j : ℕ) : Stab σ (dInv E j) := by
  refine Stab.pow ?_ j
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  intro x hx
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h10] at hx ⊢
  intro a ha
  have h1 := hx _ (stab_one σ a ha)
  let e : E ≃ₐ[ℚ] E := AlgEquiv.ofBijective σ.toRatAlgHom (Function.Involutive.bijective hσ)
  have h2 : Algebra.traceForm ℚ E (σ x) a = Algebra.traceForm ℚ E x (σ a) := by
    rw [Algebra.traceForm_apply, Algebra.traceForm_apply, ← Algebra.trace_eq_of_algEquiv e (x * σ a)]
    congr 1
    change _ = σ (x * σ a)
    rw [map_mul, hσ]
  rwa [h2]

end Ideals

section Frame

variable {E : Type} [Field E] [NumberField E]

theorem frameDualTupleIdeals_castAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.castAdd r b.castSucc) = dInv E (r - b) := by
  simp [id1]

theorem frameDualTupleIdeals_natAdd (r : ℕ) (b : Fin r) : id1 E r (Fin.natAdd (r + 1) b) = (dInv E (r - b))⁻¹ := by
  simp [id1]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem natAbs_discr_sq (h2 : Module.finrank F E = 2) [Algebra.FormallyUnramified (𝓞 F) (𝓞 E)] :
    (discr E).natAbs = (discr F).natAbs ^ 2 := by
  have h0 : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact not_dvd_differentIdeal_iff.2 (inferInstance : Algebra.IsUnramifiedAt (𝓞 F) P)
      (Ideal.dvd_iff_le.2 hle)
  have h1 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rwa [h0, Ideal.absNorm_top, one_mul, h2] at h1

theorem absNorm_dInv (j : ℕ) :
    ((FractionalIdeal.absNorm (dInv E j) : ℚ) : ℝ) = |(discr E : ℝ)|⁻¹ ^ j := by
  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E (𝓞 E)]
  simp

end Frame

end GlobalTheory.SnMass.FrameDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralDiscreteSeriesUnipotentVanishes
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma eq_zero_of_sum_star_mul_const_mul_eq_zero {n : ℕ} (x : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : ∑ i, star (x i) * (c * x i) = 0) : x = 0 := by
  have h1 : c * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) = 0 := by
    rw [← h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Complex.normSq (x i) : ℂ) = star (x i) * x i := Complex.normSq_eq_conj_mul_self
    rw [e]; ring
  have h2 : ∑ i, Complex.normSq (x i) = 0 := by
    have h3 := (mul_eq_zero.mp h1).resolve_left hc
    exact_mod_cast h3
  funext i
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h2 i
    (Finset.mem_univ i)
  simpa using h4

theorem one_le_rkR_of_isIsoC {n : ℕ} {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} (hW : IsIsoC ε W) :
    1 ≤ rkR ε := by
  unfold IsIsoC herm Jm at hW
  obtain ⟨hne, hiso⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq := hiso x hxW x hxW

  have hall : ∀ b : Bool, ∃ i, ε i = b := by
    intro b
    by_contra hno
    push_neg at hno
    have hb : ∀ i, ε i = !b := fun i => by
      have h' := hno i
      cases hε : ε i <;> cases b <;> simp_all
    apply hx0
    apply eq_zero_of_sum_star_mul_const_mul_eq_zero x (if (!b) = true then (1 : ℂ) else -1) (by split_ifs <;> norm_num)
    rw [← hq]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hb]
  obtain ⟨i, hi⟩ := hall true
  obtain ⟨j, hj⟩ := hall false
  unfold rkR
  apply le_min
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem decE_le_exp {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    decE q h t ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * t)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  unfold decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsd] at hs hs1 ⊢
  have hs0 : s ≠ 0 := hs.ne'

  have key : t / s - min (2 * t ^ 2) (t / s) ≤ 1 := by
    rcases le_total (2 * t ^ 2) (t / s) with h' | h'
    · rw [min_eq_left h']
      obtain ⟨u, hu⟩ : ∃ u, u = t / s := ⟨_, rfl⟩
      rw [← hu]
      have ht : t = u * s := by rw [hu]; field_simp
      have h2 : t ^ 2 = u ^ 2 * s ^ 2 := by rw [ht]; ring
      have h1 : 0 ≤ u ^ 2 * (s ^ 2 - 1) := mul_nonneg (sq_nonneg u) (by nlinarith)
      nlinarith [sq_nonneg (u - 1 / 4)]
    · rw [min_eq_right h']; norm_num
  have e : h / (8 * s) * t = h / 8 * (t / s) := by ring
  rw [e]
  nlinarith [mul_nonneg hh (sub_nonneg.mpr key)]

theorem rate_lt {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {h : ℝ}
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    0 ≤ h ∧ 12 * (n : ℝ) * q < h / (8 * Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hh
  have hP : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

private lemma list_prod_eq_take_mul_pair_mul_drop {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (v : ι) :
    ∏ u, F u = F v * ∏ u ∈ Finset.univ.erase v, F u :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

private lemma rkR_le' {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  unfold rkR
  calc min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card
      ≤ (Finset.univ.filter fun a => ε a = true).card := min_le_left _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem integral_phe_eq_zero : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  classical
  intro hS B d h hD hL hh v Wv hW ν hν x y
  obtain ⟨hHC, hDS, hLow, hFd⟩ := hD v
  have hDS' := hDS
  obtain ⟨_, _, hU, _⟩ := hDS'
  obtain ⟨hw1, hwS⟩ := hLow
  have hq1 : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn1 : 1 ≤ B.I.n := le_trans hq1 (rkR_le' _)
  obtain ⟨h0, hc⟩ := rate_lt hn1 hq1 (hh v)

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU
    (hS B.I.n (B.I.ε v) (B.lam v) hHC (B.H v) (B.σ v) hDS).1

  have hT := _root_.GlobalTheory.ConstTermZero.constant_term_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v) : ℝ))) α (B.w v) hU hFd hc hw1 hαs hαc
    (fun u => hαfix (B.w v) hwS u)
    ⟨Real.exp (h / 8), fun g => (hL v g).trans (decE_le_exp hq1 h0 _)⟩ (x.1 v) (y.1 v)
  have hstar : ∫ m, star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν = 0 := by
    refine (integral_conj (μ := ν)
      (f := fun m => ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ)).trans ?_
    rw [hT]; simp

  have hfun : ∀ m : UJ (B.I.ε v),
      phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
        ((((∏ u, d u : ℝ) : ℂ) * star (∏ u ∈ Finset.univ.erase v,
          ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ)) * B.e (x.2 * y.2)) *
        star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    have hrest : ∏ u ∈ Finset.univ.erase v,
        ⟪B.w u, B.σ u (uMat (x.1 u * (open Classical in (Pi.mulSingle v m : B.I.Ginf)) u * y.1 u)) (B.w u)⟫_ℂ =
        ∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ :=
      Finset.prod_congr rfl fun u hu => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]
    simp only [GlobalTheory.Count.phe, GlobalTheory.Count.ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [list_prod_eq_take_mul_pair_mul_drop _ v, hrest, Pi.mulSingle_eq_same, star_mul']
    ring
  refine (integral_congr_ae (ae_of_all ν hfun)).trans ?_
  rw [integral_const_mul, hstar, mul_zero]

end GlobalTheory.RealFibre
end

