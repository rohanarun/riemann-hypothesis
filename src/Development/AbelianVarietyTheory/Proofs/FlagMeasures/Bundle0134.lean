module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundled
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CountBridge

theorem fdegOf_eq_of_isFdeg {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure (Formalism.REAL.UJ ε))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) (hd : IsFdeg μ σ d) (w : H) (hw : ‖w‖ = 1) :
    fdegOf μ σ w = d := by
  obtain ⟨hpos, h⟩ := hd
  have h2 := (h w w w w).2
  have h3 : (fun g => coefOn (ε := ε) σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn (ε := ε) σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h3, integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h2
  have h4 : ∫ g, ‖coefOn (ε := ε) σ w w g‖ ^ 2 ∂μ = 1 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  unfold fdegOf
  rw [h4, hw]
  simp

theorem le_exp_of_log_le {x y : ℝ} (h : Real.log x ≤ y) : x ≤ Real.exp y :=
  (Real.le_exp_log x).trans (Real.exp_le_exp.mpr h)

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  apply Real.one_le_rpow
  · have h : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (discr_ne_zero I.E)
    exact_mod_cast h
  · positivity

theorem count_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  intro hT A
  obtain ⟨n₀, hn₀⟩ := hT A
  refine ⟨n₀, max 0 (8 * 10 ^ 14 * (A + 4)), le_max_left _ _, ?_⟩
  intro n₁ hn₁ C hC I b lam g g₀ e H _ _ _ σ w Hs _ _ _ σs tens μf _ fund R Re h
    ⟨hn, ⟨p, q, hpq, hq⟩, hb, hrd, hHC, hlam, hadm, hg, hgb, hpr, hg₀, hsplit⟩
    ⟨hDS, hlow, htens, hhaar, hfund, hR, hRe⟩ hgap hh hf hbb
  let B : RowsAut :=
    { I := I, μf := μf, haar := hhaar, fund := fund, fund_spec := hfund, lam := lam, H := H, σ := σ,
      w := w, Hs := Hs, σs := σs, tens := tens, tens_spec := htens, R := R, R_spec := hR, g := g,
      g₀ := g₀, e := e, e_adm := hadm, Re := Re, Re_spec := hRe }
  have hfd : ∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) := by
    intro v
    obtain ⟨_, hnt, hU, hirr, hsq, -⟩ := hDS v
    obtain ⟨d, hd⟩ := GlobalTheory.schur_orthogonality_unitary I.n (I.ε v) (H v) (σ v) hU hirr hsq
    rw [fdegOf_eq_of_isFdeg _ _ d hd _ (hlow v).1]
    exact hd
  have hlog : 0 ≤ Real.log (b * I.rd) := by
    apply Real.log_nonneg
    have := one_le_rd I
    nlinarith
  have hC' : 8 * 10 ^ 14 * (A + 4) ≤ C := (le_max_right _ _).trans hC
  have hH : GlobalTheory.Count.CountHyp B A n₀ (fun v => fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) p q b := by
    refine ⟨fun v => ⟨hHC v, hDS v, hlow v, hfd v⟩, hpq, le_trans hn₁ hn, hq, le_exp_of_log_le hrd, hf, hb,
      le_exp_of_log_le hbb, hlam, hg, hgb, hpr, hg₀, _root_.GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E g₀ hpr hsplit, ?_⟩
    intro v a a' haa
    refine le_trans ?_ (hgap v a a' haa)
    refine le_trans ?_ hh
    show 8 * 10 ^ 14 * (A + 4) * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ _
    gcongr
  have hres := (hn₀ B _ p q b hH).2
  have he : -(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) =
      -(1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) := by ring
  rw [he]
  exact hres

end GlobalTheory.CountBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WhittakerTermEqZero
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.NonOpenCell

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_val (σ : Equiv.Perm (Fin n)) :
    ((pm g σ : Gn g n) : Mt g n) = fun r j : Fin n => if r = σ j then 1 else 0 := by
  have h : IsUnit (show Mt g n from fun r j : Fin n => if r = σ j then 1 else 0) := by
    refine IsUnit.of_mul_eq_one (show Mt g n from fun r j : Fin n => if j = σ r then 1 else 0) ?_
    ext r c
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm r)]
    · simp [Matrix.one_apply, eq_comm]
    · intro k _ hk
      have : r ≠ σ k := fun h => hk (by simp [h])
      simp [this]
    · simp
  unfold pm toG
  rw [dite_eq_left h]
  rfl

theorem conj_apply (σ : Equiv.Perm (Fin n)) (x : Gn g n) (r c : Fin n) :
    (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c = (x : Mt g n) (σ r) (σ c) := by
  have h : ((pm g σ : Gn g n) : Mt g n) * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n)
      = (x : Mt g n) * ((pm g σ : Gn g n) : Mt g n) := by
    rw [← Units.val_mul, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  generalize (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) = Y at h ⊢
  have h2 := congrFun (congrFun h (σ r)) c
  rw [Matrix.mul_apply, Matrix.mul_apply] at h2
  have h3 : ∀ r j, ((pm g σ : Gn g n) : Mt g n) r j = if r = σ j then 1 else 0 := fun r j => by
    rw [pm_val]
  simpa [h3] using h2

noncomputable def elem (p q : Fin n) (h : p ≠ q) (t : ZMod g) : Gn g n :=
  ⟨Matrix.transvection p q t, Matrix.transvection p q (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

theorem mul_elem_apply (p q : Fin n) (h : p ≠ q) (t : ZMod g) (x : Gn g n) (r c : Fin n) :
    ((x * elem p q h t : Gn g n) : Mt g n) r c
      = (x : Mt g n) r c + if c = q then t * (x : Mt g n) r p else 0 := by
  change ((x : Mt g n) * Matrix.transvection p q t) r c = _
  by_cases hc : c = q
  · subst hc; simp
  · simp [hc]

theorem isUniUp_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) : IsUniUp M' := by
  intro r c
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [h, (hM r c).1 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; exact hpq.trans hc)]; simp
    · simp
  · rw [h, (hM r c).2 hc]
    split_ifs with h1
    · rw [(hM r p).1 (by subst h1; subst hc; exact hpq)]; simp
    · simp

theorem isUniUp_iff_of_col {M M' : Mt g n} {p q : Fin n} (hpq : p < q) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) : IsUniUp M' ↔ IsUniUp M := by
  refine ⟨isUniUp_of_col hpq (-t) fun r c => ?_, isUniUp_of_col hpq t h⟩
  rw [h r c, h r p, if_neg hpq.ne]
  split_ifs <;> ring

theorem supFrom_of_col {M M' : Mt g n} {p q : Fin n} (hpq : (q : ℕ) = p + 1) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = q then t * M r p else 0) (hM : IsUniUp M) :
    supFrom 0 M' = supFrom 0 M + t := by
  have hq := q.2
  have : ∀ k ∈ Finset.Ico 0 (n - 1),
      entN M' k (k + 1) = entN M k (k + 1) + if k = (p : ℕ) then t else 0 := by
    intro k hk
    have hk' : k < n ∧ k + 1 < n := by have := (Finset.mem_Ico.1 hk).2; omega
    unfold entN
    rw [dite_eq_left hk', dite_eq_left hk', h]
    congr 1
    by_cases hkp : k = (p : ℕ)
    · rw [if_pos hkp, if_pos (Fin.ext (by simp [hkp, hpq])), (hM _ p).2 (Fin.ext hkp), mul_one]
    · rw [if_neg hkp, if_neg]
      intro h1
      have := congrArg Fin.val h1
      simp only at this
      omega
  unfold supFrom
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos]
  rw [Finset.mem_Ico]; omega

theorem inPar_iff_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : InPar a M' ↔ InPar a M := by
  refine forall_congr' fun r => forall_congr' fun c => forall_congr' fun hc => ?_
  rw [h, if_neg (by rintro rfl; omega), add_zero]

theorem tl_of_col {M M' : Mt g n} {a : ℕ} {i j : Fin n} (hj : a ≤ (j : ℕ)) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) : tl a M' = tl a M := by
  ext r c
  unfold tl entN
  split_ifs with h1
  · rw [h, if_neg, add_zero]
    rintro rfl
    have := c.2
    simp only at hj
    omega
  · rfl

theorem br_of_col {M M' : Mt g n} {a b : ℕ} {i j : Fin n} (hi : (i : ℕ) < a) (t : ZMod g)
    (h : ∀ r c, M' r c = M r c + if c = j then t * M r i else 0) (hM : InPar a M) :
    br a b M' = br a b M := by
  ext r c
  unfold br entN
  split_ifs with h1
  · rw [h, hM _ i hi (by simp)]; simp
  · rfl

theorem whittaker_term_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)) (Φ : Gn g a → Gn g b → ℂ) (i j : Fin n), n = a + b → (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) = σ i + 1 → (∑ x : Gn g n, if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0) = 0 := by
  intro g _ ψ hψ a b n σ Φ i j _ hi hj hσ
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ (by ext t; simpa using hc t)
  have hlt : σ i < σ j := by rw [Fin.lt_def]; omega
  set F : Gn g n → ℂ := fun x => if IsUniUp (x : Mt g n) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) then (ψ (supFrom 0 (x : Mt g n)))⁻¹ * Φ (toG (tl a (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) (toG (br a b (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n))) else 0 with hF
  have key : ∀ x, F (x * elem (σ i) (σ j) hlt.ne t) = (ψ t)⁻¹ * F x := by
    intro x
    have h1 := mul_elem_apply (σ i) (σ j) hlt.ne t x
    have h2 : ∀ r c, (((pm g σ)⁻¹ * (x * elem (σ i) (σ j) hlt.ne t) * pm g σ : Gn g n) : Mt g n) r c
        = (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r c
          + if c = j then t * (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) r i else 0 := by
      intro r c
      rw [conj_apply, conj_apply, conj_apply, h1]
      simp only [σ.apply_eq_iff_eq]
    simp only [hF]
    rw [isUniUp_iff_of_col hlt t h1, inPar_iff_of_col hj t h2]
    split_ifs with hx
    · rw [supFrom_of_col hσ t h1 hx.1, tl_of_col hj t h2, br_of_col hi t h2 hx.2, AddChar.map_add_eq_mul,
        mul_inv]
      ring
    · simp
  have hS : ∑ x, F x = (ψ t)⁻¹ * ∑ x, F x := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight (elem (σ i) (σ j) hlt.ne t)) F]
    exact Finset.sum_congr rfl fun x _ => key x
  change ∑ x, F x = 0
  by_contra hne
  apply ht
  have : (ψ t)⁻¹ = 1 := mul_right_cancel₀ hne (by rw [one_mul]; exact hS.symm)
  exact inv_eq_one.1 this

end GlobalTheory.GLm.NonOpenCell
end

