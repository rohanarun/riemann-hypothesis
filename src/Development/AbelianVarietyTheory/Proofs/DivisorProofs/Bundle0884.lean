module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianCongrOfPositiveIndexEq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.HermCongruence

def signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : Fin n → ℂ :=
  fun i => if 0 < hA.eigenvalues i then 1 else -1

theorem eigenvalues_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0)
    (i : Fin n) : hA.eigenvalues i ≠ 0 := by
  intro h
  apply hd
  rw [hA.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

theorem exists_congr_signVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hd : A.det ≠ 0) :
    ∃ V : GL (Fin n) ℂ, (V : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * V = diagonal (signVec hA) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    have := hA.eigenvectorUnitary.2.1
    simpa [hU, Matrix.star_eq_conjTranspose] using this
  have hspec : A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have := hA.spectral_theorem
    simpa [hU, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  set c : Fin n → ℂ := fun i => ((Real.sqrt |hA.eigenvalues i|)⁻¹ : ℝ) with hc
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i
    have h1 : 0 < |hA.eigenvalues i| := abs_pos.2 (eigenvalues_ne_zero hA hd i)
    simp [hc, Real.sqrt_eq_zero', not_le.2 h1, eigenvalues_ne_zero hA hd i]
  set V := U * diagonal c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, det_mul, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hc0 i)
    intro h
    have := congrArg det hUU
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨GeneralLinearGroup.mkOfDetNeZero V hVdet, ?_⟩
  show Vᴴ * A * V = _
  have hcs : (diagonal c)ᴴ = diagonal c := by
    rw [diagonal_conjTranspose]
    congr 1; funext i; simp [hc]
  rw [hV, conjTranspose_mul, hcs]
  conv_lhs => rw [hspec]
  have : diagonal c * Uᴴ * (U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ) * (U * diagonal c) =
      diagonal c * (Uᴴ * U) * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * (Uᴴ * U) * diagonal c := by
    simp only [Matrix.mul_assoc]
  rw [this, hUU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  have hne := eigenvalues_ne_zero hA hd i
  have hpos : 0 < |hA.eigenvalues i| := abs_pos.2 hne
  have hsq : Real.sqrt |hA.eigenvalues i| * Real.sqrt |hA.eigenvalues i| = |hA.eigenvalues i| :=
    Real.mul_self_sqrt hpos.le
  have hs0 : Real.sqrt |hA.eigenvalues i| ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : (Real.sqrt |hA.eigenvalues i|)⁻¹ * hA.eigenvalues i * (Real.sqrt |hA.eigenvalues i|)⁻¹ =
      if 0 < hA.eigenvalues i then 1 else -1 := by
    rw [mul_comm, ← mul_assoc, ← mul_inv, hsq]
    split_ifs with h
    · rw [abs_of_pos h]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hne)]; field_simp
  simp only [signVec, hc]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]
  split_ifs <;> simp

end GlobalTheory.HermCongruence

namespace GlobalTheory.HermCongruence

theorem exists_equiv_pos {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : sigPosH hA = sigPosH hB) :
    ∃ e : Fin n ≃ Fin n, ∀ i, (0 < hA.eigenvalues (e i) ↔ 0 < hB.eigenvalues i) := by
  have h1 : Fintype.card {i // 0 < hB.eigenvalues i} = Fintype.card {i // 0 < hA.eigenvalues i} := h.symm
  have h2 : Fintype.card {i // ¬ 0 < hB.eigenvalues i} = Fintype.card {i // ¬ 0 < hA.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun i => ?_⟩
  by_cases hi : 0 < hB.eigenvalues i
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h1) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_true ((Fintype.equivOfCardEq h1) ⟨i, hi⟩).2 hi
  · have hx : Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2) i =
        ((Fintype.equivOfCardEq h2) ⟨i, hi⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, hi]
    rw [hx]
    exact iff_of_false ((Fintype.equivOfCardEq h2) ⟨i, hi⟩).2 hi

theorem perm_congr {n : ℕ} (d : Fin n → ℂ) (e : Fin n ≃ Fin n) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e)ᴴ * diagonal d * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e =
      diagonal (d ∘ e) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  split_ifs with h <;> simp [h]

theorem congr_of_sigPosH_eq : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian),
    A.det ≠ 0 → B.det ≠ 0 → sigPosH hA = sigPosH hB →
      ∃ Z : GL (Fin n) ℂ, B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) := by
  intro n A B hA hB hdA hdB hs
  obtain ⟨VA, hVA⟩ := exists_congr_signVec hA hdA
  obtain ⟨VB, hVB⟩ := exists_congr_signVec hB hdB
  obtain ⟨e, he⟩ := exists_equiv_pos hA hB hs
  set P : Matrix (Fin n) (Fin n) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e with hP
  have hPP : P * (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id e.symm = 1 := by
    ext i j; simp [hP, Matrix.mul_apply, Matrix.one_apply]
  have hPdet : P.det ≠ 0 := by
    intro h
    have := congrArg det hPP
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  have hsig : signVec hA ∘ e = signVec hB := by
    funext i
    simp only [Function.comp_apply, signVec]
    by_cases hi : 0 < hB.eigenvalues i
    · rw [if_pos hi, if_pos ((he i).2 hi)]
    · rw [if_neg hi, if_neg (fun h => hi ((he i).1 h))]
  refine ⟨VA * GeneralLinearGroup.mkOfDetNeZero P hPdet * VB⁻¹, ?_⟩
  set W : Matrix (Fin n) (Fin n) ℂ := ((VB⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hW
  have hVW : (VB : Matrix (Fin n) (Fin n) ℂ) * W = 1 := by
    rw [hW, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hWV : Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    rw [← conjTranspose_mul, hVW, conjTranspose_one]
  have hP' : ((GeneralLinearGroup.mkOfDetNeZero P hPdet : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = P := rfl
  rw [Units.val_mul, Units.val_mul, hP', ← hW, conjTranspose_mul, conjTranspose_mul]
  have : Wᴴ * (Pᴴ * (VA : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A * (VA * P * W) =
      Wᴴ * (Pᴴ * ((VA : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * VA) * P) * W := by
    simp only [Matrix.mul_assoc]
  rw [this, hVA, hP, perm_congr, hsig, ← hVB]
  have : Wᴴ * ((VB : Matrix (Fin n) (Fin n) ℂ)ᴴ * B * VB) * W =
      (Wᴴ * (VB : Matrix (Fin n) (Fin n) ℂ)ᴴ) * B * ((VB : Matrix (Fin n) (Fin n) ℂ) * W) := by
    simp only [Matrix.mul_assoc]
  rw [this, hWV, hVW, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.HermCongruence
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPoints
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem iterate_fst (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    ((⇑(sigG G r))^[k] g).1 = (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem iterate_snd (G : HTGroup p) (r k : ℕ) (g : Gr G r) (i : Fin G.m) :
    ((⇑(sigG G r))^[k] g).2 i = (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl

theorem unramifiedExtFrobeniusGL_one_iterate_degree (r : ℕ) (hr : 0 < r) (g : GL (Fin 1) (Qr p r)) :
    (⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin 1), ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g).val i j
      = (⇑(frobQ p r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, GlobalTheory.LKResNrmConj.frobQ_iterate_self p r hr]

theorem inclK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    Function.Injective (inclK p K r) :=
  Algebra.TensorProduct.includeLeft_injective (S := ℚ_[p]) (algebraMap ℚ_[p] (Qr p r)).injective

theorem iterate_self (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [iterate_fst, unramifiedExtFrobeniusGL_one_iterate_degree r hr]
  · rw [iterate_snd, GlobalTheory.LKResNrmConj.sigRes_iterate_self p (G.Fw i) G.n r hr]

theorem fix_incl (G : HTGroup p) (r : ℕ) (γ : Gp G) : sigG G r (inclG G r γ) = inclG G r γ := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change frobQ p r (((inclG G r γ).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe]
    by_cases h : a = b
    · subst h; simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ h]
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change sigKQ p (G.Fw i) r (((inclG G r γ).2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b) = _
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_snd, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact sigKQ_apply_inclK p (G.Fw i) r _

end GlobalTheory.LKMid.SigIter

namespace GlobalTheory.LKMid.SigIter

variable {p : ℕ} [Fact p.Prime]

theorem incl_injective (G : HTGroup p) (r : ℕ) : Function.Injective (inclG G r) := by
  intro γ γ' h
  have h1 := congrArg (fun g : Gr G r => ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h
  have h2 := fun i (a b : Fin G.n) =>
    congrArg (fun g : Gr G r => ((g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) h
  simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst, MonoidHom.coe_snd, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
    MonoidHom.coe_coe, Pi.monoidHom_apply, Pi.evalMonoidHom_apply, GeneralLinearGroup.map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Matrix.diagonal_apply_eq] at h1 h2
  refine Prod.ext (Units.ext ((algebraMap ℚ_[p] (Qr p r)).injective h1)) (funext fun i => ?_)
  exact Units.ext (Matrix.ext fun a b => inclK_injective (G.Fw i) r (h2 i a b))

theorem fixed_mem_range (G : HTGroup p) (r : ℕ) (hr : 0 < r) (g : Gr G r) (hg : sigG G r g = g) :
    g ∈ (inclG G r).range := by
  have hf : frobQ p r ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) = (g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 :=
    congrArg (fun x : Gr G r => ((x.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) hg
  obtain ⟨c, hc⟩ := frobQ_fixed_mem p r hr _ hf
  have hdet1 : IsUnit ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) := by
    have := Matrix.isUnits_det_units g.1
    rwa [Matrix.det_fin_one] at this
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact not_isUnit_zero (hc ▸ hdet1)
  have hfix : ∀ i (a b : Fin G.n), ∃ x : G.Fw i,
      inclK p (G.Fw i) r x = (g.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b := fun i a b =>
    sigKQ_fixed_eq_inclK p (G.Fw i) r hr _
      (congrArg (fun x : Gr G r => ((x.2 i : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r)) a b)) hg)
  choose M hM using hfix
  have hmap : ∀ i, (Matrix.of (M i)).map (inclK p (G.Fw i) r) = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
    fun i => Matrix.ext fun a b => hM i a b
  have hdet : ∀ i, (Matrix.of (M i)).det ≠ 0 := by
    intro i h0
    have e := RingHom.map_det (inclK p (G.Fw i) r).toRingHom (Matrix.of (M i))
    rw [h0, map_zero, RingHom.mapMatrix_apply] at e
    have e' : (Matrix.of (M i)).map (inclK p (G.Fw i) r).toRingHom = (g.2 i : Matrix (Fin G.n) (Fin G.n) _) :=
      hmap i
    rw [e'] at e
    have hu := Matrix.isUnits_det_units (g.2 i)
    rw [← e] at hu
    have hsub : Subsingleton (KQ p (G.Fw i) r) := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
    have := inclK_injective (G.Fw i) r (Subsingleton.elim (inclK p (G.Fw i) r 1) (inclK p (G.Fw i) r 0))
    exact one_ne_zero this
  refine ⟨(Units.mk0 c hc0, fun i => GeneralLinearGroup.mkOfDetNeZero (Matrix.of (M i)) (hdet i)), ?_⟩
  refine Prod.ext (Units.ext (Matrix.ext fun a b => ?_)) (funext fun i => Units.ext ?_)
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp only [inclG, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_fst, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.coe_map,
      MonoidHom.coe_coe, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact hc
  · rw [← hmap i]
    rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r →
    (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧
      Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range :=
  fun _ _ G r hr => ⟨iterate_self G r hr, fix_incl G r, incl_injective G r, fixed_mem_range G r hr⟩

end GlobalTheory.LKMid.SigIter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxTranslateExponent
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

open GlobalTheory.FinTranslate

theorem hx_translate_exponent {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (hs : IsSympl X bas)
    (hd : x ∈ X.dom) (z a : Fin g → ℂ) :
    (Real.pi : ℂ) * I * (((hx X bas idx x (z + a) (-a)).im : ℝ) : ℂ) +
        -(Real.pi / 2 : ℂ) * hx X bas idx x (z + a) (z + a) =
      -(Real.pi / 2 : ℂ) * hx X bas idx x z z + -(Real.pi * hx X bas idx x (z + (1 / 2 : ℂ) • a) a) := by
  have h1 := fock_hx_conj X bas idx x hs hd z a
  have h2 := fock_hx_conj X bas idx x hs hd a a
  have h3 : hx X bas idx x (z + a) (-a) = -hx X bas idx x (z + a) a := by
    rw [← neg_one_smul ℂ a, fock_hx_smul_right]; simp
  rw [h3]
  simp only [fock_hx_add_left, fock_hx_add_right, fock_hx_smul_left]
  rw [h1]
  have h4 : (hx X bas idx x a a).im = 0 := conj_eq_iff_im.1 h2.symm
  generalize hx X bas idx x z a = s
  generalize hx X bas idx x z z = t
  generalize hx X bas idx x a a = q at h4
  have h5 : ((s.im : ℝ) : ℂ) = (s - conj s) / (2 * I) := im_eq_sub_conj s
  simp only [neg_im, add_im, h4, add_zero, ofReal_neg, h5]
  field_simp
  ring

theorem reads_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ γ u, IsFinOf V W γ u → Reads θ V W hr X bas idx (heisO ψ V W u f) (heisG X bas (-(colsR hr γ)) φ) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0 f φ hf hR γ u hu
  have hd : x ∈ X.dom := mem_dom_of_isOrtho hx0
  obtain ⟨hsb, hth⟩ := (thA_heis_entire_linear_injective D.host.E r g V.rank X bas idx hs he x hd φ hR.1).1
    (-(colsR hr γ))
    |> fun h => (⟨(h 0).1, fun z => (h z).2⟩ : _ ∧ ∀ z, _)
  refine ⟨hsb, fun w hw => ?_⟩
  obtain ⟨hrat, hadd, -⟩ := RealCoord.zOf_coordinates D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x
  have hsy : ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I *
      ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
    first
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hd
      | exact GlobalTheory.AdThSympl.psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx0
  obtain ⟨v, hv⟩ : ∃ v : WO V W, ratW W V γ = v + u := ⟨ratW W V γ - u, (sub_add_cancel _ _).symm⟩
  have hfadd (a b : WO V W) : (a + b).map (finPart D) = a.map (finPart D) + b.map (finPart D) := by
    ext i j
    exact (finPart D).map_add _ _
  have hiadd (a b : WO V W) : (a + b).map (infPart D) = a.map (infPart D) + b.map (infPart D) := by
    ext i j
    exact (infPart D).map_add _ _
  have hvf : v.map (finPart D) = 0 := by
    have h := hu.2
    rw [hv, hfadd] at h
    exact left_eq_add.1 (h.trans (add_comm _ _))
  have hvi : v.map (infPart D) = (ratW W V γ).map (infPart D) := by
    rw [hv, hiadd, hu.1, add_zero]
  obtain ⟨w', hw'⟩ : ∃ w' : WO V W, w = w' + v := ⟨w - v, (sub_add_cancel _ _).symm⟩
  have hw'f : w'.map (finPart D) = 0 := by
    have h := hw
    rwa [hw', hfadd, hvf, add_zero] at h
  have hzv := hrat γ v hvi
  have hneg : ∀ b, pv X idx x ((-(colsR hr γ)) b) = -pv X idx x (colsR hr γ b) := by
    intro b
    have h0 : per X x 0 = 0 := by simpa using per_add X x 0 0
    have h1 := per_add X x (colsR hr γ b) (-(colsR hr γ b))
    rw [add_neg_cancel, h0] at h1
    funext j
    have h2 := congrFun h1 (idx j)
    simp only [Pi.add_apply, Pi.zero_apply] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hz' : zOf θ V W hr X idx x w' =
      fun b => zOf θ V W hr X idx x w b + pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hw', hadd, hzv]
    simp
  have hzv' : zOf θ V W hr X idx x v = fun b => -pv X idx x ((-(colsR hr γ)) b) := by
    funext b
    rw [hneg, hzv, neg_neg]
  have e1 : w + u = ratW W V γ + w' := by rw [hw', hv]; abel
  have e2 : -symplOH V W (ratW W V γ) w' = symplOH V W w' v := by
    rw [hv, symplOH_add_left, symplOH_fin_real hu.1 hw'f, add_zero, symplOH_skew V W v w']
  rw [heisO, symplOH_real_fin hu.1 hw, AddChar.map_zero_eq_one, _root_.one_mul, e1, hf.quasi, e2, hsy w' v hw'f,
    hR.2 w' hw'f, hth, hz', hzv', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [ofReal_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => hx_translate_exponent X bas idx x hs hd _ _

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepBaseChange
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.IndepBaseChange

open CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_contract {k E : Type} [Field k] [Field E] [Algebra k E] {A B : CommRingCat.{0}}
    {f : CommRingCat.of k ⟶ A} {p : A ⟶ B} {q : CommRingCat.of E ⟶ B}
    (po : IsPushout f (CommRingCat.ofHom (algebraMap k E)) p q) (l : E →ₗ[k] k) :
    ∃ Λ : B →+ A, ∀ (e : E) (a : A), Λ (q.hom e * p.hom a) = f.hom (l e) * a := by
  letI : Algebra k A := f.hom.toAlgebra
  have w := (CommRingCat.isPushout_tensorProduct k A E).w
  let d := po.desc _ _ w
  let m : A ⊗[k] E →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ l.lTensor A
  refine ⟨m.toAddMonoidHom.comp d.hom.toAddMonoidHom, fun e a => ?_⟩
  have h₁ : d.hom (p.hom a) = a ⊗ₜ[k] (1 : E) := congrArg (fun g => g.hom a) (po.inl_desc _ _ w)
  have h₂ : d.hom (q.hom e) = (1 : A) ⊗ₜ[k] e := congrArg (fun g => g.hom e) (po.inr_desc _ _ w)
  change m (d.hom (q.hom e * p.hom a)) = _
  rw [map_mul, h₁, h₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [m, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  rfl

theorem comb_f {k : Type} [Field k] (S : LinSys k) (u : Fin S.N → k) (i : S.L.ι) {W : S.Y.Opens}
    (h : W ≤ S.L.U i) : resG S.Y h ((S.comb u).f i) =
      ∑ j, ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top).hom (u j) *
        resG S.Y h ((S.b j).f i) := by
  let e : S.L.Sec →+ Γ(S.Y, W) :=
    { toFun := fun s => resG S.Y h (s.f i), map_zero' := map_zero _, map_add' := fun _ _ => map_add _ _ _ }
  refine (map_sum e _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (map_mul (resG S.Y h) _ _).trans (congrArg (· * _) ?_)
  refine (LB.resG_resG _ _ _).trans ?_
  rfl

theorem indep_baseChange (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k) (hS : S.Indep) :
    (S.baseChange E).Indep := by
  intro u hu
  have key : ∀ l : E →ₗ[k] k, (fun j => l (u j)) = (0 : Fin S.N → k) := fun l => by
    refine hS _ (LB.f_injective (funext fun i => ?_))
    refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
      (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
    · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
      exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
    obtain ⟨⟨W, hW⟩, hle⟩ := W
    have H := S.isPullback_baseChange E
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
      (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
    have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
        (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
      refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
        (by simp) ?_ (by simp) (by simp)
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    obtain ⟨Λ, hΛ⟩ := exists_contract po' l
    have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
      fun y hy => Set.mem_iInter.2 fun _ => hle hy
    have e := comb_f (S.baseChange E) u (fun _ => i) hle'
    rw [hu] at e
    have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
        ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
      have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
        (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
      have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
      exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
    have e₂ := congrArg Λ e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e', map_sum, hΛ] at e₂
    refine (comb_f S _ i hle).trans (e₂.symm.trans ?_)
    exact ((congrArg Λ (map_zero _)).trans (map_zero Λ)).trans (map_zero _).symm
  funext j
  exact (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l => congrFun (key l) j

end GlobalTheory.Adelic.IndepBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegrStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (exact GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (intros; apply GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSumStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArchimedeanRapidKernelOperator_finset_sum : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (ι : Type) [Fintype ι] (T : ι → (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), (∀ i, IsKerOpInf (T i)) → IsKerOpInf (fun W z g => ∑ i, T i W z g) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (exact GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum) | (intros; apply GlobalTheory.JSW.MirCinf.isKerOpInf_fintype_sum  <;> assumption)
end

