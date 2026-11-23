module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionUnipotentInvariant
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetSecondCayleyBlockNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CmiMulCm
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem mul_cm₁₁ (x : M2 n) : (x * Cm n).toBlocks₁₁ = Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂ := by
  simp [toBlocks₁₁_mul', Cm, Matrix.mul_smul]

theorem cmS : (Cm n)ᴴ * JJ n * Cm n = fromBlocks ((-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0
    ((2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [Cm, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem cmiH_cmi : (Cmi n)ᴴ * Cmi n = (1 / 2 : ℂ) • (1 : M2 n) := by
  rw [← fromBlocks_one, fromBlocks_smul]
  simp only [Cmi, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem mR_inv_mul (y y' : GR n) : mR (y⁻¹ * y') = (mR y)⁻¹ * mR y' := by
  simp [mR, Matrix.coe_units_inv]

theorem isUnit_mR (y : GR n) : IsUnit (mR y) := (y.1).isUnit

theorem fib : Fib := by
  intro n y y' hz
  have hGk : InG (mR (y⁻¹ * y')) := (y⁻¹ * y').2
  refine ⟨hGk, ?_⟩
  set x := mR y with hxdef
  set x' := mR y' with hx'def
  set k := mR (y⁻¹ * y') with hkdef
  have hkxx : k = x⁻¹ * x' := mR_inv_mul y y'
  have hxu : IsUnit x := isUnit_mR y
  have hxdet : IsUnit x.det := (Matrix.isUnit_iff_isUnit_det x).1 hxu
  have hu1 : (u1 x).det ≠ 0 := (detU1 n y).1
  have hu1' : (u1 x').det ≠ 0 := (detU1 n y').1
  have hu1u : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 hu1
  have hu1u' : IsUnit (u1 x').det := isUnit_iff_ne_zero.2 hu1'
  set c := (u1 x)⁻¹ * u1 x' with hc

  have h21 : (x' * Cm n).toBlocks₂₁ = (x * Cm n).toBlocks₂₁ * c := by
    rw [mul_cm₂₁, mul_cm₂₁, hc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1u, Matrix.one_mul]
  have h11 : (x' * Cm n).toBlocks₁₁ = (x * Cm n).toBlocks₁₁ * c := by
    rw [mul_cm₁₁, mul_cm₁₁]
    have hz' : (Complex.I • x.toBlocks₁₁ + x.toBlocks₁₂) * (u1 x)⁻¹ =
        (Complex.I • x'.toBlocks₁₁ + x'.toBlocks₁₂) * (u1 x')⁻¹ := hz
    have := congrArg (· * u1 x') hz'
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1u', Matrix.mul_one] at this
    rw [hc]; exact this.symm

  set D := Cmi n * k * Cm n with hD
  have hDE : D * fromBlocks 1 0 0 0 = fromBlocks c 0 0 0 := by
    have e1 : x' * Cm n * fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0 0 =
        x * Cm n * fromBlocks c 0 0 0 := by
      conv_lhs => rw [← fromBlocks_toBlocks (x' * Cm n), fromBlocks_multiply]
      conv_rhs => rw [← fromBlocks_toBlocks (x * Cm n), fromBlocks_multiply]
      rw [h11, h21]; simp
    calc D * fromBlocks 1 0 0 0 = Cmi n * x⁻¹ * (x' * Cm n * fromBlocks 1 0 0 0) := by
          rw [hD, hkxx]; simp only [Matrix.mul_assoc]
      _ = Cmi n * x⁻¹ * (x * Cm n * fromBlocks c 0 0 0) := by rw [e1]
      _ = Cmi n * (x⁻¹ * x) * Cm n * fromBlocks c 0 0 0 := by simp only [Matrix.mul_assoc]
      _ = fromBlocks c 0 0 0 := by
          rw [Matrix.nonsing_inv_mul _ hxdet, Matrix.mul_one, cmi_mul_cm, Matrix.one_mul]
  have hD0 : D = fromBlocks c D.toBlocks₁₂ 0 D.toBlocks₂₂ := by
    have := hDE
    conv_lhs at this => rw [← fromBlocks_toBlocks D, fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero] at this
    obtain ⟨e11, -, e21, -⟩ := Matrix.fromBlocks_inj.1 this
    conv_lhs => rw [← fromBlocks_toBlocks D]
    rw [e11, e21]

  have hk : kᴴ * JJ n * k = JJ n := hGk
  have hS : Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D = (Cm n)ᴴ * JJ n * Cm n := by
    have hcc : (Cmi n)ᴴ * (Cm n)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, cm_mul_cmi, Matrix.conjTranspose_one]
    calc Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D
        = (Cm n)ᴴ * kᴴ * ((Cmi n)ᴴ * (Cm n)ᴴ) * JJ n * (Cm n * Cmi n) * k * Cm n := by
          rw [hD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * (kᴴ * JJ n * k) * Cm n := by
          rw [hcc, cm_mul_cmi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Cm n)ᴴ * JJ n * Cm n := by rw [hk]
  rw [cmS, hD0] at hS
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_zero,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at hS
  obtain ⟨s11, s12, -, s22⟩ := Matrix.fromBlocks_inj.1 hS
  have hI : (-2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hI' : (2 * Complex.I) ≠ 0 := by simp [Complex.ext_iff]
  have hcc : cᴴ * c = 1 := by
    have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s11
    simpa [smul_smul, inv_mul_cancel₀ hI] using this
  have hcc' : c * cᴴ = 1 := mul_eq_one_comm.1 hcc
  have hB : D.toBlocks₁₂ = 0 := by
    have h1 : cᴴ * D.toBlocks₁₂ = 0 := by
      have := congrArg (fun M => (-2 * Complex.I)⁻¹ • M) s12
      simpa [smul_smul, inv_mul_cancel₀ hI] using this
    calc D.toBlocks₁₂ = c * cᴴ * D.toBlocks₁₂ := by rw [hcc', Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have hc' : (D.toBlocks₂₂)ᴴ * D.toBlocks₂₂ = 1 := by
    rw [hB] at s22
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, smul_zero] at s22
    have := congrArg (fun M => (2 * Complex.I)⁻¹ • M) s22
    simpa [smul_smul, inv_mul_cancel₀ hI'] using this
  have hDD : Dᴴ * D = 1 := by
    rw [hD0, hB, fromBlocks_conjTranspose, fromBlocks_multiply, hcc, hc', ← fromBlocks_one]
    simp

  have hkD : k = Cm n * D * Cmi n := by
    rw [hD]; simp only [← Matrix.mul_assoc]
    rw [cm_mul_cmi, Matrix.one_mul, Matrix.mul_assoc, cm_mul_cmi, Matrix.mul_one]
  have hcm2 : (Cm n)ᴴ * Cm n = (2 : ℂ) • (1 : M2 n) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    simp only [Cm, fromBlocks_conjTranspose, fromBlocks_multiply]
    congr 1 <;> ext i j <;> simp [Matrix.one_apply] <;> split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  calc kᴴ * k = (Cmi n)ᴴ * (Dᴴ * ((Cm n)ᴴ * Cm n) * D) * Cmi n := by
        rw [hkD]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (2 : ℂ) • ((Cmi n)ᴴ * Cmi n) := by
        rw [hcm2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hDD, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one]
    _ = 1 := by rw [cmiH_cmi, smul_smul]; norm_num

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicTranslationLevi
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

abbrev EE (n : ℕ) := Fin n → Fin n → ℂ

theorem herm_re (v : EE n) : (Matrix.of ((1 / 2 : ℂ) • (v + fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  ring

theorem herm_im (v : EE n) :
    (Matrix.of ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  field_simp
  ring

theorem split_re_im (v : EE n) :
    v = (1 / 2 : ℂ) • (v + fun i j => star (v j i)) + Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i))) := by
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

private theorem herm_Hpk_smul_left (k : EE n) (hk : (Matrix.of k).IsHermitian) (t : ℝ) :
    (Matrix.of ((t : ℂ) • k)).IsHermitian := by
  ext i j
  have h2 := congrFun (congrFun hk i) j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2 ⊢
  simp [h2]

theorem const_of_transl (G : EE n → ℂ) (hG : DifferentiableOn ℂ G (Dom n))
    (hT : ∀ W ∈ Dom n, ∀ k : EE n, (Matrix.of k).IsHermitian → G (W + k) = G W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n, G W = G W' := by
  have key : ∀ W ∈ Dom n, fderiv ℂ G W = 0 := by
    intro W hW
    have hGd : HasFDerivAt G (fderiv ℂ G W) W :=
      ((hG W hW).differentiableAt (isOpen_dom'.mem_nhds hW)).hasFDerivAt
    have hk0 : ∀ k : EE n, (Matrix.of k).IsHermitian → fderiv ℂ G W k = 0 := by
      intro k hk
      have hc : HasDerivAt (fun t : ℝ => W + (t : ℂ) • k) k 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const k).const_add W
        simpa using h1
      have hcomp := (hGd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
      have hfun : (G ∘ fun t : ℝ => W + (t : ℂ) • k) = fun _ => G W := by
        funext t
        exact hT W hW _ (herm_Hpk_smul_left k hk t)
      rw [hfun] at hcomp
      simpa using hcomp.unique (hasDerivAt_const _ _)
    refine ContinuousLinearMap.ext fun v => ?_
    calc fderiv ℂ G W v = fderiv ℂ G W ((1 / 2 : ℂ) • (v + fun i j => star (v j i)) +
          Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))) := by
          rw [← split_re_im v]
      _ = 0 := by
          rw [map_add (f := _), hk0 _ (herm_re v), map_smul, hk0 _ (herm_im v)]
          simp
  intro W hW W' hW'
  exact convex_dom'.is_const_of_fderivWithin_eq_zero hG
    (fun x hx => by rw [fderivWithin_of_isOpen isOpen_dom' hx]; exact key x hx) hW hW'

private theorem exp_trace_mul_H_const_on_dom (H : EE n → ℂ) (hH : DifferentiableOn ℂ H (Dom n))
    (β : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c * c = 1) (hcs : star c = c)
    (hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n,
      Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W =
        Complex.exp (-(c * Complex.I * (β * Matrix.of W').trace)) * H W' := by
  apply const_of_transl (fun W => Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W)
  · refine DifferentiableOn.mul ?_ hH
    apply Differentiable.differentiableOn
    have hl : Differentiable ℂ (fun W : EE n => (β * Matrix.of W).trace) := by
      simp only [Matrix.trace, Matrix.mul_apply, Matrix.of_apply, Matrix.diag]
      fun_prop
    fun_prop
  · intro W hW k hk
    have hof : Matrix.of (c • k) = c • Matrix.of k := rfl
    have hh : (Matrix.of (c • k)).IsHermitian := by
      rw [hof, Matrix.IsHermitian, Matrix.conjTranspose_smul, hcs, hk.eq]
    have hWk : W + k = W + c • (c • k) := by
      ext i j
      simp [smul_smul, hc]
    have htr : (β * Matrix.of (W + k)).trace = (β * Matrix.of W).trace + (β * Matrix.of k).trace := by
      rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.trace_add]
    have htr2 : (β * Matrix.of (c • k)).trace = c * (β * Matrix.of k).trace := by
      rw [hof, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hHk : H (W + k) = Complex.exp (Complex.I * (c * (β * Matrix.of k).trace)) * H W := by
      rw [hWk, hT W hW _ hh, htr2]
    try dsimp only
    rw [hHk, htr, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

theorem holomorphic_translation_levi : ∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y := by
  intro n p q e φ hφ β hβ a a' x y hx ha
  obtain ⟨H, hH, hφH⟩ := hφ
  obtain ⟨Z, hZ⟩ : ∃ Z : GR n → Matrix (Fin n) (Fin n) ℂ,
      ∀ y, Z y = if q = 0 then zOf y else -(zOf y)ᴴ := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = if q = 0 then 1 else -1 := ⟨_, rfl⟩
  have hφ' : ∀ y, φ y = F0 p q e y * H (Z y) := fun y => by rw [hZ]; exact hφH y
  have hdom : ∀ y : GR n, Z y ∈ Dom n := by
    intro y
    rw [hZ]
    split_ifs
    · exact zOf_mem' y
    · exact neg_conj_mem' (zOf_mem' y)
  have hsurj : ∀ W ∈ Dom n, ∃ y : GR n, Z y = W := by
    intro W hW
    simp only [hZ]
    split_ifs
    · exact zOf_surj' hW
    · obtain ⟨y, hy⟩ := zOf_surj' (neg_conj_mem' hW)
      refine ⟨y, ?_⟩
      rw [hy]
      simp only [Matrix.conjTranspose_neg, neg_neg, Matrix.conjTranspose_conjTranspose]
      rfl
  have hnU : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      Z (x * y) = Z y + c • h := by
    intro h x y hh hx
    rw [hZ, hZ, hc, zOf_nU' h x y hx]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_add, hh.eq]
      simp
      abel
  have hlevi : ∀ y : GR n, Z (x * y) = a * Z y * aᴴ := by
    intro y
    rw [hZ, hZ, zOf_levi' a a' x y hx]
    split_ifs
    · rfl
    · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W := by
    intro W hW h hh
    obtain ⟨y0, hy0⟩ := hsurj W hW
    obtain ⟨x0, hx0⟩ := nU_mem' hh
    have h1 := hβ _ x0 y0 hh hx0
    rw [hφ', hφ', spherical_section_unipotent_invariant p q e _ x0 y0 hx0, hnU _ x0 y0 hh hx0] at h1
    have e0 : (W + c • h : EE n) = Z y0 + c • Matrix.of h := by
      rw [hy0]
      rfl
    rw [e0]
    apply mul_left_cancel₀ (spherical_section_ne_zero_group p q e y0)
    rw [h1, hy0]
    ring
  have hc2 : c * c = 1 := by
    rw [hc]
    split_ifs <;> norm_num
  have hcs : star c = c := by
    rw [hc]
    split_ifs <;> simp
  have hconst := exp_trace_mul_H_const_on_dom H hH β c hc2 hcs hT
  have htr : (β * (a * Z y * aᴴ)).trace = (β * Z y).trace := by
    rw [show β * (a * Z y * aᴴ) = (β * a * Z y) * aᴴ by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show aᴴ * (β * a * Z y) = (aᴴ * β * a) * Z y by simp [Matrix.mul_assoc], ha]
  have hHeq : H (a * Z y * aᴴ) = H (Z y) := by
    have h1 := hconst _ (hlevi y ▸ hdom (x * y)) _ (hdom y)
    have htr' : (β * Matrix.of (a * Z y * aᴴ)).trace = (β * Matrix.of (Z y)).trace := htr
    rw [htr'] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  rw [hφ' (x * y), hφ' y, spherical_section_levi_mul p q e a a' x y hx, hlevi y, hHeq]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTau
section
namespace PositivityTheory.Rg.Sw.HSt

theorem locTau : LocTau := asmLT lt1 lt2 lt3 crux

end PositivityTheory.Rg.Sw.HSt
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothPf
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_restrict_of_zero (ν : Measure (GR n)) {C : Set (GR n)} (_hCm : MeasurableSet C) {F : GR n → ℂ}
    (hF : ∀ u ∉ C, F u = 0) : ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict C) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem holInt (ν : Measure (GR n)) [ν.IsHaarMeasure] {C : Set (GR n)} (hC : IsCompact C) {U : Set ℂ} (hU : IsOpen U)
    (F : GR n → ℂ → ℂ) (hF0 : ∀ u ∉ C, ∀ z, F u z = 0)
    (hcont : ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ u ∈ C, DifferentiableOn ℂ (F u) U) :
    DifferentiableOn ℂ (fun z => ∫ u, F u z ∂ν) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ u, F u z ∂ν) z = ∫ u, iteratedDeriv r (F u) z ∂ν := by
  classical
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hdF : ∀ u, DifferentiableOn ℂ (F u) U := by
    intro u
    by_cases hu : u ∈ C
    · exact hd u hu
    · have h0 : F u = fun _ => 0 := funext (hF0 u hu)
      rw [h0]
      exact differentiableOn_const 0
  have key : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨(ε / 2).toNNReal, Real.toNNReal_pos.mpr (half_pos hε), ?_⟩
    rw [Real.coe_toNNReal _ (half_pos hε).le]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      Integrable (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod (ν.restrict C)) := by
    intro z R hzR a ha
    rw [Measure.prod_restrict]
    have hc2 : ContinuousOn (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        (Set.Icc 0 (2 * Real.pi) ×ˢ C) := by
      apply ContinuousOn.smul (ha.comp continuous_fst).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × GR n => (p.2, circleMap z R p.1)) (Set.Icc 0 (2 * Real.pi) ×ˢ C) :=
        (continuous_snd.prodMk ((continuous_circleMap z R).comp continuous_fst)).continuousOn
      refine hcont.comp h1 ?_
      rintro ⟨θ, u⟩ ⟨_, hu⟩
      exact ⟨hu, hzR (circleMap_mem_closedBall z R.coe_nonneg θ)⟩
    exact (hc2.integrableOn_compact (isCompact_Icc.prod hC)).mono_set
      (Set.prod_mono (Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le (by positivity)).subset) subset_rfl)
  have hfub : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • ∫ u, F u (circleMap z R θ) ∂ν)
        = ∫ u, (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • F u (circleMap z R θ)) ∂ν := by
    intro z R hzR a ha
    have e1 : ∀ θ, a θ • ∫ u, F u (circleMap z R θ) ∂ν
        = ∫ u, a θ • F u (circleMap z R θ) ∂(ν.restrict C) := by
      intro θ
      rw [integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu (circleMap z R θ)), integral_smul]
    simp_rw [e1]
    rw [intervalIntegral_integral_swap (hint z R hzR a ha)]
    exact (integral_restrict_of_zero ν hCm (fun u hu => by simp [hF0 u hu])).symm
  have hcirc : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ k : ℂ → ℂ,
      Continuous (fun θ => k (circleMap z R θ)) →
      (∮ ζ in C(z, R), k ζ • ∫ u, F u ζ ∂ν) = ∫ u, (∮ ζ in C(z, R), k ζ • F u ζ) ∂ν := by
    intro z R hzR k hk
    simp only [circleIntegral, deriv_circleMap, smul_smul]
    exact hfub z R hzR (fun θ => circleMap 0 R θ * Complex.I * k (circleMap z R θ))
      (((continuous_circleMap 0 R).mul continuous_const).mul hk)
  have hps : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U ∧
      HasFPowerSeriesOnBall (fun w => ∫ u, F u w ∂ν) (cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R) z R := by
    intro z hz
    obtain ⟨R, hR, hzR⟩ := key z hz
    refine ⟨R, hR, hzR, ?_⟩
    have hci : CircleIntegrable (fun w => ∫ u, F u w ∂ν) z R := by
      have h := (hint z R hzR (fun _ => 1) continuous_const).integral_prod_left
      rw [CircleIntegrable, intervalIntegrable_iff]
      refine h.congr (Eventually.of_forall fun θ => ?_)
      simp only [one_smul]
      exact (integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu _)).symm
    refine (hasFPowerSeriesOn_cauchy_integral hci hR).congr ?_
    intro w hw
    rw [Metric.eball_coe] at hw
    have hk : Continuous (fun θ => (circleMap z R θ - w)⁻¹) :=
      ((continuous_circleMap z R).sub continuous_const).inv₀
        (fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hw θ))
    show (2 * ↑Real.pi * Complex.I)⁻¹ • (∮ ζ in C(z, R), (ζ - w)⁻¹ • ∫ u, F u ζ ∂ν) = ∫ u, F u w ∂ν
    rw [hcirc z R hzR (fun ζ => (ζ - w)⁻¹) hk, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw ((hdF u).continuousOn.mono hzR)
      (fun x hx => (hdF u).differentiableAt (hU.mem_nhds (hzR (Metric.ball_subset_closedBall hx.1))))
  constructor
  · intro z hz
    obtain ⟨R, -, -, h⟩ := hps z hz
    exact h.analyticAt.differentiableAt.differentiableWithinAt
  · intro z hz r
    obtain ⟨R, hR, hzR, h⟩ := hps z hz
    have hFu : ∀ u, iteratedDeriv r (F u) z = r.factorial • cauchyPowerSeries (F u) z R r (fun _ => 1) := by
      intro u
      rw [iteratedDeriv_eq_iteratedFDeriv, ← (((hdF u).mono hzR).hasFPowerSeriesOnBall hR).factorial_smul]
    have hne : ∀ θ, circleMap z R θ - z ≠ 0 := fun θ =>
      sub_ne_zero.mpr (fun h' => hR.ne' (by exact_mod_cast circleMap_eq_center_iff.mp h'))
    have hG : cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R r (fun _ => 1)
        = ∫ u, cauchyPowerSeries (F u) z R r (fun _ => 1) ∂ν := by
      simp only [cauchyPowerSeries_apply, smul_smul]
      rw [hcirc z R hzR (fun ζ => (1 / (ζ - z)) ^ r * (ζ - z)⁻¹)
        (((continuous_const.div ((continuous_circleMap z R).sub continuous_const) hne).pow r).mul
          (((continuous_circleMap z R).sub continuous_const).inv₀ hne)), integral_smul]
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h.factorial_smul, integral_congr_ae (Eventually.of_forall hFu), hG]
    simp only [nsmul_eq_mul]
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

