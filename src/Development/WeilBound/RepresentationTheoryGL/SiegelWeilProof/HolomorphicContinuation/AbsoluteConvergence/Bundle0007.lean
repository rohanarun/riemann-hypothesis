module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousOnTwistedSectionCompact
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem cont_KR_mul (n : ℕ) (y k1 : GR n) : Continuous (fun k : KR n => y * (k : GR n) * k1) :=
  (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem cont_KR_mul' (n : ℕ) (k1 : GR n) : Continuous (fun k : KR n => (k : GR n) * k1) :=
  continuous_subtype_val.mul continuous_const

theorem spherical_section_eq_extension {n : ℕ} (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g = twistedScalarSection p q e (mR g) := by
  simp only [F0, twistedScalarSection]

theorem inK_mul {n : ℕ} (k : KR n) (k1 : GR n) (hk1 : k1 ∈ KR n) : InK (mR ((k : GR n) * k1)) :=
  (KR n).mul_mem k.2 hk1

theorem continuousOn_twisted_section_compact {n : ℕ} (p q : ℕ) (e : ℤ) (X : Fin n → ℝ) (y k1 : GR n) (U : Set ℂ) (κ : KR n → ℂ)
    (hκ : Continuous κ) (C : Set (GR n)) (hC : ∀ k : KR n, y * (k : GR n) * k1 ∈ C)
    (hU2c : ContinuousOn (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) (C ×ˢ U)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul n y k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => twistedScalarSection p q e (mR (y * (yz.1 : GR n) * k1) * aZ X yz.2)) =
      (fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) ∘ (fun yz : KR n × ℂ => (y * (yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun yz : GR n × ℂ => twistedScalarSection p q e (mR yz.1 * aZ X yz.2)) hU2c hφ.continuousOn
    (fun yz hyz => ⟨hC yz.1, hyz.2⟩)

theorem contOn_Fid {n : ℕ} (k1 : GR n) (U U1 : Set ℂ) (hUU : U ⊆ U1) (κ : KR n → ℂ) (hκ : Continuous κ)
    (Fid : GR n → ℂ → ℂ) (hFidc : ContinuousOn (fun y : GR n × ℂ => Fid y.1 y.2) (univ ×ˢ U1)) :
    ContinuousOn (fun yz : KR n × ℂ => κ yz.1 * Fid ((yz.1 : GR n) * k1) yz.2) (univ ×ˢ U) := by
  refine (hκ.comp continuous_fst).continuousOn.mul ?_
  have hφ : Continuous (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    ((cont_KR_mul' n k1).comp continuous_fst).prodMk continuous_snd
  have hcmp : (fun yz : KR n × ℂ => Fid ((yz.1 : GR n) * k1) yz.2) =
      (fun y : GR n × ℂ => Fid y.1 y.2) ∘ (fun yz : KR n × ℂ => ((yz.1 : GR n) * k1, yz.2)) :=
    funext fun _ => rfl
  rw [hcmp]
  exact ContinuousOn.comp (g := fun y : GR n × ℂ => Fid y.1 y.2) hFidc hφ.continuousOn
    (fun yz hyz => ⟨mem_univ _, hUU hyz.2⟩)

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CycSecM
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology MvPolynomial
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.CycP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n}

def secK (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) : C(KR n, ℂ) :=
  ⟨fun k => sL R ((k : GR n) * y), (hL.cont R).comp (continuous_subtype_val.mul continuous_const)⟩

@[simp] theorem secK_apply (hL : LocData ε c t p q e sL ρ) (R : PX m n) (y : GR n) (k : KR n) :
    secK hL R y k = sL R ((k : GR n) * y) := rfl

def Ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) : Submodule ℂ (PX m n) where
  carrier := {R | ∀ y, L (secK hL R y) = 0}
  add_mem' := by
    intro R R' hR hR' y
    have : secK hL (R + R') y = secK hL R y + secK hL R' y := by ext k; simp
    rw [this, map_add (f := _), hR y, hR' y, add_zero]
  zero_mem' := by
    intro y
    have : secK hL 0 y = 0 := by ext k; simp
    rw [this, map_zero]
  smul_mem' := by
    intro a R hR y
    have : secK hL (a • R) y = a • secK hL R y := by ext k; simp
    rw [this, map_smul, hR y, smul_zero]

theorem ann_of_quot (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) {R D : PX m n} (hR : R ∈ Ann hL L)
    (hq : ∀ y : GR n, ∃ f : ℝ → GR n, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, s ≠ 0 → |s| < η → ∀ k : KR n,
      ‖(sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s - sL D ((k : GR n) * y)‖ ≤ δ) :
    D ∈ Ann hL L := by
  intro y
  have hR' : ∀ y', L (secK hL R y') = 0 := hR
  obtain ⟨f, hf⟩ := hq y
  set F : ℝ → C(KR n, ℂ) := fun s => (s : ℂ)⁻¹ • (secK hL R (y * f s) - secK hL R y) with hF
  have hU : TendstoUniformly (fun s (k : KR n) => F s k) (secK hL D y) (𝓝[≠] (0:ℝ)) := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    obtain ⟨η, hη, hs⟩ := hf (δ / 2) (by linarith)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨η, hη, ?_⟩
    intro s hs1 hs2 k
    have hs0 : s ≠ 0 := hs2
    have habs : |s| < η := by simpa [Real.dist_eq] using hs1
    have hk := hs s hs0 habs k
    rw [dist_comm, dist_eq_norm]
    have e : F s k = (sL R ((k : GR n) * y * f s) - sL R ((k : GR n) * y)) / s := by
      simp [hF, secK_apply, mul_assoc, div_eq_inv_mul]
    rw [e, secK_apply]
    linarith
  have hT : Filter.Tendsto F (𝓝[≠] (0:ℝ)) (𝓝 (secK hL D y)) :=
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr (fun K _ => hU.tendstoUniformlyOn)
  have hL0 : Filter.Tendsto (fun s => L (F s)) (𝓝[≠] (0:ℝ)) (𝓝 (L (secK hL D y))) :=
    (L.continuous.tendsto _).comp hT
  have hz : (fun s => L (F s)) = fun _ => (0 : ℂ) := by
    funext s
    simp only [hF, map_smul, map_sub, hR' (y * f s), hR' y, sub_self, smul_zero]
  rw [hz] at hL0
  exact tendsto_nhds_unique hL0 tendsto_const_nhds

theorem t_ne (hL : LocData ε c t p q e sL ρ) : t ≠ 0 := by
  intro h0
  have hc := hL.cpos
  rcases hL.sign with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

def lin (Φ : Fin n → Fin n → PX m n) (H : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, C (H i j) * Φ j i

theorem lin_add (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H + H') = lin Φ H + lin Φ H' := by
  simp only [lin, Matrix.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem lin_sub (Φ : Fin n → Fin n → PX m n) (H H' : Matrix (Fin n) (Fin n) ℂ) : lin Φ (H - H') = lin Φ H - lin Φ H' := by
  simp only [lin, Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lin_smul (Φ : Fin n → Fin n → PX m n) (z : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) : lin Φ (z • H) = z • lin Φ H := by
  simp only [lin, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem lin_single (Φ : Fin n → Fin n → PX m n) (a b : Fin n) :
    lin Φ (Matrix.single a b (1 : ℂ)) = Φ b a := by
  classical
  simp [lin, Matrix.single_apply, ite_and, apply_ite C, ite_mul, Finset.sum_ite_eq]

theorem herm1 (a b : Fin n) : (Matrix.single a b (1 : ℂ) + Matrix.single b a 1).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one, add_comm]

theorem herm2 (a b : Fin n) : (Complex.I • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)).IsHermitian := by
  show (_ : Matrix (Fin n) (Fin n) ℂ)ᴴ = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
    star_one, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem entry_of_lin (S : Submodule ℂ (PX m n)) (Φ : Fin n → Fin n → PX m n) (R : PX m n)
    (h : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin Φ H * R ∈ S) (a b : Fin n) :
    Φ b a * R ∈ S := by
  have h1 := h _ (herm1 a b)
  have h2 := h _ (herm2 a b)
  rw [lin_add, lin_single, lin_single] at h1
  rw [lin_smul, lin_sub, lin_single, lin_single] at h2
  have hI : (-(Complex.I / 2)) * Complex.I = (1 / 2 : ℂ) := by
    rw [neg_mul, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have h3 : Φ b a * R = (1 / 2 : ℂ) • ((Φ b a + Φ a b) * R) + (-(Complex.I / 2)) • ((Complex.I • (Φ b a - Φ a b)) * R) := by
    rw [smul_mul_assoc, smul_smul, hI, add_mul, sub_mul]
    module
  rw [h3]
  exact S.add_mem (S.smul_mem _ h1) (S.smul_mem _ h2)

theorem mon_le_adjoin (ε : Fin m → Bool) (d : ℕ) {R : PX m n} (hR : R ∈ Mon ε d) :
    R ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have hle : Mon ε d ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n))) := by
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    apply Subalgebra.list_prod_mem
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact Algebra.subset_adjoin ⟨k, rfl⟩
  exact hle hR

theorem gen_mul_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer) (d : ℕ)
    (hd : Mon ε d ≤ Ann hL L) {R : PX m n} (hR : R ∈ Mon ε d) (k : Bool × Fin n × Fin n) :
    gen ε k * R ∈ Ann hL L := by
  have hRA : R ∈ Ann hL L := hd hR
  have hRad := mon_le_adjoin ε d hR
  have hN : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qp ε j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDN : DN ε t H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).1)
    have ht : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (t_ne hL))
    have e1 : lin (fun j i => Qp ε j i) H * R = (Complex.I * (t : ℂ))⁻¹ • DN ε t H R := by
      rw [lin, DN, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ hDN
  have hM : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → lin (fun j i => Qb ε true j i + Qb ε false j i) H * R ∈ Ann hL L := by
    intro H hH
    have hDM : DM ε c H R ∈ Ann hL L :=
      ann_of_quot hL L hRA (fun y => (hD m n ε c t p q e sL ρ hL R hRad y H hH).2)
    have hE : eulH H R ∈ Ann hL L := hd (eulH_mon ε H d hR)
    have hc : (2 * (c : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hL.cpos.ne')
    have e1 : lin (fun j i => Qb ε true j i + Qb ε false j i) H * R
        = (2 * (c : ℂ))⁻¹ • (((m : ℂ) * H.trace) • R + eulH H R - DM ε c H R) := by
      rw [lin, DM, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, sub_sub_cancel, ← mul_assoc, ← mul_assoc,
        ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [e1]
    exact (Ann hL L).smul_mem _ ((Ann hL L).sub_mem ((Ann hL L).add_mem ((Ann hL L).smul_mem _ hRA) hE) hDM)
  obtain ⟨b, i, j⟩ := k
  have hP := entry_of_lin (Ann hL L) (fun j i => Qp ε j i) R hN j i
  have hS := entry_of_lin (Ann hL L) (fun j i => Qb ε true j i + Qb ε false j i) R hM j i
  have hsum := (Ann hL L).add_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  have hdif := (Ann hL L).sub_mem ((Ann hL L).smul_mem (1 / 2 : ℂ) hS) ((Ann hL L).smul_mem (1 / 2 : ℂ) hP)
  cases b
  · convert hdif using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module
  · convert hsum using 1
    simp only [gen, Qp, add_mul, sub_mul]
    module

theorem mon_le_ann (hL : LocData ε c t p q e sL ρ) (L : C(KR n, ℂ) →L[ℂ] ℂ) (hD : SecDer)
    (h1 : (1 : PX m n) ∈ Ann hL L) : ∀ d, Mon ε d ≤ Ann hL L := by
  intro d
  induction d with
  | zero =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    have hl0 : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hl0
    simpa using h1
  | succ d ih =>
    unfold Mon
    rw [Submodule.span_le]
    rintro M ⟨l, hl, rfl⟩
    cases l with
    | nil => simpa using h1
    | cons a l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
      rw [List.map_cons, List.prod_cons]
      have hM : (List.map (gen ε) l).prod ∈ Mon ε d := Submodule.subset_span ⟨l, hl, rfl⟩
      exact gen_mul_ann hL L hD d ih hM a

end PositivityTheory.Rg.Sw.AbsSt.CycP

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.CycP

theorem cycSec_of (hC : Cyc) (hZ : SecZero) (hD : SecDer) : CycSec := by
  intro m n ε c t p q e sL ρ hL L hL0 P h hh
  have h1 : (1 : PX m n) ∈ Ann hL L := by
    intro y
    refine hL0 y _ fun k => ?_
    simp [hL.vac]
  obtain ⟨R, hR, hPR⟩ := hC m n ε c hL.cpos P
  obtain ⟨d, hd⟩ := adjoin_le ε hR
  have hRA := mon_le_ann hL L hD h1 d hd
  have hz := (hZ m n ε c t p q e sL ρ hL (P - R)).1 hPR
  have : h = secK hL R 1 := by
    ext k
    have := hz (k : GR n)
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at this
    rw [hh, secK_apply, mul_one, this]
  rw [this]
  exact hRA 1

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell
section
noncomputable section

open Matrix Set Filter Topology Polynomial
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

def nbU (l : ℝ) : GL (Fin n ⊕ Fin n) ℂ where
  val := fromBlocks 1 0 ((l : ℂ) • 1) 1
  inv := fromBlocks 1 0 (-((l : ℂ) • 1)) 1
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

theorem nbU_mem (l : ℝ) : nbU (n := n) l ∈ GR n := by
  change InG (fromBlocks 1 0 ((l : ℂ) • 1) 1)
  simp only [InG, JJ, fromBlocks_conjTranspose, fromBlocks_multiply]
  congr 1 <;> simp [Matrix.smul_eq_diagonal_mul]

def nbG (l : ℝ) : GR n := ⟨nbU l, nbU_mem l⟩

theorem nbG_zero : nbG (n := n) 0 = 1 := by
  apply ext_mR
  show fromBlocks 1 0 (((0 : ℝ) : ℂ) • 1) 1 = 1
  simp [fromBlocks_one]

theorem cont_nbG : Continuous (nbG (n := n)) := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun l : ℝ => (fromBlocks 1 0 ((l : ℂ) • 1) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop
  · show Continuous fun l : ℝ => (fromBlocks 1 0 (-((l : ℂ) • 1)) 1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp <;> fun_prop

theorem nbG_low (l : ℝ) (y : GR n) :
    (mR (nbG l * y)).toBlocks₂₁ = (l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁ := by
  have hm : mR (nbG l * y) = fromBlocks 1 0 ((l : ℂ) • 1) 1 * mR y := rfl
  rw [hm]
  conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
  rw [fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem det_I (y : GR n) : (Complex.I • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let v : Fin n ⊕ Fin n → ℂ := Sum.elim x 0
  have hYv : mR y *ᵥ v = Sum.elim ((mR y).toBlocks₁₁ *ᵥ x) ((mR y).toBlocks₂₁ *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks (mR y)]
    rw [fromBlocks_mulVec]
    simp [v]
  have hCx : (mR y).toBlocks₂₁ *ᵥ x = -(Complex.I • ((mR y).toBlocks₁₁ *ᵥ x)) := by
    rw [add_mulVec, smul_mulVec] at hx
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hy : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hform : star (mR y *ᵥ v) ⬝ᵥ (JJ n *ᵥ (mR y *ᵥ v)) = 0 := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.mul_assoc, hy,
      ← dotProduct_mulVec]
    simp [v, JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  rw [hYv, hCx] at hform
  simp [JJ, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] at hform
  set u := (mR y).toBlocks₁₁ *ᵥ x with hu
  simp only [neg_mulVec, Pi.neg_apply] at hform
  have h3 : (-2 * Complex.I) * ∑ i, starRingEnd ℂ (u i) * u i = 0 := by
    rw [← hform, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : ∑ i, starRingEnd ℂ (u i) * u i = 0 :=
    (mul_eq_zero.mp h3).resolve_left (by simp [Complex.I_ne_zero])
  have hu0 : u = 0 := by
    rw [← dotProduct_star_self_eq_zero]
    simpa [dotProduct] using h2
  have hYv0 : mR y *ᵥ v = 0 := by
    rw [hYv, hCx, hu0]
    ext i
    rcases i with i | i <;> simp
  have hinv : mR y⁻¹ * mR y = 1 := congrArg mR (inv_mul_cancel y)
  have hv : v = 0 := by
    rw [← one_mulVec v, ← hinv, ← mulVec_mulVec, hYv0, mulVec_zero]
  apply hx0
  funext i
  exact congrFun hv (Sum.inl i)

theorem finite_bad (y : GR n) :
    {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0}.Finite := by
  let M : Matrix (Fin n) (Fin n) ℂ[X] :=
    (X : ℂ[X]) • (mR y).toBlocks₁₁.map (Polynomial.C : ℂ →+* ℂ[X]) + (mR y).toBlocks₂₁.map (Polynomial.C : ℂ →+* ℂ[X])
  let p : ℂ[X] := M.det
  have hev : ∀ z : ℂ, p.eval z = (z • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det := by
    intro z
    have h := RingHom.map_det (Polynomial.evalRingHom z) M
    rw [Polynomial.coe_evalRingHom] at h
    rw [h]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : p ≠ 0 := by
    intro h0
    apply det_I y
    rw [← hev, h0, Polynomial.eval_zero]
  apply (p.roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset
  intro l hl
  simp only [Set.mem_setOf_eq] at hl
  rw [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact (hev _).trans hl

theorem dense_cell : Dense {y : GR n | (mR y).toBlocks₂₁.det ≠ 0} := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y
  have hS := finite_bad y
  set S := {l : ℝ | ((l : ℂ) • (mR y).toBlocks₁₁ + (mR y).toBlocks₂₁).det = 0} with hSdef
  have hT : (S \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    (hS.diff (s := S) (t := {0})).isClosed.isOpen_compl.mem_nhds (by simp)
  have hcont : Continuous fun t : ℝ => nbG (n := n) t * y := cont_nbG.mul continuous_const
  have htend : Tendsto (fun t : ℝ => nbG (n := n) t * y) (𝓝[≠] 0) (𝓝 y) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    simpa [nbG_zero] using h
  apply mem_closure_of_tendsto htend
  filter_upwards [nhdsWithin_le_nhds hT, self_mem_nhdsWithin] with t h1 h2
  simp only [Set.mem_setOf_eq, nbG_low]
  intro hdet
  exact h1 ⟨hdet, h2⟩

end PositivityTheory.Rg.Sw.AbsSt.DF
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

def hz {m n : ℕ} {G : Type} (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (Q : PX m n) (x : G) : ℂ :=
  ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec Q x

def FarRight : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (c t : ℝ) (p q : ℕ) (e : ℤ) (sL : PX m n →ₗ[ℂ] (GR n → ℂ))
    (ρ : GR n → PX m n →ₗ[ℂ] PX m n), LocData ε c t p q e sL ρ →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0)
      (sec I : PX m n →ₗ[ℂ] (G → ℂ)) (Λ : Set ((G → ℂ) → ℂ)), GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ →
      ∃ σ : ℝ, (∀ Q g, DifferentiableOn ℂ (fun z => GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z Q) g) (GlobalTheory.Cont.rightOf σ)) ∧
        (∀ Q g (z : ℂ), σ < z.re → Summable fun q => GlobalTheory.Eis.term Pp Γ (hz Ht sec s₀ z Q) g q) ∧
        ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (ν : Measure (KR n)) (κ : KR n → ℂ) (N : ℕ) (yy : Fin N → GR n)
          (QQ : Fin N → PX m n) (M : ℂ → Matrix (Fin N) (Fin N) ℂ), IsFiniteMeasure ν → Continuous κ →
          (∀ (w : ℂ) (i : Fin N) (y' : GR n), ∫ k, κ k * ((hLoc (y' * (k : GR n) * yy i) : ℂ) ^ w *
              F0 p q e (y' * (k : GR n) * yy i)) ∂ν = (hLoc y' : ℂ) ^ w * ∑ j, M w i j * sL (QQ j) y') →
          ∀ (z : ℂ), σ < z.re → ∀ (g : G) (i : Fin N),
            ∫ k, κ k * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z 1) (g * ι ((k : GR n) * yy i)) ∂ν =
              ∑ j, M (z - s₀) i j * GlobalTheory.Eis.cosetSum Pp Γ (hz Ht sec s₀ z (QQ j)) g

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerMSt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SDM

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ}

def mulR (A : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ := fun a j => ∑ i, y a i * A i j

def aE (H : Matrix (Fin n) (Fin n) ℂ) (σ : ℝ) : Matrix (Fin n) (Fin n) ℂ := NormedSpace.exp ((σ : ℂ) • H)

def DMp (ε : Fin m → Bool) (c : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (R : PX m n) : PX m n :=
  eulH H R - MvPolynomial.C (2 * (c : ℂ)) *
    (∑ i, ∑ j, MvPolynomial.C (H i j) * (Qb ε true j i + Qb ε false j i)) * R

def CellM : Prop := ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.IsHermitian → ∀ f : ℝ → GR n,
  (∀ σ : ℝ, mR (f σ) = fromBlocks (NormedSpace.exp ((σ : ℂ) • H)) 0 0 (NormedSpace.exp (-((σ : ℂ) • H)))) →
  ∀ g : GR n, (mR g).toBlocks₂₁.det ≠ 0 → ∃ (y₁ : GR n) (b : Matrix (Fin n) (Fin n) ℂ), IsUp y₁ ∧ b.IsHermitian ∧
    ∀ (p q : ℕ) (e : ℤ) (σ : ℝ), ∃ (mA w : GR n), IsUp mA ∧
      F0 p q e mA = Complex.exp (-((σ : ℂ) * ((p + q : ℕ) : ℂ) * H.trace)) ∧
      mR w = JJ n * nU (aE H (-σ) * b * aE H (-σ)) ∧ (aE H (-σ) * b * aE H (-σ)).IsHermitian ∧
      g * f σ = y₁ * mA * w

def CoV : Prop := ∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.det ≠ 0 → ∀ F : (Fin m → Fin n → ℂ) → ℂ,
  ∫ x, F x = ((Complex.normSq A.det ^ m : ℝ) : ℂ) * ∫ y, F (mulR A y)

end PositivityTheory.Rg.Sw.AbsSt.SDM
end
end

