module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.DetOneAddSmulSingleSame
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInv
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eA_comm {n : ℕ} (a b : Fin n) : eA a b * JJ n = JJ n * eA a b := by
  simp [eA, JJ, Matrix.fromBlocks_multiply]

theorem eB_comm {n : ℕ} (a b : Fin n) : eB a b * JJ n = JJ n * eB a b := by
  simp [eB, JJ, Matrix.fromBlocks_multiply]

theorem infInv_of (hL : LeftDeriv) (hP : LawDeriv) (hI : PtId) (hC : CDiff) : InfInv := by
  intro n F1 F2 Ω hΩ hGΩ hF1 hF2 hlaw Kg _ _ _ _ _ _ μ _ ι hι hK Z
  have hΘc : ContDiffOn ℂ ∞ (fun y => F1 y * F2 y) Ω := hF1.mul hF2
  have hKk : ∀ k : Kg, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hmem : ∀ k : Kg, ι k ∈ Ω := fun k => hGΩ (hKk k).1
  have hlawΘ := hP n (fun y => F1 y * F2 y) Ω hΩ hGΩ (hΘc.differentiableOn (by simp))
    (fun p x hp hp0 hx => hlaw p x hp hp0 hx)
  have hU : KSet n ⊆ Ω := fun g hg => hGΩ hg.1
  have hcd : ∀ c : M2 n → ℂ, ContDiff ℝ ∞ c →
      ContDiffOn ℝ 1 (fun y => c y * (F1 y * F2 y)) Ω := fun c hc =>
    (hc.contDiffOn.mul (hΘc.restrict_scalars ℝ)).of_le (by simp)
  have hA : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b)) μ ∧
      ∫ k, dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).1) (eA a b) (eA_comm a b)
  have hB : ∀ a b : Fin n, Integrable (fun k => dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) μ ∧
      ∫ k, dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b) ∂μ = 0 := fun a b =>
    hL n Kg μ ι hι hK _ Ω hΩ hU (hcd _ (hC n Z a b).2) (eB a b) (eB_comm a b)
  have key : ∀ k : Kg, fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) =
      ∑ a : Fin n, ∑ b : Fin n, (dK (fun y => cA Z a b y * (F1 y * F2 y)) (ι k) (eA a b) +
        dK (fun y => cB Z a b y * (F1 y * F2 y)) (ι k) (eB a b)) := by
    intro k
    have hnh : Ω ∈ nhds (ι k) := hΩ.mem_nhds (hmem k)
    have hd1 : DifferentiableAt ℂ F1 (ι k) :=
      ((hF1.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hd2 : DifferentiableAt ℂ F2 (ι k) :=
      ((hF2.differentiableOn (by simp)) _ (hmem k)).differentiableAt hnh
    have hprod : fderiv ℂ (fun y => F1 y * F2 y) (ι k) (ι k * Z) =
        fderiv ℂ F1 (ι k) (ι k * Z) * F2 (ι k) + F1 (ι k) * fderiv ℂ F2 (ι k) (ι k * Z) := by
      have h : HasFDerivAt (fun y => F1 y * F2 y)
          (F1 (ι k) • fderiv ℂ F2 (ι k) + F2 (ι k) • fderiv ℂ F1 (ι k)) (ι k) :=
        hd1.hasFDerivAt.mul hd2.hasFDerivAt
      rw [h.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [← hprod]
    exact hI n (fun y => F1 y * F2 y) (ι k) Z (hKk k) ((hΘc.contDiffAt hnh).of_le (by simp))
      (fun Y hY => hlawΘ (ι k) (hKk k).1 Y hY)
  simp_rw [key]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [integral_add (hA a b).1 (hB a b).1, (hA a b).2, (hB a b).2, add_zero]
    · intro b _
      exact (hA a b).1.add (hB a b).1
  · intro a _
    exact MeasureTheory.integrable_finsetSum _ (fun b _ => (hA a b).1.add (hB a b).1)

end PositivityTheory.Rg.Sw.LVs.II

namespace PositivityTheory.Rg.Sw.LVs

theorem infInv : InfInv := II.infInv_of II.leftDeriv II.lawDeriv II.ptId II.cDiff

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffC
section
noncomputable section

open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw

namespace STD

variable {n : ℕ}

theorem dc_comp {Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ} {x : Vr n} (hΨ : DifferentiableAt ℂ Ψ (herm x))
    (a : Fin n × Fin n) :
    dc a (fun y => Ψ (herm y)) x = fderiv ℂ Ψ (herm x) (Matrix.single a.1 a.2 1) := by
  have hd : HasFDerivAt (fun y => Ψ (hermL n y)) (((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n)) x :=
    (hΨ.hasFDerivAt.restrictScalars ℝ).comp x (hermL n).hasFDerivAt
  have hf : fderiv ℝ (fun y => Ψ (herm y)) x = ((fderiv ℂ Ψ (herm x)).restrictScalars ℝ).comp (hermL n) :=
    hd.fderiv
  simp only [dc, hf, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', hermL_apply]
  rw [← herm_v, map_add (f := _), map_smul, smul_eq_mul]

theorem dList_ofFn {r : ℝ} {G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hG : ContDiffOn ℂ ∞ G (Metric.ball 0 r)) :
    ∀ (k : ℕ) (m : Fin k → Fin n × Fin n) (x : Vr n), herm x ∈ Metric.ball 0 r →
      dList (List.ofFn m) (fun y => G (herm y)) x =
        iteratedFDeriv ℂ k G (herm x) (fun i => Matrix.single (m i).1 (m i).2 1)
  | 0, m, x, _ => by simp [dList]
  | k + 1, m, x, hx => by
    have hU : IsOpen ((hermL n) ⁻¹' Metric.ball 0 r) := Metric.isOpen_ball.preimage (hermL n).continuous
    let V : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ := fun i => Matrix.single (m i).1 (m i).2 1
    let Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun H => iteratedFDeriv ℂ k G H (Fin.tail V)
    have hIt : DifferentiableOn ℂ (fun H => iteratedFDeriv ℂ k G H) (Metric.ball 0 r) := by
      have hWithin := hG.differentiableOn_iteratedFDerivWithin (m := k)
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
        Metric.isOpen_ball.uniqueDiffOn
      exact hWithin.congr (fun H hH => (iteratedFDerivWithin_of_isOpen k Metric.isOpen_ball hH).symm)
    have hItx : DifferentiableAt ℂ (iteratedFDeriv ℂ k G) (herm x) :=
      (hIt _ hx).differentiableAt (Metric.isOpen_ball.mem_nhds hx)
    have hΨd : DifferentiableAt ℂ Ψ (herm x) := hItx.continuousMultilinear_apply_const (Fin.tail V)
    have heq : dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y)) =ᶠ[𝓝 x] fun y => Ψ (herm y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact dList_ofFn hG k (fun i => m i.succ) y hy
    rw [List.ofFn_succ]
    simp only [dList]
    have h1 : dc (m 0) (dList (List.ofFn fun i : Fin k => m i.succ) (fun y => G (herm y))) x =
        dc (m 0) (fun y => Ψ (herm y)) x := by
      simp only [dc, heq.fderiv_eq]
    rw [h1, dc_comp hΨd]
    exact (hItx.iteratedFDeriv_succ_apply_left' (m := V)).symm

end STD

end PositivityTheory.Rg.Sw.LVs
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockC
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def eBq (j : ℕ) : {x // x ∈ blkB (n := n) j} ≃ {x // ¬ x ∈ blkA (n := n) j} :=
  Equiv.subtypeEquivRight (fun x => mem_blkB j x)

def piP (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) : Equiv.Perm (Fin n) :=
  Equiv.Perm.subtypeCongr σA ((eBq j).permCongr τ)

end PositivityTheory.Rg.Sw.LVs.TC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCHeights
section
noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end PositivityTheory.Rg.Sw.LVs.TC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB
section
noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by
  unfold InG at *
  rw [conjTranspose_mul, show hᴴ * gᴴ * JJ n * (g * h) = hᴴ * (gᴴ * JJ n * g) * h by simp only [Matrix.mul_assoc], hg, hh]

theorem inG_left_inv {g : M2 n} (hg : InG g) : (-(JJ n) * gᴴ * JJ n) * g = 1 := by
  unfold InG at hg
  rw [show -(JJ n) * gᴴ * JJ n * g = -(JJ n) * (gᴴ * JJ n * g) by simp only [Matrix.mul_assoc], hg, neg_mul, jj_mul_jj,
    neg_neg]

theorem inG_mul_inv {g : M2 n} (hg : InG g) : g * g⁻¹ = 1 := by
  rw [Matrix.inv_eq_left_inv (inG_left_inv hg)]
  exact mul_eq_one_comm.1 (inG_left_inv hg)

theorem inG_inv {g : M2 n} (hg : InG g) : InG g⁻¹ := by
  have h1 := inG_mul_inv hg
  unfold InG at *
  calc (g⁻¹)ᴴ * JJ n * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * JJ n * g) * g⁻¹ := by rw [hg]
    _ = (g * g⁻¹)ᴴ * JJ n * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [h1]; simp

theorem mul_compl_zero (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ) (hQ : ∀ a b, Q a b ≠ 0 → b ∈ blkA j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j) : Q * S = 0 :=
  _root_.UpperTheory.Reformulated.B.Yha8.main j Q S hQ hS

theorem mX_factor (j : ℕ) (P Q R S : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ a b, P a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkB j)
    (hS : ∀ a b, S a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkA j) (hQ : ∀ a b, Q a b ≠ 0 → a ∈ blkA j ∧ b ∈ blkA j)
    (hR : ∀ a b, R a b ≠ 0 → a ∈ blkB j ∧ b ∈ blkB j) :
    mX (1 + P) Q R (1 + S) = mX 1 Q R 1 * mX (1 + P) 0 0 (1 + S) := by
  have hQS : Q * S = 0 := mul_compl_zero j Q S (fun a b h => (hQ a b h).2) (fun a b h => (hS a b h).1)
  have hRP : R * P = 0 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hr : R a k = 0
    · simp [hr]
    by_cases hp : P k b = 0
    · simp [hp]
    exact absurd (hP k b hp).1 (by have := (hR a k hr).2; simp [blkB] at this; exact this)
  unfold mX
  rw [cm_inv, show Cm n * fromBlocks 1 Q R 1 * CmI n * (Cm n * fromBlocks (1 + P) 0 0 (1 + S) * CmI n) =
      Cm n * (fromBlocks 1 Q R 1 * (CmI n * Cm n) * fromBlocks (1 + P) 0 0 (1 + S)) * CmI n by
        simp only [Matrix.mul_assoc], cmI_mul_cm, Matrix.mul_one, fromBlocks_multiply]
  simp [Matrix.mul_add, hQS, hRP]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

