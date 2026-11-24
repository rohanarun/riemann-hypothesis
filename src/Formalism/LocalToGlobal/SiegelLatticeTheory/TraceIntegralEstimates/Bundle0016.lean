module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0015
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0023
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSWire
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.S.Pv.HaarSubS

theorem hform_crdX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  unfold Formalism.UG.hform crdOf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  have hst : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  simp only [hst]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_eqX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) =
      X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frameRelX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    PI.NMeasInv.FrameRel X.B.I X.eR X.fR (X.zR u) := by
  have h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) =
      X.ιE.symm ((VS D).hT v w) := fun v w => hform_eqX X v w
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [h, X.ee, map_zero]
  · rw [h, X.ff, map_zero]
  · rw [h, X.ef]
    split_ifs <;> simp
  · rw [h, (X.zu_orth u a).1, map_zero]
  · rw [h, (X.zu_orth u a).2, map_zero]
  · rw [h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact (D.mem u).A.T_prime.ne_zero

theorem measN_holds : MeasN := by
  obtain ⟨h1, h2, h3, h4⟩ := PI.n_measure_invariant
  intro D X u
  have hF := frameRelX X u
  have hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u) := X.muN_haar u
  exact ⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩

theorem nuQSFinite_holds : NuQSFinite := by
  intro D X u
  haveI : SigmaFinite (X.nuQ u) :=
    quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u)
      (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)
  infer_instance

theorem stepSubG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := stepSubG_of_MN measN_holds nuQSFinite_holds

end Formalism.L2.S.Pv.HaarSubS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.StCoordVCoef
section
noncomputable section

open scoped Matrix
open Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_conj {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem blkOf_mono {K : Type*} : ∀ (l : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf l i ≤ blkOf l j
  | [], _, _, _ => le_rfl
  | (x, s) :: bs, i, j, h => by
    unfold blkOf
    by_cases hi : i < s
    · rw [if_pos hi]; exact Nat.zero_le _
    · have hj : ¬ j < s := fun hj => hi (lt_of_le_of_lt h hj)
      rw [if_neg hi, if_neg hj]
      exact Nat.succ_le_succ (blkOf_mono bs (i - s) (j - s) (Nat.sub_le_sub_right h s))

variable {D : D7} {w : Point D.host.E (D.R.rS + 1)}

theorem blk_mid (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) :
    blkOf w.1 p.1.1.1 = blkOf w.1 c.1 ∧ blkOf w.1 c.1 = blkOf w.1 p.1.2.1 := by
  have h1 := blkOf_mono w.1 p.1.1.1 c.1 (le_of_lt h.1)
  have h2 := blkOf_mono w.1 c.1 p.1.2.1 (le_of_lt h.2)
  have h3 := p.2.2
  omega

def midL (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(p.1.1, c), h.1, (blk_mid p c h).1⟩

def midR (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(c, p.1.2), h.2, (blk_mid p c h).2⟩

def BX (p : FreeE w) (x y : FreeE w → ℂ) : ℂ :=
  ∑ c : Fin (D.R.rS + 1), if h : p.1.1 < c ∧ c < p.1.2 then x (midL p c h) * y (midR p c h) else 0

theorem BX_zero (p : FreeE w) (x : FreeE w → ℂ) : BX p x 0 = 0 := by
  unfold BX; simp

theorem BX_lower (p : FreeE w) (x x' y y' : FreeE w → ℂ)
    (h : ∀ q : FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q ∧ y q = y' q) :
    BX p x y = BX p x' y' := by
  unfold BX
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 := h (midL p c hc) (by
      simp only [midL]; have := hc.1; have := hc.2
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    have h2 := h (midR p c hc) (by
      simp only [midR]
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    rw [h1.1, h2.2]
  · rfl

theorem BX_measurable (p : FreeE w) : Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2) := by
  unfold BX
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs with hc
  · exact ((measurable_pi_apply _).comp measurable_fst).mul ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

section Law

variable (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

theorem dual_v (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_conj, show X.eR b = X.crd (X.eX b) from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ef]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero, star_zero]

theorem fz_v (u' : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) = 0 := by
  rw [show X.zR u' = X.crd (X.zu u') from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u' a).2, map_zero]

theorem ha_free (q : FreeE w) : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega

theorem stCoordV_coef (u' : D.what₂.Word) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v)) (q : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y q =
      (D.host.rdE : ℂ) ^ (D.R.rS - q.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - q.1.2.1))⁻¹ *
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR ⟨q.1.1.1, ha_free q⟩))
          (uMat ((γ v)⁻¹ * y * γ v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) q.1.2) := by
  unfold Formalism.L2.SG.NGPin.stCoordV frm famSc
  rw [Matrix.mulVec_smul, hJ_smul]
  ring

theorem stCoordV_mul {u u' : D.what₂.Word} {γ : X.B.I.Ginf} {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε v)}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (p : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v (y₁ * y₂) p =
      Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁ p + Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂ p +
        BX p (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁) (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂) := by
  have hdual := dual_v X v
  have hfz := fz_v X v u'
  have hS₁ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₁ * γ v)) := h₁.2.1
  have hS₂ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₂ * γ v)) := h₂.2.1
  have hmul : uMat ((γ v)⁻¹ * (y₁ * y₂) * γ v) = uMat ((γ v)⁻¹ * y₁ * γ v) * uMat ((γ v)⁻¹ * y₂ * γ v) := by
    rw [show (γ v)⁻¹ * (y₁ * y₂) * γ v = ((γ v)⁻¹ * y₁ * γ v) * ((γ v)⁻¹ * y₂ * γ v) by group]; rfl
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.MainNotions.S.Pv.HH.one_le_rdE D
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one this))
  have hab : (⟨p.1.1.1, ha_free p⟩ : Fin D.R.rS).1 < p.1.2.1 := p.2.1
  unfold BX
  simp only [stCoordV_coef X v u' γ]
  rw [hmul, coef_mul (X.B.I.ε v) _ _ _ hdual hfz hS₁ hS₂ ⟨p.1.1.1, ha_free p⟩ p.1.2 hab,
    Fin.sum_univ_castSucc, dite_eq_right (fun h => (not_lt.2 (Fin.le_last _)) h.2), add_zero]
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [dite_eq_left hc, if_pos ⟨hc.1, hc.2⟩]
    simp only [midL, midR]
    have e1 : fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c.castSucc = rv X.B.I v (X.eR c) := by
      unfold fam; rw [Fin.snoc_castSucc]
    rw [e1]
    simp only [Fin.val_castSucc, Fin.eta]
    have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - c.castSucc.1) ≠ 0 := pow_ne_zero _ hrd
    field_simp
  · rw [dite_eq_right hc, if_neg (fun h => hc ⟨h.1, h.2⟩), mul_zero]

end Law

end Formalism.L2.S.Pv.Chart

end
end

