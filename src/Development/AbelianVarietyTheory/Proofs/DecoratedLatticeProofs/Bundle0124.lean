module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionEqLeviUnipotentProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.TransvDec

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

def colM {n : ℕ} (a : Fin n → AE D) : Mx D n 1 := replicateCol (Fin 1) a

theorem colM_mulVec {m n : ℕ} (M : Mx D m n) (a : Fin n → AE D) : colM (M *ᵥ a) = M ⬝ colM a :=
  replicateCol_mulVec M a

theorem colM_mul {n : ℕ} (a : Fin n → AE D) (K : Mx D 1 1) : colM a ⬝ K = colM (K 0 0 • a) := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [colM, Matrix.mul_apply, mul_comm]

theorem form_eq (S : HSp D) (y v : VA S) : form S y v = (adj (colM v) ⬝ (gA S ⬝ colM y)) 0 0 := by
  rw [← colM_mulVec]; rfl

theorem ext_colM {m n : ℕ} {M N : Mx D m n} (h : ∀ y : Fin n → AE D, M ⬝ colM y = N ⬝ colM y) : M = N := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have := h (Pi.single i 1)
  rw [← colM_mulVec, ← colM_mulVec] at this
  exact funext fun k => congrFun (congrFun this k) 0

theorem mt_transv {S : HSp D} {w v : VA S} {u : GA D S} (hu : IsTransv S w v u) :
    mt S u = 1 + colM w ⬝ (adj (colM v) ⬝ gA S) - colM v ⬝ (adj (colM w) ⬝ gA S) -
      half D • (colM w ⬝ (adj (colM v) ⬝ (gA S ⬝ (colM v ⬝ (adj (colM w) ⬝ gA S))))) := by
  refine ext_colM fun y => ?_
  have h : mt S u *ᵥ y = transv S w v y := hu y
  rw [← colM_mulVec, h]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc]
  have e : (adj (colM v) ⬝ (gA S ⬝ (colM v ⬝ (adj (colM w) ⬝ (gA S ⬝ colM y))))) 0 0 = form S v v * form S y w := by
    rw [form_eq, form_eq, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (colM v)), Matrix.mul_apply,
      Fin.sum_univ_one]
  rw [colM_mul w, colM_mul w, e, colM_mul v, ← form_eq, ← form_eq]
  ext i j
  simp [colM, transv, mul_assoc]

def unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : GL (Fin ρ) (AE D) where
  val := 1 + A ⬝ adj γ
  inv := 1 - A ⬝ adj γ
  val_inv := by
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, cancel₂ h,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, add_sub_cancel_right]
  inv_val := by
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, cancel₂ h,
      Matrix.zero_mul, Matrix.mul_zero, sub_zero, sub_add_cancel]

theorem val_unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : (unip A γ h).1 = 1 + A ⬝ adj γ := rfl

theorem val_unip_inv {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : ((unip A γ h)⁻¹).1 = 1 - A ⬝ adj γ := rfl

theorem det_eq_one_of_val {R : Type} [CommRing R] {m n : ℕ} (g : GL (Fin m) R) (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) (hg : g.1 = 1 + A * B) (h : B * A = 0) : Matrix.GeneralLinearGroup.det g = 1 := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Matrix.det_one_add_mul_comm, h, add_zero, det_one, Units.val_one]

theorem det_unip {ρ : ℕ} (A γ : Mx D ρ 1) (h : adj γ ⬝ A = 0) : Matrix.GeneralLinearGroup.det (unip A γ h :) = 1 := by
  have hg := val_unip A γ h
  generalize unip A γ h = g at hg ⊢
  exact det_eq_one_of_val (R := AE D) g A (adj γ) hg h

def skewPart {ρ : ℕ} (A α γ : Mx D ρ 1) : skewA D ρ :=
  ⟨A ⬝ adj α - α ⬝ adj A + (half D • (A ⬝ (adj γ ⬝ (α ⬝ adj A))) - half D • (A ⬝ (adj α ⬝ (γ ⬝ adj A)))), by
    simp only [mem_skewA, adj_add, adj_sub, adj_smul, adj_mul, adj_adj, cA_half, Matrix.mul_assoc]
    abel⟩

theorem qS_skewPart {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A α γ : Mx D ρ 1) (T : HSp D) (x : Mx D T.rank ρ)
    (hx : x ⬝ A = 0) : d.qS T (skewPart A α γ) x = 0 := by
  have h : x ⬝ (skewPart A α γ).1 = -(x ⬝ α ⬝ adj A) := by
    simp only [skewPart, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, cancel₂ hx, Matrix.zero_mul, smul_zero,
      sub_zero, add_zero, zero_sub, Matrix.mul_assoc]
  rw [HypDec.qS, HypDec.symplOH_extX_extY, h, pairS, adj_neg, adj_mul, adj_adj, Matrix.neg_mul, trace_neg,
    Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hx, Matrix.mul_zero, Matrix.mul_zero,
    trace_zero, neg_zero, map_zero]

section Main

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {A α γ : Mx D ρ 1} {β : Mx D S₀.rank 1} (h : adj γ ⬝ A = 0)

theorem prod_jX (b : Mx D ρ S₀.rank) (c : skewA D ρ) :
    mt S (d.levi (unip A γ h) * d.nB b * d.nC c) ⬝ d.jX = d.jX + d.jX ⬝ (A ⬝ adj γ) := by
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX, val_unip, Matrix.mul_add,
    Matrix.mul_one]

theorem wittCoreColumns_transvectionLeviProduct (s : Mx D 1 S₀.rank) (c : skewA D ρ) :
    mt S (d.levi (unip A γ h) * d.nB (A ⬝ s) * d.nC c) ⬝ d.j0 = d.j0 + d.jX ⬝ (A ⬝ s) := by
  rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_j0, d.nB_j0, Matrix.mul_add, d.wittDecomp_levi_inclAnisotropic,
    cancel₂ (d.levi_jX _), val_unip, Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, cancel₂ h,
    Matrix.zero_mul, Matrix.mul_zero, add_zero]

set_option maxHeartbeats 1000000 in
theorem prod_jY :
    mt S (d.levi (unip A γ h) * d.nB (A ⬝ (adj β ⬝ gA S₀)) * d.nC (skewPart A α γ)) ⬝ d.jY =
      d.jY + d.jX ⬝ (A ⬝ adj α) - (d.jX ⬝ α + d.j0 ⬝ β + d.jY ⬝ γ) ⬝ adj A -
        half D • (d.jX ⬝ (A ⬝ ((adj γ ⬝ α + adj β ⬝ (gA S₀ ⬝ β) + adj α ⬝ γ) ⬝ adj A))) := by
  have hp : plus S₀ (A ⬝ (adj β ⬝ gA S₀)) = β ⬝ adj A := by
    simp only [plus, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel]
  have hh := half_smul_add (d.jX ⬝ (A ⬝ (adj γ ⬝ (α ⬝ adj A))))
  have hm := val_unip A γ h
  have hm' := val_unip_inv A γ h
  generalize unip A γ h = g at hm hm' ⊢
  simp only [mt_mul, Matrix.mul_assoc, d.nC_jY, Matrix.mul_add, d.nB_jY, cancel₂ (d.nB_jX _), hp,
    Matrix.mul_sub, d.levi_jY, cancel₂ (d.wittDecomp_levi_inclAnisotropic _), cancel₂ (d.levi_jX _)]
  rw [hm, hm']
  simp only [skewPart, adj_sub, adj_mul, adj_adj, adj_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_smul, smul_add, smul_zero, Matrix.mul_assoc, cancel₂ h,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, sub_zero, zero_add]
  generalize half D • (d.jX ⬝ (A ⬝ (adj γ ⬝ (α ⬝ adj A)))) = t at hh ⊢
  rw [← hh]
  abel

end Main


set_option maxHeartbeats 1000000 in
theorem eq_levi_nB_nC {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A : Mx D ρ 1) (V : Mx D S.rank 1)
    (h : adj (d.pY ⬝ V) ⬝ A = 0) (u : GA D S)
    (hu : mt S u = 1 + d.jX ⬝ A ⬝ (adj V ⬝ gA S) - V ⬝ (adj (d.jX ⬝ A) ⬝ gA S) -
      half D • (d.jX ⬝ A ⬝ (adj V ⬝ (gA S ⬝ (V ⬝ (adj (d.jX ⬝ A) ⬝ gA S)))))) :
    u = d.levi (unip A (d.pY ⬝ V) h) * d.nB (A ⬝ (adj (d.p0 ⬝ V) ⬝ gA S₀)) *
      d.nC (skewPart A (d.pX ⬝ V) (d.pY ⬝ V)) := by
  have hV : d.jX ⬝ (d.pX ⬝ V) + d.j0 ⬝ (d.p0 ⬝ V) + d.jY ⬝ (d.pY ⬝ V) = V := by
    simp only [← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.add_mul, d.sum_eq_one, Matrix.one_mul]
  have hX : adj V ⬝ (gA S ⬝ d.jX) = adj (d.pY ⬝ V) := by
    rw [d.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  have hY : adj V ⬝ (gA S ⬝ d.jY) = adj (d.pX ⬝ V) := by
    rw [d.pX_eq, adj_mul, adj_mul, adj_adj, adj_gA]
  have h0 : adj V ⬝ (gA S ⬝ d.j0) = adj (d.p0 ⬝ V) ⬝ gA S₀ := by
    simp only [d.p0_eq, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one]
  have hK : adj (d.pY ⬝ V) ⬝ (d.pX ⬝ V) + adj (d.p0 ⬝ V) ⬝ (gA S₀ ⬝ (d.p0 ⬝ V)) + adj (d.pX ⬝ V) ⬝ (d.pY ⬝ V) =
      adj V ⬝ (gA S ⬝ V) := by
    rw [← cancel₃ hX, ← cancel₃ hY, ← Matrix.mul_assoc (adj (d.p0 ⬝ V)), ← cancel₃ h0, ← Matrix.mul_add,
      ← Matrix.mul_add, ← Matrix.mul_add, ← Matrix.mul_add, hV]
  have hP : adj (d.jX ⬝ A) ⬝ gA S = adj A ⬝ d.pY := by rw [d.pY_eq, adj_mul, Matrix.mul_assoc]
  simp only [hP] at hu
  refine d.ga_ext ?_ ?_ ?_
  · rw [prod_jX, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_jX, hX,
      Matrix.mul_zero, Matrix.one_mul, smul_zero, sub_zero]
  · rw [wittCoreColumns_transvectionLeviProduct, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_j0, h0,
      Matrix.mul_zero, Matrix.one_mul, smul_zero, sub_zero]
  · rw [prod_jY, hV, hK, hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc, d.pY_jY, hY, Matrix.one_mul,
      Matrix.mul_one]

end GlobalTheory.Unf.TransvDec

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction TransvDec

theorem transv_eq_levi_nB_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA S), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form S (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d a) v = 0 → ∀ u : GA D S, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv S (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d a) v u → ∃ (m : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank) (c : skewA D ρ), u = d.levi m * d.nB b * d.nC c ∧ Matrix.GeneralLinearGroup.det m = 1 ∧ ∀ (T : HSp D) (x : Mx D T.rank ρ), x *ᵥ a = 0 → x ⬝ m.1 = x ∧ x ⬝ b = 0 ∧ d.qS T c x = 0 := by
  intro D S S₀ ρ d a v hv u hu
  have hw : colM (vecX d a) = d.jX ⬝ colM a := colM_mulVec _ _
  have h : adj (d.pY ⬝ colM v) ⬝ colM a = 0 := by
    rw [form_eq, hw] at hv
    rw [d.pY_eq, adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, Matrix.mul_assoc]
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    exact hv
  have hm := mt_transv hu
  rw [hw] at hm
  refine ⟨_, _, _, eq_levi_nB_nC d (colM a) (colM v) h u hm, det_unip _ _ h, fun T x hx => ?_⟩
  have hx' : x ⬝ colM a = 0 := by
    rw [← colM_mulVec, hx]; rfl
  refine ⟨?_, ?_, qS_skewPart d _ _ _ T x hx'⟩
  · change x ⬝ (1 + colM a ⬝ adj (d.pY ⬝ colM v)) = x
    rw [Matrix.mul_add, Matrix.mul_one, cancel₂ hx', Matrix.zero_mul, add_zero]
  · rw [cancel₂ hx', Matrix.zero_mul]

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvAdelic

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec, mt_unitary, form]

theorem unitary_of_form (S : HSp D) (M : Mx D S.rank S.rank)
    (h : ∀ x y, form S (M *ᵥ x) (M *ᵥ y) = form S x y) : adj M * (gA S * M) = gA S := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  have e : (fun k => cA D ((Pi.single i 1 : VA S) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [form_mulVec, form, e] at this
  simpa using this

theorem form_vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) :
    form S (vecX d a) (vecX d a) = 0 := by
  rw [vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

@[reducible] def starRingA (D : D7) : StarRing (AE D) where
  star := cA D
  star_involutive := cA_cA
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add (cA D)

@[reducible] def invTwo (D : D7) : Invertible (2 : AE D) where
  invOf := half D
  invOf_mul_self := by rw [mul_two, half_add_half]
  mul_invOf_self := by rw [two_mul, half_add_half]

theorem form_transv (S : HSp D) (w v : VA S) (hw : form S w w = 0) (hv : form S w v = 0) (x y : VA S) :
    form S (transv S w v x) (transv S w v y) = form S x y := by
  letI := starRingA D
  letI := invTwo D
  exact (GlobalTheory.eichlerTransvection_unitary_inverse_conj (AE D) (Fin S.rank) (gA S) (adj_gA S) (form S)
    (fun _ _ => rfl) (transv S) (fun _ _ _ => rfl)).1 w v hw hv x y

def transvLin (S : HSp D) (w v : VA S) : VA S →ₗ[AE D] VA S where
  toFun := transv S w v
  map_add' x y := by
    funext i
    simp only [transv, form, Matrix.mulVec_add, dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' s x := by
    funext i
    simp only [transv, form, Matrix.mulVec_smul, dotProduct_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem toMatrix_transvLin (S : HSp D) (w v y : VA S) :
    LinearMap.toMatrix' (transvLin S w v) *ᵥ y = transv S w v y := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem act_transv (S : HSp D) (g : GA D S) (w v y : VA S) :
    act S g (transv S w v y) = transv S (act S g w) (act S g v) (act S g y) := by
  rw [transv, transv, form_act, form_act, form_act]
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem act_mul (S : HSp D) (g h : GA D S) (y : VA S) : act S (g * h) y = act S g (act S h y) := by
  rw [act, act, act, mt_mul, Matrix.mulVec_mulVec]

theorem transv_unitary_conj :
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  intro D
  refine ⟨fun S S₀ ρ d a v hv => ?_, fun S S₀ ρ d a v _ u g hu y => ?_⟩
  · refine ⟨ofMat S (LinearMap.toMatrix' (transvLin S (vecX d a) v)) (unitary_of_form S _ fun x y => ?_), fun y => ?_⟩
    · rw [toMatrix_transvLin, toMatrix_transvLin, form_transv S _ _ (form_vecX d a) hv]
    · rw [act, mt_ofMat, toMatrix_transvLin]
  · rw [act_mul, act_mul, hu, act_transv, ← act_mul S g g⁻¹, mul_inv_cancel]
    congr 1
    rw [act, mt_one, Matrix.one_mulVec]

end GlobalTheory.TransvAdelic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
section
namespace I195MixedCoordinates_7149a82cc25e6f9e668c8c61

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_7149a82cc25e6f9e668c8c61

public noncomputable abbrev _root_.I195MixedCoordinates_00549d7c7323d43c39912169.source :=
  @_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.source

public noncomputable abbrev _root_.I195MixedCoordinates_00549d7c7323d43c39912169.target :=
  @_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.target

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem mixS_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (d : HypDec S S₀ 0)
    (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)) (hμ : IsCovolOne (ratMx D T.rank 0) μ 𝓕)
    (f : WO S T → ℂ) (x : Mx D T.rank 0) : (_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.source d) T ψ μ 𝓕 f x = fun w => f (d.ext0 T w) := by
  funext w
  have h1 : ∀ a : Mx D T.rank 0,
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 = f (d.ext0 T w) := by
    intro a
    rw [d.integrandS_eq, Subsingleton.elim a 0, Subsingleton.elim x 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  change (∫ a in 𝓕, heisO ψ S T (d.extY T a)
    (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0 ∂μ) = _
  simp_rw [h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem mixT_rankZero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T T₀ : HSp D) (d : HypDec T T₀ 0)
    (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)) (hμ : IsCovolOne (ratMx D 0 S.rank) μ 𝓕)
    (f : WO S T → ℂ) (y : Mx D S.rank 0) : (_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.target d) S ψ μ 𝓕 f y = fun w => f (d.inc0 S w) := by
  funext w
  have h1 : ∀ ξ : Mx D 0 S.rank,
      heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) f)) 0 = f (d.inc0 S w) := by
    intro ξ
    rw [d.integrandT_eq, Subsingleton.elim ξ 0, Subsingleton.elim y 0, map_zero, map_zero, symplOH_zero_left,
      AddChar.map_zero_eq_one, one_mul, zero_add, zero_add]
  change (∫ ξ in 𝓕, heisO ψ S T (d.incX S ξ)
    (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w) f)) 0 ∂μ) = _
  simp_rw [h1]
  rw [MeasureTheory.setIntegral_const]
  simp [Measure.real, hμ.2.2]

theorem rankZero_trivial {D : D7} (S S₀ : HSp D) (d : HypDec S S₀ 0) :
    (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  refine ⟨fun a => ?_, fun b => ?_, fun c => ?_⟩
  · rw [Subsingleton.elim a 1, map_one]
  · rw [Subsingleton.elim b 0, d.nB_zero]
  · rw [Subsingleton.elim c 0, d.nC_zero]

theorem mixRankZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (S S₀ T : HSp D) (d : HypDec S S₀ 0) (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)), IsCovolOne (ratMx D T.rank 0) μ 𝓕 → ∀ f x, (_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.source d) T ψ μ 𝓕 f x = fun w => f (d.ext0 T w)) ∧ (∀ (S T T₀ : HSp D) (d : HypDec T T₀ 0) (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)), IsCovolOne (ratMx D 0 S.rank) μ 𝓕 → ∀ f y, (_root_.I195MixedCoordinates_7149a82cc25e6f9e668c8c61.target d) S ψ μ 𝓕 f y = fun w => f (d.inc0 S w)) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ 0), (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  intro D ψ
  exact ⟨fun S S₀ T d μ 𝓕 hμ f x => mixS_rankZero ψ S S₀ T d μ 𝓕 hμ f x,
    fun S T T₀ d μ 𝓕 hμ f y => mixT_rankZero ψ S T T₀ d μ 𝓕 hμ f y,
    fun S S₀ d => rankZero_trivial S S₀ d⟩

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XZeroColumnLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ColSplitA

variable {D : D7}

theorem mulVec_mem_latA {S T : HSp D} {L : Lat S} {L' : Lat T} {P : Pl D → Prop} (M : Mx D T.rank S.rank)
    (hM : ∀ y ∈ latV S L P, M *ᵥ y ∈ latV T L' P) {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) :
    M *ᵥ z ∈ latA T L' P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (M *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact VacFlat.smul_mem_latA ha (hM u hu')
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.ColSplitA

end
end

