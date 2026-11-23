module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0183
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOZeroRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7}

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_zero_right (S T : HSp D) (x : WO S T) : hO S T x 0 = 0 := by
  unfold hO
  simp

theorem hO_zero_left (S T : HSp D) (y : WO S T) : hO S T 0 y = 0 := by
  unfold hO
  simp

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add (f := _)]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO
  rw [hO_zero_right, mul_zero, map_zero]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (M : Mx D n k) : MxAt P (a ⬝ M) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem mxAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a b : Mx D m n} (ha : MxAt P a) (hb : MxAt P b) : MxAt P (a + b) :=
  fun i j => add_mem (ha i j) (hb i j)

theorem mxAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a : Mx D m n} (ha : MxAt P a) : MxAt P (-a) :=
  fun i j => neg_mem (ha i j)

variable {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) : hO V W u (d.extY W a') = hO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, hO_zero_right, pairS, adj_zero,
    Matrix.zero_mul, Matrix.trace_zero, add_zero]

theorem hO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) : hO V W (d.extX W a) u' = hO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, pairS, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, add_zero, zero_add, hO_zero_left, hO_zero_right]

end GlobalTheory.AscFin.AnnPieces

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem symplO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) :
    symplO V W u (d.extY W a') = symplO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  unfold symplO
  rw [hO_extY_right]

theorem symplO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) :
    symplO V W (d.extX W a) u' = symplO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  unfold symplO
  rw [← hO_extX_left]

theorem extY_mul_jY (a' : Mx D W.rank ρ) : d.extY W a' ⬝ d.jY = a' := by
  rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]

theorem extX_mul_jX (a : Mx D W.rank ρ) : d.extX W a ⬝ d.jX = a := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]

def annY : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, d.extX W a ∈ Γ → ψ (symplO V W (d.extX W a) (d.extY W a')) = 1}
  zero_mem' := ⟨mxAt_zero, fun a _ => by rw [map_zero, symplO_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨mxAt_add hx.1 hy.1, fun a ha => by
    rw [map_add (f := _), symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨mxAt_neg hx.1, fun a ha => by
    rw [map_neg, symplO_neg_right, AddChar.map_neg_eq_inv, hx.2 a ha, inv_one]⟩

def annSet : Set (WO V W) := {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO V W u u') = 1}

variable {d ψ Γ}

theorem extY_mem_annSet (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) {a' : Mx D W.rank ρ} (ha' : a' ∈ annY d ψ Γ) :
    d.extY W a' ∈ annSet ψ Γ :=
  ⟨mxAt_mul ha'.1 _, fun u hu => by rw [symplO_extY_right]; exact ha'.2 _ (hX u hu)⟩

theorem mul_jY_mem_annY {u' : WO V W} (hu' : u' ∈ annSet ψ Γ) : u' ⬝ d.jY ∈ annY d ψ Γ :=
  ⟨mxAt_mul hu'.1 _, fun a ha => by rw [← symplO_extX_left]; exact hu'.2 _ ha⟩

theorem annY_eq_image (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) :
    (annY d ψ Γ : Set (Mx D W.rank ρ)) = (fun u : WO V W => u ⬝ d.jY) '' annSet ψ Γ :=
  Set.ext fun a' => ⟨fun h => ⟨_, extY_mem_annSet hX h, extY_mul_jY d a'⟩, by
    rintro ⟨u, hu, rfl⟩
    exact mul_jY_mem_annY hu⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W)) :
    (piecesOf d dW ψ Γ Γ₂).A₂ = annY d ψ Γ := by
  show AddSubgroup.closure (annY d ψ Γ : Set (Mx D W.rank ρ)) = _
  exact AddSubgroup.closure_eq _

theorem pieces_dualA (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W))
    (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ)
    (hc : IsCompact (annSet ψ Γ))
    (ho : ∃ U : Set (WO V W), IsOpen U ∧ (0 : WO V W) ∈ U ∧
      ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ Γ, ψ (symplO V W u u') = 1)
    (hb : ∀ u, MxAt (fun _ => True) u → (∀ u' ∈ annSet ψ Γ, ψ (symplO V W u u') = 1) → u ∈ Γ) :
    FinLat (piecesOf d dW ψ Γ Γ₂).A₂ ∧
      (∀ a, MxAt (fun _ => True) a → (a ∈ (piecesOf d dW ψ Γ Γ₂).A₁ ↔
        ∀ a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) ∧
      (∀ a', MxAt (fun _ => True) a' → (a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂ ↔
        ∀ a ∈ (piecesOf d dW ψ Γ Γ₂).A₁, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) := by
  rw [A₂_eq]
  refine ⟨⟨fun a' ha' => ha'.1, ?_, ?_⟩, fun a ha => ⟨fun h a' ha' => ha'.2 a h, fun h => ?_⟩,
    fun a' ha' => ⟨fun h a ha => h.2 a ha, fun h => ⟨ha', h⟩⟩⟩
  · rw [annY_eq_image hX]
    exact hc.image (continuous_id.matrix_mul continuous_const)
  · obtain ⟨U, hU, h0, hUm⟩ := ho
    refine ⟨(fun a' => d.extY W a') ⁻¹' U, hU.preimage (continuous_id.matrix_mul continuous_const), ?_, ?_⟩
    · show d.extY W 0 ∈ U
      rw [map_zero]
      exact h0
    · intro a' ha' hfin
      refine ⟨hfin, fun b hb' => ?_⟩
      have := hUm _ ha' (mxAt_mul hfin _) _ hb'
      rwa [symplO_extY_right, extX_mul_jX] at this
  · show d.extX W a ∈ Γ
    refine hb _ (mxAt_mul ha _) fun u' hu' => ?_
    rw [symplO_extX_left]
    exact h _ (mul_jY_mem_annY hu')

end GlobalTheory.AscFin.AnnPieces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinates
section
namespace I195MixedCoordinates_b311a3746f35afef36fdd39b

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

end I195MixedCoordinates_b311a3746f35afef36fdd39b

public noncomputable abbrev _root_.I195MixedCoordinates_b1361229ba0dbce9b699add1.source :=
  @_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source

public noncomputable abbrev _root_.I195MixedCoordinates_b1361229ba0dbce9b699add1.target :=
  @_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaMixInj

variable {D : D7}

theorem psi_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (t : AF D.host.F) : ψ t ≠ 0 := by
  intro h
  have e := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at e
  exact one_ne_zero e

theorem heisO_two (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v f) z = ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * f (z + u + v)) := rfl

theorem heisO_three (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u v t : WO S T) (f : WO S T → ℂ) (z : WO S T) :
    heisO ψ S T u (heisO ψ S T v (heisO ψ S T t f)) z =
      ψ (symplOH S T z u) * (ψ (symplOH S T (z + u) v) * (ψ (symplOH S T (z + u + v) t) * f (z + u + v + t))) := rfl

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem wittHyperbolic_symplecticPairing_core_dual_eq_zero {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (w : WO S T₀) (η : Mx D ρ S.rank) :
    symplOH S T (d.inc0 S w) (d.incY S η) = 0 := by
  have h := d.hO_inc S 0 0 0 η w 0
  simp only [map_zero, zero_add, add_zero, pairT, hO_eq_trace S T₀, adj_zero, Matrix.mul_zero, Matrix.zero_mul,
    trace_zero] at h
  rw [symplOH_eq, h, map_zero]


set_option maxHeartbeats 1000000 in
theorem mixT_incAdj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (g : WO S T → ℂ) (y y' : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ μ 𝓕 (heisO ψ S T (d.incAdj S y') g) y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ μ 𝓕 g (y + y') := by
  set_option backward.isDefEq.respectTransparency false in
    funext w₀
    unfold _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target
    refine congrArg (fun F : Mx D ρ S.rank → ℂ => ∫ ξ in 𝓕, F ξ ∂μ) (funext fun ξ => ?_)
    change heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) (heisO ψ S T (d.incAdj S y') g))) 0 = heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S (y + y')) (heisO ψ S T (d.inc0 S w₀) g)) 0
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq, heisO]
    have e1 : symplOH S T (d.incX S ξ + d.incAdj S y + d.inc0 S w₀) (d.incAdj S y') =
        symplOH S T (d.incX S ξ) (d.incAdj S y') := by
      rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_left]
      simp only [HypDec.incAdj_apply, HypDec.symplOH_incY_incY, wittHyperbolic_symplecticPairing_core_dual_eq_zero, add_zero]
    have e2 : d.incX S ξ + d.incAdj S y + d.inc0 S w₀ + d.incAdj S y' = d.incX S ξ + d.incAdj S (y + y') + d.inc0 S w₀ := by
      rw [map_add (f := _)]; abel
    rw [e1, e2, ← mul_assoc, ← AddChar.map_add_eq_mul, ← GlobalTheory.OrientedHeis.symplOH_add_right, ← map_add (f := _)]

theorem source {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (v : VolM D T.rank ρ) (h : ∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f x = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f' x) : f = f' := by
  set_option backward.isDefEq.respectTransparency false in
    have L := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v
    funext z
    have hz : z = d.extX T (z ⬝ d.jX) + d.ext0 T (z ⬝ d.j0) + d.extY T (z ⬝ d.jY) :=
      ((d.coordS T).symm_apply_apply z).symm
    generalize z ⬝ d.jX = a at hz
    generalize z ⬝ d.j0 = w at hz
    generalize z ⬝ d.jY = b at hz
    subst hz
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T b)
    have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.extY T b)
    have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.extX T a)
    have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.extX T a)
    have hmix : ∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f)) x =
        (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) (heisO ψ S T (d.extY T b) f')) x := fun x => by
      change I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x
      change ∀ x, I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 f x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 f' x at h
      rw [(L _ hg).1 x a, (L _ hg').1 x a, (L f hf).2.1 (x + a) b, (L f' hf').2.1 (x + a) b, h]
    have e1 := (L _ hk).2.2.2.2 w
    have e2 := (L _ hk').2.2.2.2 w
    change ∀ x, I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x = I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d T ψ v.μ v.𝓕 _ x at hmix
    have hv := e1.unique (by convert e2 using 1; exact funext fun x => congrFun (hmix (rat x)) _)
    rw [heisO_two, heisO_two] at hv
    have p : d.ext0 T w + d.extX T a + d.extY T b = d.extX T a + d.ext0 T w + d.extY T b := by abel
    rw [p] at hv
    exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv)

theorem target {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') {T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)
    (v : VolM D ρ S.rank) (h : ∀ y, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f' y) : f = f' := by
  set_option backward.isDefEq.respectTransparency false in
    have L := GlobalTheory.HeisTarget.main D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol
    funext z
    obtain ⟨y, hy⟩ := incAdj_surj d S (d.pY ⬝ z)
    have hz : z = d.incX S (d.pX ⬝ z) + d.inc0 S (d.p0 ⬝ z) + d.incAdj S y := by
      rw [hy]; exact ((d.coordT S).symm_apply_apply z).symm
    generalize d.pX ⬝ z = ξ at hz
    generalize d.p0 ⬝ z = w at hz
    subst hz
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.incAdj S y)
    have hg' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf' (d.incAdj S y)
    have hk := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (d.inc0 S w)
    have hk' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg' (d.inc0 S w)
    have hm := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk (d.incX S ξ)
    have hm' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hk' (d.incX S ξ)
    have hmix : ∀ y₀, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕
          (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f))) y₀ =
        (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕
          (heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.inc0 S w) (heisO ψ S T (d.incAdj S y) f'))) y₀ := fun y₀ => by
      change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀
      rw [(L _ hk).1 ξ y₀, (L _ hk').1 ξ y₀, (L _ hg).2.1 w y₀, (L _ hg').2.1 w y₀]
      have hh : I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 (heisO ψ S T (d.incAdj S y) f) y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 (heisO ψ S T (d.incAdj S y) f') y₀ := by
        change _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d S ψ v.μ v.𝓕 _ _ = _root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d S ψ v.μ v.𝓕 _ _
        rw [mixT_incAdj, mixT_incAdj, h]
      rw [hh]
    have e1 := (L _ hm).2.2
    have e2 := (L _ hm').2.2
    change ∀ y₀, I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ v.μ v.𝓕 _ y₀ at hmix
    have hv := e1.unique (by convert e2 using 1; exact funext fun x => congrFun (hmix (rat x)) _)
    rw [heisO_three, heisO_three, zero_add] at hv
    exact mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) (mul_left_cancel₀ (psi_ne_zero ψ _) hv))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), (∀ x, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f x = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.source d) T ψ v.μ v.𝓕 f' x) → f = f') ∧ ∀ (T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank), (∀ y, (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f y = (_root_.I195MixedCoordinates_b311a3746f35afef36fdd39b.target d) S ψ v.μ v.𝓕 f' y) → f = f' :=
  fun _ _ hψ _ _ _ _ hf hf' =>
    ⟨fun _ _ d v h => source hψ hf hf' d v h, fun _ _ d v h => target hψ hf hf' d v h⟩

end GlobalTheory.ThetaMixInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.Chain.LiftReg

theorem liftProps_obj : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D :=
  fun hP D => liftProps_of_rapidDecay hP D (_root_.GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D)

end GlobalTheory.Chain.LiftReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffPolynomialDecayRealDirections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section
open scoped ComplexConjugate

namespace GlobalTheory.RealDecay

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplOH_swap (S T : HSp D) (u v : WO S T) : symplOH S T v u = -symplOH S T u v := by
  obtain ⟨l1, l2, l3, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have h := l3 (u + v)
  rw [l1, l2, l2, l3, l3, zero_add, add_zero] at h
  linear_combination h

theorem symplO_zero_left (S T : HSp D) (w : WO S T) : symplO S T 0 w = 0 := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplOH_zero_left, add_zero]

theorem heisO_comm (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (u w : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = ψ (symplO S T u w) • heisO ψ S T w (heisO ψ S T u f) := by
  have hc := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).1
  obtain ⟨-, -, -, l4, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  rw [hc, hc, smul_smul, ← AddChar.map_add_eq_mul, add_comm w u, symplOH_swap S T u w, ← l4]
  congr 2
  ring

theorem dRho_heisO (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T)
    (hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w f₀) =
      deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 • heisO ψ S T w f₀ +
        heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) := by
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := (GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ).2.2.1 w f₀ h₀
  funext x
  have h1 : HasDerivAt (fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x)
      (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀) x) 0 :=
    (DS.1 f₀ h₀ (x + w)).const_mul (ψ (symplOH S T x w))
  have h2 := hd.hasDerivAt.mul h1
  have e : ((fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) *
      fun t : ℝ => heisO ψ S T w (heisO ψ S T (lineAt θ τ z t) f₀) x) =
      fun t : ℝ => heisO ψ S T (lineAt θ τ z t) (heisO ψ S T w f₀) x := by
    funext t
    rw [Pi.mul_apply, heisO_comm hψ S T (lineAt θ τ z t) w]
    rfl
  rw [e] at h2
  rw [(DS.1 _ hw x).unique h2]
  simp only [map_zero, symplO_zero_left, AddChar.map_zero_eq_one, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [GlobalTheory.OrientedHeis.heisO_zero]

theorem step_bound (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) {μ : Measure (WO S T)}
    {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f)
    (h₀ : IsThetaFunO ψ S T f₀) (w : WO S T) :
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤
      ‖thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀)‖ +
        ‖thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀))‖ := by
  set ℓ := deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 with hℓ
  by_cases hl : ℓ = 0
  · rw [hl, norm_zero, zero_mul]
    positivity
  have hd : DifferentiableAt ℝ (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0 := by
    by_contra hn
    exact hl (deriv_zero_of_not_differentiableAt hn)
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  have HU := GlobalTheory.ThetaSquare.heisUnitary (V := S) (W := T) hψ
  have hw : IsThetaFunO ψ S T (heisO ψ S T w f₀) := HU.2.2.1 w f₀ h₀
  have hw' : IsThetaFunO ψ S T (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) :=
    HU.2.2.1 w _ (DS.2.1 f₀ h₀)
  have key := DS.2.2 μ 𝓕 hμ h𝓕 f _ h hw
  rw [dRho_heisO hψ hθ S T τ z h₀ w hd] at key
  have i1 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw
  have i2 := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 h hw'
  have e : GlobalTheory.Ker.ipO μ 𝓕 f (ℓ • heisO ψ S T w f₀ + heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) =
      conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) +
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    simp only [GlobalTheory.Ker.ipO, thPair, Complex.star_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul, mul_add]
    rw [integral_add _ i2, ← integral_const_mul]
    · congr 1
      refine integral_congr_ae (.of_forall fun x => ?_)
      dsimp only
      ring
    · exact (i1.const_mul (conj ℓ)).congr (.of_forall fun x => by dsimp only; ring)
  change thPair μ 𝓕 _ _ = _ at key
  rw [e] at key
  have e2 : conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀) =
      -thPair μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) (heisO ψ S T w f₀) -
        thPair μ 𝓕 f (heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f₀)) := by
    rw [key]; ring
  calc ‖ℓ‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ = ‖conj ℓ * thPair μ 𝓕 f (heisO ψ S T w f₀)‖ := by
        rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := by
        rw [e2]
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_neg]

theorem coeff_bounded (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (h1 : μ 𝓕 < ⊤) {f f₀ : WO S T → ℂ} (h : IsThetaFunO ψ S T f) (h₀ : IsThetaFunO ψ S T f₀) :
    ∃ C : ℝ, ∀ w : WO S T, ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  obtain ⟨a, ha⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f h).2.1
  obtain ⟨b, hb⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := S) (W := T) hψ f₀ h₀).2.1
  refine ⟨a * b * μ.real 𝓕, fun w => norm_setIntegral_le_of_norm_le_const h1 fun x _ => ?_⟩
  rw [norm_mul, norm_star, GlobalTheory.ThetaSquare.norm_heisO hψ]
  exact mul_le_mul (ha x) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha x))

theorem realDecay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ →
    ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖ ≤ C := by
  intro D ψ hψ θ hθ S T μ 𝓕 hc f f₀ h h₀ τ z k
  obtain ⟨hμ, h𝓕, h1⟩ := hc
  have DS := GlobalTheory.ThetaSquare.derSkew (V := S) (W := T) hψ hθ τ z
  induction k generalizing f f₀ with
  | zero =>
    obtain ⟨C, hC⟩ := coeff_bounded hψ S T (μ := μ) (𝓕 := 𝓕) (by rw [h1]; exact ENNReal.one_lt_top) h h₀
    exact ⟨C, fun w => by rw [pow_zero, one_mul]; exact hC w⟩
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ := ih _ f₀ (DS.2.1 f h) h₀
    obtain ⟨C₂, hC₂⟩ := ih f _ h (DS.2.1 f₀ h₀)
    refine ⟨C₁ + C₂, fun w => ?_⟩
    have hs := step_bound hψ hθ S T hμ h𝓕 τ z h h₀ w
    calc _ = ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k *
          (‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ * ‖thPair μ 𝓕 f (heisO ψ S T w f₀)‖) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_add _ _ _
      _ ≤ C₁ + C₂ := add_le_add (hC₁ w) (hC₂ w)

end GlobalTheory.RealDecay

end
end

