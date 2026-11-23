module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ThK.PolMatchStep

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_lin_eq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ ψ φ₁ ψ₁ χ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (hψ : ψ ∈ SB (κ → Fv F v)) (h₁ : Acts (evFin F v) T φ φ₁)
    (h₂ : Acts (evFin F v) T ψ ψ₁) (a b : ℂ) (h₃ : Acts (evFin F v) T (a • φ + b • ψ) χ) :
    χ = a • φ₁ + b • ψ₁ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hs : a • φ + b • ψ ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem a hφ) ((SB _).smul_mem b hψ)
  have hlin : ∀ x y : (κ → Fv F v) → ℂ,
      tens (evFin F v) (a • x + b • y) R = a • tens (evFin F v) x R + b • tens (evFin F v) y R := by
    intro x y; funext z; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ hs).1 ?_
  rw [← h₃ R (hR _ hs), hlin, map_add (f := _), map_smul, map_smul, h₁ R (hR _ hφ), h₂ R (hR _ hψ), hlin]

open Classical in
theorem pure_update (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f : SInf F κ)
    (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (κ → Fv F w))
    (hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1)
    {φ₁ : (κ → Fv F v) → ℂ} (hA : Acts (evFin F v) T (φ v) φ₁) :
    T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ v φ₁) := by
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = tens (evFin F v) (φ v) r := by rw [hrt, Function.update_eq_self]
  have hRest : Rest (evFin F v) (φ v) r := ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  rw [e1, hA r hRest, hrt]

end Local

end GlobalTheory.ThK.PolMatchStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsFromSecondMixedCoordinate
section
namespace I195MixedCoordinates_2eaa982f095d86fcb3cef527

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_2eaa982f095d86fcb3cef527

public noncomputable abbrev _root_.I195MixedCoordinates_5f138841817cdbc027192222.target :=
  @_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MixCondT

variable {D : D7}

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixT_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target d) S ψ μ 𝓕 (c • f) y = c • (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target d) S ψ μ 𝓕 f y := by
  funext w₀
  simp only [I195MixedCoordinates_2eaa982f095d86fcb3cef527.target, Pi.smul_apply,
    heisO_smul, smul_eq_mul, ← integral_const_mul]

theorem isHalf_of_wittHyperbolic_inclusion {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} {e : AE D} {w : WO S T₀}
    (h : IsHalf e (d.inc0 S w)) : IsHalf e w := by
  have hw : w = d.p0 ⬝ d.inc0 S w := by rw [HypDec.wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul]
  intro i j
  rw [hw]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem mul_eq_zero_real_fin {m k n : ℕ} {r : Mx D m k} {ξ : Mx D k n} (hr : r.map (finPart D) = 0)
    (hξ : MxAt (fun _ => True) ξ) : r ⬝ ξ = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have h1 : finPart D (r i l) = 0 := by
    have := congrFun (congrFun hr i) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  have h2 : infPart D (ξ l j) = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 (hξ l j)).1
  rw [mul_comm]
  exact GlobalTheory.RatHalfDense.mul_eq_zero_of_parts h2 h1

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vT : VolM D σ V₀.rank) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ), p.Is dV dW x ψ → ∀ (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ), VacG ψ V₀ W₀ p.Γ₀ g → IsThetaFunO ψ V₀ W g' → (∀ y', (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 g' y' = β₂ y' • g) → (∀ η ∈ p.B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β₂ (z + b) = β₂ z) → (∀ z, β₂ z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ p.B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η) → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') ∧ (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') ∧ IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vT p x y hp β₂ g g' hgv hg' hmix hinv hsupp
  have L := GlobalTheory.HeisTarget.main D ψ hψ V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol g' hg'
  have inj : ∀ f f' : WO V₀ W → ℂ, IsThetaFunO ψ V₀ W f → IsThetaFunO ψ V₀ W f' →
      (∀ y', (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 f y' = (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 f' y') → f = f' :=
    fun f f' hf hf' h => (_root_.GlobalTheory.ThetaMixInj.main D ψ hψ V₀ W f f' hf hf').2 W₀ σ dW vT h
  change (∀ ξ y, (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 (heisO ψ V₀ W (dW.incX V₀ ξ) g') y = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 g' y) ∧ (∀ w y, (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 (heisO ψ V₀ W (dW.inc0 V₀ w) g') y = heisO ψ V₀ W₀ w ((_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 g' y)) ∧ _ at L
  have th : ∀ u, IsThetaFunO ψ V₀ W (heisO ψ V₀ W u g') := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ hξ
    have hξf : MxAt (fun _ => True) ξ := hp.b₁.fin ξ hξ
    have key : ∀ z, symplO V₀ W (dW.incAdj V₀ z) (dW.incX V₀ ξ) =
        -Algebra.trace (AF D.host.F) (AE D) (z ⬝ ξ).trace := fun z => by
      rw [GlobalTheory.OrientedHeis.symplO_skew, HypDec.symplO_incX_incAdj]
    refine inj _ _ (th _) (GlobalTheory.OrientedHeis.theta_smul _ hg') fun y' => ?_
    rw [L.1 ξ y', mixT_smul, hmix y']
    by_cases hb : β₂ y' = 0
    · simp only [hb, zero_smul, smul_zero]
    obtain ⟨r, hr, η, hη, he⟩ := hsupp y' hb
    have hη1 : ψ (symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ)) = 1 := by
      rw [GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv,
        (hp.dualB' η (hp.b₂.fin η hη)).1 hη ξ hξ, inv_one]
    have hsplit : y' = y + r + (y' - (y + r)) := by abel
    have e1 : symplO V₀ W (dW.incAdj V₀ y') (dW.incX V₀ ξ) =
        symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ) + symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ) := by
      rw [← he, key, key, key]
      conv_lhs => rw [hsplit]
      rw [Matrix.add_mul, Matrix.add_mul, mul_eq_zero_real_fin hr hξf, add_zero, Matrix.trace_add, map_add (f := _), neg_add]
    rw [e1, AddChar.map_add_eq_mul, hη1, mul_one]
  · intro η hη
    obtain ⟨b, hb⟩ := incAdj_surj dW V₀ η
    rw [← hb]
    refine inj _ _ (th _) hg' fun y' => ?_
    change dW.mixT V₀ ψ vT.μ vT.𝓕 (heisO ψ V₀ W (dW.incAdj V₀ b) g') y' = dW.mixT V₀ ψ vT.μ vT.𝓕 g' y'
    rw [GlobalTheory.MixModel.Check.mixT_heis_incAdj]
    change (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 g' (y' + b) = (_root_.I195MixedCoordinates_2eaa982f095d86fcb3cef527.target dW) V₀ ψ vT.μ vT.𝓕 g' y'
    rw [hmix, hmix, hinv η hη b hb y']
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    rw [← map_nsmul]
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.1 w hw]
  · intro e he u hu hh
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.2 e he w hw (isHalf_of_wittHyperbolic_inclusion dW hh)]

end GlobalTheory.MixCondT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingConditionsOfFlatMapWeilActionNeZero
section
namespace I195MixedCoordinates_42c4dae75290f981192a257e

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

end I195MixedCoordinates_42c4dae75290f981192a257e

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFinCond

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem symplO_extX_extY_pairS {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem flatS_smul {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ) (Ψ : WO V W → ℂ) :
    flatS dV dW s x y (a • Ψ) = a • flatS dV dW s x y Ψ :=
  GlobalTheory.HandHom.flatAt_smul ψ dV dW _ _ _ _ _ x y a Ψ

theorem exists_mixS_ne {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (F : WO V W → ℂ) (hF : flatS dV dW s x y F ≠ 0) :
    ∃ u : UX D ρ, ∃ w₀, (_root_.I195MixedCoordinates_42c4dae75290f981192a257e.source dV) W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) w₀ ≠ 0 := by
  by_contra hne
  push_neg at hne
  apply hF
  funext w
  have h0 : ∀ u : UX D ρ, GlobalTheory.MixPer.flatFun ψ dV dW s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 x y F w u = 0 := by
    intro u
    have hg : (_root_.I195MixedCoordinates_42c4dae75290f981192a257e.source dV) W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) = (0 : ℂ) • (_root_.I195MixedCoordinates_42c4dae75290f981192a257e.source dV) W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1) := by
      funext w₀; simp [hne u w₀]
    simp only [GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt]
    change star (psiUni ψ u.1) * (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.target dW) V₀ ψ s.vT.μ s.vT.𝓕 ((_root_.I195MixedCoordinates_42c4dae75290f981192a257e.source dV) W ψ s.vS.μ s.vS.𝓕 F (x ⬝ u.1.1)) y w = 0
    rw [hg, GlobalTheory.HandHom.mixT_smul, zero_smul]
    simp
  simp only [flatS, GlobalTheory.MixPer.flatAt, h0, integral_zero, Pi.zero_apply]

theorem actO_one_extX {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extX W a) = d.extX W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extX, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem actO_one_extY {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : Mx D W.rank ρ) :
    actO V W 1 h (d.extY W a) = d.extY W (mt W h ⬝ a) := by
  simp only [actO, HypDec.extY, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem weilAction_one_wittExtZero {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (h : GA D W) (a : WO V₀ W) :
    actO V W 1 h (d.ext0 W a) = d.ext0 W (mt W h ⬝ a) := by
  simp only [actO, HypDec.ext0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inv_one, mt_one, Matrix.mul_one, Matrix.mul_assoc]

theorem eq_one_of_smul {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hF
  have e := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e hw
  have : (c - c') * F w = 0 := by rw [sub_mul, e, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hw

theorem pairS_sub_left {T : HSp D} {ρ : ℕ} (x x' y : Mx D T.rank ρ) : pairS T (x - x') y = pairS T x y - pairS T x' y := by
  simp only [pairS, Matrix.mul_sub, Matrix.trace_sub]

theorem pairS_idem {T : HSp D} {ρ : ℕ} {c : AE D} (hc : c * c = c) (hcA : cA D c = c) (x y : Mx D T.rank ρ) :
    pairS T (c • x) (c • y) = pairS T x (c • y) := by
  simp only [pairS, adj_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hcA]
  rw [← mul_assoc, hc]


set_option maxHeartbeats 1000000 in
theorem cond_of_flatS_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ p : Pieces V₀ W W₀ ρ σ, p.Is dV dW (rat x₀) ψ → ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, ∀ h, flatS dV dW s (rat x₀) y (s.om (1, h) Φ) ≠ 0 → Cond dW p (rat x₀) y ψ (fun _ => True) h := by
  intro D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne
  obtain ⟨hΦt, hA1, hA2, hB1, -, -⟩ := hΦ
  have hf : IsThetaFunO ψ V W (s.om (1, h) Φ) := s.weil.om_pres _ _ hΦt
  have laws := _root_.GlobalTheory.AscFlatLaws.flatS_laws D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli _ hf
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨u, w₀, hM⟩ := exists_mixS_ne dV dW s (rat x₀) y _ hne
    obtain ⟨ε, hε⟩ : ∃ ε, ε = GlobalTheory.FinPlLoc.idem D (fun _ => True) := ⟨_, rfl⟩
    have hεε : ε * ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.idem_mul_self _
    have hcA : cA D ε = ε := by rw [hε]; exact GlobalTheory.FinPlLoc.cA_idem _
    obtain ⟨A, hAdef⟩ : ∃ A : Mx D W.rank ρ, A = mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) := ⟨_, rfl⟩
    have key : ∀ a' ∈ p.A₂, ψ (symplO V W (dV.extX W A) (dV.extY W a')) =
        ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) := by
      intro a' ha'
      have e1 : heisO ψ V W (dV.extY W (mt W h ⬝ a')) (s.om (1, h) Φ) =
          ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) • s.om (1, h) Φ := by
        rw [← actO_one_extY, ← s.weil.om_heis 1 h _ Φ hΦt, hA2 a' ha', map_smul]
      have e2 := GlobalTheory.MixModel.Check.mixS_heis_extY dV s.vS.covol hf (mt W h ⬝ a') ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀
      rw [e1] at e2
      change (_root_.I195MixedCoordinates_234e4f75c563de28cf3cb155.source dV) W ψ s.vS.μ s.vS.𝓕 (ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) • (s.om (1, h) Φ)) ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀ = _ at e2
      rw [GlobalTheory.HandHom.mixS_smul, Pi.smul_apply, smul_eq_mul] at e2
      have e3 : (ψ (symplO V W (dV.extX W (rat x₀)) (dV.extY W a')) -
          ψ (symplO V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1)) (dV.extY W (mt W h ⬝ a')))) *
          (_root_.I195MixedCoordinates_42c4dae75290f981192a257e.source dV) W ψ s.vS.μ s.vS.𝓕 (s.om (1, h) Φ) ((rat x₀ : Mx D W.rank ρ) ⬝ u.1.1) w₀ = 0 := by
        rw [sub_mul, e2]
        exact sub_self _
      rcases mul_eq_zero.1 e3 with h1 | h1
      · rw [hAdef, ← GlobalTheory.StripVanish.symplO_extX_extY_mt]; exact (sub_eq_zero.1 h1).symm
      · exact absurd h1 hM
    refine ⟨u, ε • (A - rat x₀), ?_, ?_⟩
    · have hεb : MxAt (fun _ => True) (ε • (A - rat x₀)) := fun i j => by
        rw [GlobalTheory.FinPlLoc.mem_idAt_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← hε, hεε]
      refine (hp.dualA _ hεb).2 fun a' ha' => ?_
      have ha'e : ε • a' = a' := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul, hε, ← GlobalTheory.FinPlLoc.mem_idAt_iff]; exact hp.a₂.fin a' ha' i j
      have hsym : symplO V W (dV.extX W (ε • (A - rat x₀))) (dV.extY W a') =
          symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') := by
        rw [← ha'e, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_idem hεε hcA]
      have hsub : symplO V W (dV.extX W (A - rat x₀)) (dV.extY W a') =
          symplO V W (dV.extX W A) (dV.extY W a') - symplO V W (dV.extX W (rat x₀)) (dV.extY W a') := by
        rw [symplO_extX_extY_pairS, symplO_extX_extY_pairS, symplO_extX_extY_pairS, pairS_sub_left, mul_sub, map_sub]
      rw [hsym, hsub, sub_eq_add_neg, AddChar.map_add_eq_mul, key a' ha', ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · rw [← hAdef]
      intro i j
      rw [GlobalTheory.FinPlLoc.mem_idOff_iff, ← hε]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub ε (A i j - (rat x₀ : Mx D W.rank ρ) i j), ← mul_assoc, hεε, sub_self]
  ·
    intro N _ hN hA
    have key : heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) (s.om (1, h) Φ) = s.om (1, h) Φ := by
      have e : dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N) =
          actO V W 1 h (dV.extX W (mt W h⁻¹ ⬝ ((rat x₀ : Mx D W.rank ρ) ⬝ N))) := by
        rw [actO_one_extX, ← Matrix.mul_assoc, mt_mul_inv, Matrix.one_mul]
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hA1 _ hA]
    have e := laws.1 N hN
    rw [key] at e
    exact eq_one_of_smul hne (e.symm.trans (one_smul ℂ _).symm)
  ·
    intro ξ hξ ξ' _ hξ'
    have key : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ')) (s.om (1, h) Φ) =
        ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • s.om (1, h) Φ := by
      have e : dV.ext0 W (dW.incX V₀ ξ') = actO V W 1 h (dV.ext0 W (dW.incX V₀ ξ)) := by
        rw [weilAction_one_wittExtZero, hξ']
      rw [e, ← s.weil.om_heis 1 h _ Φ hΦt, hB1 ξ hξ, map_smul]
    have e := laws.2 ξ'
    rw [key, flatS_smul] at e
    exact (eq_one_of_smul hne e).symm

end GlobalTheory.AscFinCond
end
end

