module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.LetterDescent

open TensorProduct

variable {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂]
  [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (F : Type) [Field F] [Algebra LL F]

def baseBil (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] F ⊗[LL] D₃ :=
  ((LinearMap.baseChangeHom LL F D₂ D₃) ∘ₗ β).liftBaseChange F

theorem baseBil_tmul (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (a b : F) (x : D₁) (y : D₂) :
    baseBil F β (a ⊗ₜ x) (b ⊗ₜ y) = (a * b) ⊗ₜ β x y := by
  simp [baseBil, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']

theorem baseBil_left (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₁ : Module.End LL D₁) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β (f₁ x) y = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β (f₁.baseChange F w) z = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add (f := _), LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

theorem baseBil_right (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₂ : Module.End LL D₂) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β x (f₂ y) = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β w (f₂.baseChange F z) = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add (f := _), LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

end GlobalTheory.LetterDescent

namespace GlobalTheory.LetterDescent

open TensorProduct

theorem exists_letter_tensor_map {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁)
    (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F]
    (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (h₁ : ∀ c x y, β (m₁ c x) y = m₃ c (β x y))
    (h₂ : ∀ c x y, β x (m₂ c y) = m₃ c (β x y)) :
    ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ,
      ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) =
        GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  let C : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ :=
    (baseBil F β).compr₂ (GlobalTheory.Pst.letterQ m₃ F τ)
  have hmem : ∀ (c : U) (v : F ⊗[LL] D₃),
      GlobalTheory.Pst.letterQ m₃ F τ ((m₃ c).baseChange F v - τ c • v) = 0 := by
    intro c v
    rw [← LinearMap.mem_ker, GlobalTheory.Pst.ker_letterQ]
    exact Submodule.mem_iSup_of_mem c ⟨v, rfl⟩
  have k₂ : GlobalTheory.Pst.letterKer m₂ F τ ≤ LinearMap.ker C.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    ext w
    simp only [C, LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, baseBil_right F β (m₂ c) (m₃ c) (h₂ c), LinearMap.zero_apply]
    rw [← map_smul, ← map_sub]
    exact hmem c _
  let C₂ := (GlobalTheory.Pst.letterKer m₂ F τ).liftQ C.flip k₂
  have k₁ : GlobalTheory.Pst.letterKer m₁ F τ ≤ LinearMap.ker C₂.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := GlobalTheory.Pst.letterQ_surjective m₂ F τ q
    change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (((m₁ c).baseChange F - τ c • LinearMap.id : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₁) w) z) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, baseBil_left F β (m₁ c) (m₃ c) (h₁ c)]
    exact hmem c _
  refine ⟨TensorProduct.lift ((GlobalTheory.Pst.letterKer m₁ F τ).liftQ C₂.flip k₁), fun x y => ?_⟩
  change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (1 ⊗ₜ x) (1 ⊗ₜ y)) = _
  rw [baseBil_tmul, mul_one]
  rfl

end GlobalTheory.LetterDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspSupportExist

theorem L_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (π : Irr k 0), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := _root_.GlobalTheory.CuspidalSupportZero.exists_isCuspSupport_zero

theorem L_jacq : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := _root_.GlobalTheory.exists_embedding_parInd_of_jacquet_nontrivial

theorem L_tens : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := _root_.GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac

theorem L_ind : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := _root_.GlobalTheory.ParIndSubquot.parInd_isSubquotient

theorem L_lt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad k e ≠ ⊥ → ∀ a, d a < n := _root_.GlobalTheory.UnipRadProper.blocks_lt_of_unipRad_ne_bot

theorem L_pit : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := _root_.GlobalTheory.piTensor_isSubquotient_of_forall

theorem L_stage : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := GlobalTheory.T.isSubquotient_parInd_products_flattened

theorem cusp_case (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hn : 0 < n) (π : Irr k n) (hc : IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  let e : (Σ _ : Fin 1, Fin n) ≃ Fin n :=
    { toFun := fun p => p.2, invFun := fun i => ⟨0, i⟩,
      left_inv := fun p => by
        obtain ⟨a, i⟩ := p
        obtain rfl : a = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one π.smooth e (fun _ _ => rfl)
  exact ⟨1, fun _ => n, fun _ => π, π.irr, fun _ => ⟨hn, π.irr, hc⟩, e,
    .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩

theorem reduce (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (hGL : GlobalTheory.Published.GeometricLemma) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (π : Irr k n) (hc : ¬ IsCuspidal π.π) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (σ : ∀ a, Irr k (d a)),
      (∀ a, d a < n) ∧ IsSubquotient π.π (multiProd e fun a => (σ a).π) := by
  obtain ⟨s, d, e, hne, hns⟩ : ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n),
      unipRad k e ≠ ⊥ ∧ ¬ Subsingleton (Jacquet π.π (unipRad k e)) := by
    by_contra h
    push_neg at h
    exact hc ⟨π.smooth, fun s d e hne => h s d e hne⟩
  obtain ⟨Y, _, _, τ, hτi, hτs, hτq, φ, hφ⟩ := L_jacq hBZ k n π s d e hns
  obtain ⟨σ, hσ⟩ := L_tens hGL k n π s d e Y τ hτi hτq
  exact ⟨s, d, e, σ, L_lt k n s d e hne, (IsSubquotient.of_injective φ hφ).trans
    (L_ind k _ _ _ e _ _ τ _ (isSmooth_piTensor fun a => (σ a).smooth) hσ)⟩

theorem glue (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, Irr k (d a)) (hsub : IsSubquotient π.π (multiProd e fun a => (σ a).π))
    (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (τ : ∀ a b, Irr k (d' a b))
    (hτ : ∀ a, IsCuspSupport (σ a).π (d' a) (fun b => (τ a b).π)) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  have h3 := fun a => (hτ a).2.2
  choose e' he' using h3
  have step1 : IsSubquotient (multiProd e fun a => (σ a).π)
      (multiProd e fun a => multiProd (e' a) fun b => (τ a b).π) :=
    L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := L_stage k s n d e t d' e' _ (fun a b => (τ a b).π) fun a b => (τ a b).smooth
  exact ⟨∑ a, t a, _, fun c => τ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, π.irr,
    fun c => (hτ _).2.1 _, E, hsub.trans (step1.trans hE)⟩

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) := by
  intro hBZ hGL k _ _ _ _ n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact L_zero k π
  by_cases hc : IsCuspidal π.π
  · exact cusp_case k n hn π hc
  · obtain ⟨s, d, e, σ, hlt, hsub⟩ := reduce hBZ hGL k n π hc
    have h := fun a => ih (d a) (hlt a) (σ a)
    choose t d' τ hτ using h
    exact glue k n π s d e σ hsub t d' τ hτ

end GlobalTheory.CuspSupportExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDoubleCosetCommutingMapPrincipalCongruence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeIsoMap

theorem isoMap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S₁ → NG.IsoRep S₁ S₂ → ∀ N : ℕ, 0 < N → (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ f ≠ 0) → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W), (∀ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ f ∈ S₂ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ (φ f) = φ f) ∧ (∃ f ∈ S₁, (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) ∧ φ f ≠ 0) ∧ (∀ (g : GAf L n) (f : GAf L n → a.W), f ∈ S₁ → (∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) → φ (NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} f) = NG.heckeD (GlobalTheory.IsotOrth.congSub L n N) {x | ∃ u ∈ GlobalTheory.IsotOrth.congSub L n N, ∃ u' ∈ GlobalTheory.IsotOrth.congSub L n N, x = u * g * u'} (φ f)) := by
  classical
  intro L _ _ _ n a S₁ S₂ hS₁ hiso N hN hex
  obtain ⟨T, hT⟩ := hiso
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (S₂.subtype ∘ₗ T.toLinearMap)
  have hφS : ∀ f (hf : f ∈ S₁), φ f = ((T ⟨f, hf⟩ : S₂) : GAf L n → a.W) := by
    intro f hf
    have := LinearMap.congr_fun hφ ⟨f, hf⟩
    simpa using this
  have hrt : ∀ h (f : GAf L n → a.W), f ∈ S₁ → φ (NG.rt L n h f) = NG.rt L n h (φ f) := by
    intro h f hf
    have hf' : NG.rt L n h f ∈ S₁ := hS₁.1.stable h f hf
    rw [hφS _ hf', hφS _ hf]
    exact hT h ⟨f, hf⟩ ⟨_, hf'⟩ rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro f hf hfix
    refine ⟨?_, fun κ hκ => ?_⟩
    · rw [hφS _ hf]; exact (T ⟨f, hf⟩).2
    · rw [← hrt κ f hf, hfix κ hκ]
  · obtain ⟨f, hf, hfix, hne⟩ := hex
    refine ⟨f, hf, hfix, ?_⟩
    rw [hφS _ hf]
    intro h0
    apply hne
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff T).1 this)
    simpa using this
  · intro g f hf hfix
    set J := GlobalTheory.IsotOrth.congSub L n N with hJ
    set D : Set (GAf L n) := {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * g * u'} with hD
    obtain ⟨M, hM, hMc⟩ := GlobalTheory.ConjCong.exists_cong_conj L n N g hN
    have hfin : {c : GAf L n ⧸ J | ∃ x ∈ D, (x : GAf L n ⧸ J) = c}.Finite := by
      refine ((GlobalTheory.HeckeRecon.finite_cosets (L := L) (n := n) (N * M) (Nat.mul_pos hN hM)).image
        (fun c : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M) => ((c.out * g : GAf L n) : GAf L n ⧸ J))).subset ?_
      rintro _ ⟨x, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)), ⟨u, (show NG.Cong L n N u from hu).1, rfl⟩, ?_⟩
      obtain ⟨k, hk⟩ : ∃ k ∈ GlobalTheory.IsotOrth.congSub L n (N * M),
          (Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))) = u * k := by
        have h1 := QuotientGroup.out_eq' (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M))
        rw [QuotientGroup.eq] at h1
        exact ⟨_, Subgroup.inv_mem _ h1, by group⟩
      obtain ⟨hkmem, hkeq⟩ := hk
      show ((Quotient.out (u : GAf L n ⧸ GlobalTheory.IsotOrth.congSub L n (N * M)) * g : GAf L n) : GAf L n ⧸ J) = ((u * g * u' : GAf L n) : GAf L n ⧸ J)
      rw [hkeq, QuotientGroup.eq]
      have hc : g⁻¹ * k * g ∈ J := hMc k hkmem
      have : (u * k * g)⁻¹ * (u * g * u') = (g⁻¹ * k * g)⁻¹ * u' := by group
      rw [this]
      exact J.mul_mem (J.inv_mem hc) hu'
    have hsum : ∀ F : GAf L n → a.W, NG.heckeD J D F = ∑ c ∈ hfin.toFinset,
        (if hc : ∃ x ∈ D, (x : GAf L n ⧸ J) = c then NG.rt L n hc.choose F else 0) := by
      intro F
      funext x
      rw [GlobalTheory.HeckeRecon.heckeD_eq_sum J D hfin, Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · exact hrt _ f hf
    · exact map_zero φ

end GlobalTheory.HeckeIsoMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNhdsOnePrincipalCongruenceSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCongNbhd

theorem conjAL_entry (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j)
      = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hx : ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have h3 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul]; simp
  have h2 : (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := by
    calc _ = (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
          (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
            conjT (conjAL L) ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
            rw [hx, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]; simp [conjT, Matrix.transpose_apply, Matrix.map_apply]

theorem ringHom_one_apply {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (n : ℕ) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.SplitCongNbhd


open GlobalTheory.SplitCongNbhd in
theorem GlobalTheory.SplitCongNbhd.exists_nhds_one_cong (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (s : SplitPlace L) (N : ℕ) (hN : 0 < N) :
    ∃ U ∈ nhds (1 : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))),
      ∀ x : GAf L n, TrivOutside {s.v} x → s.loc n x ∈ U → NG.Cong L n N x := by
  set K := s.v.adicCompletion (maximalRealSubfield L)
  let U : Set (GL (Fin n) K) := {A | ∀ i j,
    Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
    Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
      (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1}
  refine ⟨U, ?_, ?_⟩
  · have hball : {t : K | Valued.v t ≤ 1} ∈ nhds (0 : K) :=
      (Valued.isOpen_integer K).mem_nhds (by simp [Valuation.mem_integer_iff])
    have key : ∀ f : GL (Fin n) K → K, Continuous f → f 1 = 0 →
        ∀ᶠ A in nhds (1 : GL (Fin n) K), Valued.v (f A) ≤ 1 := by
      intro f hf h1
      exact hf.continuousAt.preimage_mem_nhds (by rw [h1]; exact hball)
    have hc1 : ∀ i j, Continuous fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_val.matrix_elem i j
    have hc2 : ∀ i j, Continuous fun A : GL (Fin n) K =>
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := fun i j =>
      Units.continuous_coe_inv.matrix_elem i j
    have hij : ∀ i j, ∀ᶠ (A : GL (Fin n) K) in nhds 1,
        Valued.v ((N : K)⁻¹ * ((A : Matrix (Fin n) (Fin n) K) i j - (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 ∧
        Valued.v ((N : K)⁻¹ * (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j -
          (1 : Matrix (Fin n) (Fin n) K) i j)) ≤ 1 := fun i j =>
      (key _ (continuous_const.mul ((hc1 i j).sub continuous_const)) (by simp)).and
        (key _ (continuous_const.mul ((hc2 i j).sub continuous_const)) (by simp))
    exact Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hij i j
  · intro x hx hU
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitSep.exists_sep L s
    have hN' : (N : L) ≠ 0 := by exact_mod_cast hN.ne'
    set c : AL L := ((N : L)⁻¹) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hc
    have hNc : (N : AL L) * c = 1 := by
      rw [hc, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hN',
        one_mul]; rfl
    have hconjc : conjAL L c = c := by
      rw [hc, GlobalTheory.SplitLift.conjAL_tmul, map_inv₀, map_natCast]
    have hprojc : s.proj c = (N : K)⁻¹ := by
      rw [hc, GlobalTheory.SplitLift.proj_tmul, map_inv₀, map_natCast]; simp
    set M : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hM
    have hy : ∀ i j, c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) ∈ ALint L := by
      intro i j
      refine GlobalTheory.mem_ALint_of_supported_at_split L s e he1 he2 _ ?_ ?_ ?_
      · intro w hw
        have h1 := congrFun (congrFun (hx w (by simpa using hw)) i) j
        rw [Matrix.map_apply] at h1
        rw [map_mul, map_sub, h1, ringHom_one_apply, sub_self, mul_zero]
      · rw [map_mul, map_sub, hprojc, ringHom_one_apply]
        exact (hU i j).1
      · have hinv : s.proj ((((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
            ((((s.loc n x)⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) j i := by
          rw [← map_inv]; rfl
        have h1 : (1 : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) j i := by
          simp [Matrix.one_apply, eq_comm]
        rw [map_mul, map_sub, hconjc, hM, conjAL_entry, ringHom_one_apply, map_mul, map_sub, hprojc, hinv,
          ringHom_one_apply, h1]
        exact (hU j i).2
    have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
      intro i j; rw [Matrix.one_apply]; split_ifs
      · exact (ALint L).one_mem
      · exact (ALint L).zero_mem
    have hz : ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) := by
      intro i j; rw [← mul_assoc, hNc, one_mul]
    refine ⟨?_, fun i j => ⟨_, hy i j, hz i j⟩⟩
    show ∀ i j, M i j ∈ ALint L
    intro i j
    have : M i j = (N : AL L) * (c * (M i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) +
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j := by rw [← hz, sub_add_cancel]
    rw [this]
    exact (ALint L).add_mem ((ALint L).mul_mem (natCast_mem _ _) (hy i j)) (hone i j)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PstConj

open TensorProduct Module GlobalTheory.Pst.EnlargeCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'}

theorem tensQ_tensQ (f : V →ₗ[ℚ_[l]] V') (g : V' →ₗ[ℚ_[l]] V) (hgf : ∀ v, g (f v) = v)
    (x : V ⊗[ℚ_[l]] Bst P) : tensQ P g (tensQ P f x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [hgf]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

def dpstUrCongr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) :
    DpstUr P ρ ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ' :=
  let f : V →ₗ[ℚ_[l]] V' := (e : V →ₗ[LL] V').restrictScalars ℚ_[l]
  let g : V' →ₗ[ℚ_[l]] V := (e.symm : V' →ₗ[LL] V).restrictScalars ℚ_[l]
  have hf : ∀ s v, f (ρ s v) = ρ' s (f v) := he
  have hg : ∀ s v, g (ρ' s v) = ρ s (g v) := fun s v => by
    apply e.injective
    change e (e.symm (ρ' s v)) = e (ρ s (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  { toFun := fun x => toUr P ρ' (dQ P hf ((toUr P ρ).symm x))
    invFun := fun x => toUr P ρ (dQ P hg ((toUr P ρ').symm x))
    map_add' := fun x y => by simp only [map_add (f := _)]
    map_smul' := fun c x => dQ_mulD P hf c _
    left_inv := fun x => Subtype.ext (tensQ_tensQ P f g (fun v => e.symm_apply_apply v) x.1)
    right_inv := fun x => Subtype.ext (tensQ_tensQ P g f (fun v => e.apply_symm_apply v) x.1) }

theorem isPst_congr (e : V ≃ₗ[LL] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (hV : IsPst P ρ) : IsPst P ρ' := by
  rw [IsPst, ← (dpstUrCongr P e he).rank_eq, hV]
  exact (e.restrictScalars ℚ_[l]).rank_eq

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : GlobalTheory.Pst.Induces Bw) (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)) (p : GL (Fin a) (Qbar l)), (∀ g, r' g = p * r g * p⁻¹) → IsPstAt P Bw r → IsPstAt P Bw r' ∧ wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  intro E Ω _ _ _ _ _ l _ ι a P AI _ w A h O _ _ _ Bw hj r r' p hc hr
  have hr' : IsPstAt P Bw r' := by
    obtain ⟨L₁, r₁, h₁, hp⟩ := hr
    obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
    exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩
  exact ⟨hr', GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr hr'⟩

end GlobalTheory.PstConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineWeilDeligneSpaceRestrictionEquivStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw') (hle : Bw.Kw.1 ≤ Bw'.Kw.1), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l)) → ∀ (LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (GlobalTheory.Pst.resTo ρ hle))], IsPst P ρ → ∃ e : WDSpace P ι ρ ≃ₗ[ℂ] WDSpace P ι (GlobalTheory.Pst.resTo ρ hle), (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (wdRho P ι Bw h hj ρ σ x) = wdRho P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle) σ' (e x)) ∧ ∀ x, e (wdN P ι ρ x) = wdN P ι (GlobalTheory.Pst.resTo ρ hle) (e x) := by
  first | exact @GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | exact GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv | (intros; apply GlobalTheory.Pst.ResLetter.wdSpace_resTo_equiv <;> assumption)
end

