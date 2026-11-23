module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0069
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
section
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ConjDualPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}


variable (L a) in
def phiA : GA L a := finGL L a (PhiU a (Af L)) * infGL L a (PhiU a (Cinf L))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem invT_map_invT (c : Af L →+* Af L) (k : GL (Fin a) (Af L)) :
    invT a (Af L) (GeneralLinearGroup.map c (invT a (Af L) k)) = GeneralLinearGroup.map c k := by
  ext i j
  rfl

theorem rt_phiA_act (o : Op L a) :
    rt L a (phiA L a) * act (conjOp o) = act (thetaOp (invTOp o)) * rt L a (phiA L a) := by
  cases o with
  | fin k =>
    change rt L a (phiA L a) * rt L a (finGL L a _) = rt L a (finGL L a (thetaGL a _ (invT a (Af L) k))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    have h : thetaGL a (conjFin (IsCMField.complexConj L).toRingEquiv) (invT a (Af L) k) =
        PhiU a (Af L) * GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k * (PhiU a (Af L))⁻¹ := by
      change PhiU a (Af L) * invT a (Af L) (GeneralLinearGroup.map _ (invT a (Af L) k)) * (PhiU a (Af L))⁻¹ = _
      rw [invT_map_invT]
    rw [h, phiA, map_mul, map_mul, map_inv, mul_assoc, infGL_comm]
    group
  | cpt k =>
    change rt L a (phiA L a) * rt L a (infGL L a (Unitary.toUnits _)) =
      rt L a (infGL L a (Unitary.toUnits (PhiK L a * barK k * (PhiK L a)⁻¹))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [phiA, map_mul, map_mul, map_inv, toUnits_PhiK, map_mul, map_mul, map_inv]
    have e := infGL_comm (E := L) (a := a) (PhiU a (Cinf L) * Unitary.toUnits (barK k) * (PhiU a (Cinf L))⁻¹)
      (PhiU a (Af L))
    rw [map_mul, map_mul, map_inv] at e
    rw [toUnits_PhiK, ← mul_assoc (_ * _ * _) (finGL L a _), e]
    group
  | lie X =>
    change rt L a (phiA L a) * lie L a (fun i j => star (X i j)) =
      lie L a (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ))) *
        rt L a (phiA L a)
    rw [phiA, map_mul, mul_assoc,
      show (fun i j => star (X i j) : Lie L a) = toL (Matrix.of fun i j => star (X i j)) from rfl,
      GlobalTheory.CapAdInv.rt_lie, ← mul_assoc, ← lie_rt_fin, mul_assoc]
    refine congrArg (fun Y => lie L a (toL Y) * _) ?_
    have h : (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ = -(Matrix.of fun i j => star (X i j)) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    change GlobalTheory.Tw.Phi a (Cinf L) * _ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ = _
    rw [h, mul_neg, neg_mul, neg_neg]

theorem rt_inv_phiA (f : Sm L a) : rt L a (phiA L a)⁻¹ (rt L a (phiA L a) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem dualIsConjBy_of_paired_invT : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  intro L _ _ _ a π ψ ⟨B, hl, hr, hf, hc, hX⟩ ⟨T, hT⟩
  let u : π.V →ₗ[ℂ] π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  have hu : ∀ χ : π.V, (u χ).1 = rt L a (phiA L a) χ.1 := fun χ => by
    change rt L a (finGL L a _) (rt L a (infGL L a (Unitary.toUnits (PhiK L a))) χ.1) = _
    rw [toUnits_PhiK, phiA, map_mul]
    rfl
  have hkey : ∀ o χ, u (π.op (conjOp o) χ) = π.op (thetaOp (invTOp o)) (u χ) := fun o χ =>
    Subtype.ext (by rw [hu, CuspSub.op_val, CuspSub.op_val, hu]; exact LinearMap.congr_fun (rt_phiA_act o) χ.1)
  have hinj : ∀ χ, u χ = 0 → χ = 0 := fun χ h => Subtype.ext (by
    have e := congrArg (fun ξ : π.V => rt L a (phiA L a)⁻¹ ξ.1) h
    simp only [hu, rt_inv_phiA, ZeroMemClass.coe_zero, map_zero] at e
    exact e)
  have hsurj : ∀ χ : π.V, ∃ ξ, u ξ = χ := fun χ =>
    ⟨π.op (.cpt (PhiK L a)⁻¹) (π.op (.fin (PhiU a (Af L))⁻¹) χ), Subtype.ext (by
      rw [hu]
      change rt L a (phiA L a) (rt L a (infGL L a (Unitary.toUnits (PhiK L a)⁻¹)) (rt L a (finGL L a _) χ.1)) = _
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, map_inv, toUnits_PhiK, phiA, map_inv,
        map_inv]
      simp)⟩
  refine ⟨B.compl₂ (T.toLinearMap ∘ₗ u), fun φ h => hl φ fun ψ' => ?_, fun χ h => hinj χ ?_,
    fun k φ χ => ?_, fun k φ χ => ?_, fun X φ χ => ?_⟩
  · obtain ⟨χ, rfl⟩ := T.surjective ψ'
    obtain ⟨ξ, rfl⟩ := hsurj χ
    exact h ξ
  · exact (LinearEquiv.map_eq_zero_iff T).1 (hr _ h)
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hf k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hc k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hX X φ _

end GlobalTheory.ConjDualPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepDualIsoOfCommonRepresentedFunctional
section
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ContraPair

theorem iso_of_common_functional : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (s₁ s₂ : Op E a → Op E a), Function.Involutive s₁ → Function.Involutive s₂ → ∀ B₁ B₂ : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B₁ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₁ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₁ (π.op (.fin k) φ) (π.op (s₁ (.fin k)) ψ) = B₁ φ ψ) → (∀ k φ ψ, B₁ (π.op (.cpt k) φ) (π.op (s₁ (.cpt k)) ψ) = B₁ φ ψ) → (∀ X φ ψ, B₁ (π.op (.lie X) φ) ψ + B₁ φ (π.op (s₁ (.lie X)) ψ) = 0) → (∀ φ, (∀ ψ, B₂ φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B₂ φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B₂ (π.op (.fin k) φ) (π.op (s₂ (.fin k)) ψ) = B₂ φ ψ) → (∀ k φ ψ, B₂ (π.op (.cpt k) φ) (π.op (s₂ (.cpt k)) ψ) = B₂ φ ψ) → (∀ X φ ψ, B₂ (π.op (.lie X) φ) ψ + B₂ φ (π.op (s₂ (.lie X)) ψ) = 0) → ∀ ψ₁ ψ₂ : π.V, ψ₁ ≠ 0 → (∀ φ, B₁ φ ψ₁ = B₂ φ ψ₂) → ∃ S : π.V ≃ₗ[ℂ] π.V, ∀ o φ, S (π.op (s₁ o) φ) = π.op (s₂ o) (S φ) := by
  intro E _ _ _ a π s₁ s₂ hs₁ hs₂ B₁ B₂ hl₁ hr₁ hf₁ hc₁ hL₁ hl₂ hr₂ hf₂ hc₂ hL₂ ψ₁ ψ₂ hψ₁ hψ

  have irr : ∀ P : Submodule ℂ π.V, (∀ o, ∀ x ∈ P, π.op o x ∈ P) → P ≠ ⊥ → P = ⊤ := by
    intro P hP h0
    have hst : _root_.GlobalTheory.CuspRep.IsStable (P.map π.V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨π.op o x, hP o x hx, rfl⟩
    have e := Submodule.comap_map_eq_of_injective π.V.injective_subtype P
    rcases π.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact absurd (by rw [← e, h, Submodule.comap_bot, Submodule.ker_subtype]) h0
    · rw [← e, h, Submodule.comap_subtype_self]
  have hfin : ∀ k (φ : π.V), π.op (.fin k) (π.op (.fin k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (finRep E a k * finRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)
  have hcpt : ∀ k (φ : π.V), π.op (.cpt k) (π.op (.cpt k⁻¹) φ) = φ := fun k φ => Subtype.ext (by
    show (cptRep E a k * cptRep E a k⁻¹) φ.1 = φ.1
    rw [← map_mul, mul_inv_cancel, map_one]; rfl)

  have key : ∀ o ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ∀ φ, B₁ φ (π.op (s₁ o) ψ) = B₂ φ (π.op (s₂ o) ψ') := by
    intro o ψ ψ' h φ
    cases o with
    | fin k =>
      have e1 := hf₁ k (π.op (.fin k⁻¹) φ) ψ
      have e2 := hf₂ k (π.op (.fin k⁻¹) φ) ψ'
      rw [hfin] at e1 e2
      rw [e1, e2, h]
    | cpt k =>
      have e1 := hc₁ k (π.op (.cpt k⁻¹) φ) ψ
      have e2 := hc₂ k (π.op (.cpt k⁻¹) φ) ψ'
      rw [hcpt] at e1 e2
      rw [e1, e2, h]
    | lie X =>
      have e1 := hL₁ X φ ψ
      have e2 := hL₂ X φ ψ'
      have e3 := h (π.op (.lie X) φ)
      linear_combination e1 - e2 - e3
  have uniq : ∀ x y : π.V, (∀ φ, B₂ φ x = B₂ φ y) → x = y := fun x y h =>
    sub_eq_zero.1 (hr₂ _ fun φ => by rw [map_sub, h, sub_self])
  have inj₂ : Function.Injective B₂.flip := fun x y h => uniq x y fun φ => by
    simpa using LinearMap.congr_fun h φ

  let N : Submodule ℂ π.V := (LinearMap.range B₂.flip).comap B₁.flip
  have memN : ∀ ψ ψ', (∀ φ, B₁ φ ψ = B₂ φ ψ') → ψ ∈ N := fun ψ ψ' h =>
    ⟨ψ', LinearMap.ext fun φ => by simpa using (h φ).symm⟩
  have hN : N = ⊤ := by
    refine irr N (fun o x hx => ?_) fun h => hψ₁ ((Submodule.eq_bot_iff _).1 h ψ₁ (memN _ _ hψ))
    obtain ⟨y, hy⟩ := hx
    have h : ∀ φ, B₁ φ x = B₂ φ y := fun φ => by simpa using (LinearMap.congr_fun hy φ).symm
    have := key (s₁ o) x y h
    rw [hs₁ o] at this
    exact memN _ _ this
  have hmem : ∀ ψ, B₁.flip ψ ∈ LinearMap.range B₂.flip := fun ψ =>
    (show ψ ∈ N from hN ▸ Submodule.mem_top)
  let T : π.V →ₗ[ℂ] π.V := (LinearEquiv.ofInjective B₂.flip inj₂).symm.toLinearMap ∘ₗ
    B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem
  have hT : ∀ ψ φ, B₂ φ (T ψ) = B₁ φ ψ := by
    intro ψ φ
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective B₂.flip inj₂).apply_symm_apply
      (B₁.flip.codRestrict (LinearMap.range B₂.flip) hmem ψ))
    rw [LinearEquiv.ofInjective_apply, LinearMap.codRestrict_apply] at h1
    have h2 := LinearMap.congr_fun h1 φ
    rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
    exact h2
  have hTo : ∀ o φ, T (π.op (s₁ o) φ) = π.op (s₂ o) (T φ) := fun o φ =>
    uniq _ _ fun χ => by rw [hT]; exact key o φ (T φ) (fun χ => (hT φ χ).symm) χ
  have injT : Function.Injective T := fun x y h =>
    sub_eq_zero.1 (hr₁ _ fun φ => by rw [map_sub, ← hT, ← hT, h, sub_self])
  have hR : LinearMap.range T = ⊤ := by
    refine irr _ (fun o x hx => ?_) fun h => hψ₁ (injT ?_)
    · obtain ⟨y, rfl⟩ := hx
      refine ⟨π.op (s₁ (s₂ o)) y, ?_⟩
      rw [hTo, hs₂ o]
    · rw [map_zero]
      exact (Submodule.eq_bot_iff _).1 h _ ⟨ψ₁, rfl⟩
  exact ⟨LinearEquiv.ofBijective T ⟨injT, LinearMap.range_eq_top.1 hR⟩, hTo⟩

end GlobalTheory.ContraPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorEqLabelOperatorLocalReps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkDict

theorem lift_cosets {H G : Type} [Group H] [Group G] (φ : H →* G) (N J₀ L₀ L₁ : Subgroup H) (J : Subgroup G) (K : Set H)
    (hs : ∀ x, ∃ g ∈ N, φ g = x) (hi : ∀ g g', g ∈ N → g' ∈ N → φ g = φ g' → g = g')
    (hJ : ∀ g, g ∈ N → (φ g ∈ J ↔ g ∈ J₀)) (hLN : ∀ g ∈ L₀, g ∈ N)
    (hc : ∀ g g', g ∈ L₀ → g' ∈ L₁ → Commute g g') (hd : ∀ g, g ∈ L₀ → g ∈ L₁ → g = 1)
    (hK : ∀ g, g ∈ L₀ → (g ∈ J₀ ↔ g ∈ K))
    (hsp : ∀ k ∈ J₀, ∃ k₁ ∈ J₀, ∃ k₂ ∈ J₀, k₁ ∈ L₀ ∧ k₂ ∈ L₁ ∧ k = k₁ * k₂)
    (α : H) (hα : α ∈ L₀) (B : Finset G) (hB : ∀ a ∈ B, ∃ g ∈ L₀, φ g = a) (hDC : Bridge.IsDC J (φ α) B) :
    ∃ R : Finset H, (∀ γ ∈ R, γ ∈ L₀) ∧
      (∀ γ ∈ R, ∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ γ = k₁ * α * k₂) ∧
      (∀ x : H, (∃ k₁, (k₁ ∈ K ∧ k₁ ∈ L₀) ∧ ∃ k₂, (k₂ ∈ K ∧ k₂ ∈ L₀) ∧ x = k₁ * α * k₂) →
        ∃! γ, γ ∈ R ∧ (γ⁻¹ * x ∈ K ∧ γ⁻¹ * x ∈ L₀)) ∧
      ∀ (W : Type) [AddCommMonoid W] (F : G → W), ∑ a ∈ B, F a = ∑ γ ∈ R, F (φ γ) := by
  classical
  choose s hs1 hs2 using hs
  have hsL : ∀ a ∈ B, s a ∈ L₀ := fun a ha => by
    obtain ⟨g, hg, rfl⟩ := hB a ha
    rw [hi _ _ (hs1 _) (hLN g hg) (hs2 _)]
    exact hg
  have hsinj : Function.Injective s := fun a b h => by rw [← hs2 a, ← hs2 b, h]
  have hKJ : ∀ k, k ∈ K ∧ k ∈ L₀ → φ k ∈ J := fun k hk => (hJ k (hLN k hk.2)).2 ((hK k hk.2).2 hk.1)
  refine ⟨B.image s, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact hsL a ha
  · intro γ hγ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    obtain ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, hk⟩ := hDC.1 a ha
    have j₁ : s k₁ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    have j₂ : s k₂ ∈ J₀ := (hJ _ (hs1 _)).1 (by rwa [hs2])
    obtain ⟨a₁, ha₁, b₁, hb₁, la₁, lb₁, e₁⟩ := hsp _ j₁
    obtain ⟨a₂, ha₂, b₂, hb₂, la₂, lb₂, e₂⟩ := hsp _ j₂
    have e : s a = s k₁ * α * s k₂ := by
      refine hi _ _ (hs1 _) (N.mul_mem (N.mul_mem (hs1 _) (hLN _ hα)) (hs1 _)) ?_
      rw [map_mul, map_mul, hs2, hs2, hs2]
      exact hk
    have e' : s a = (a₁ * α * a₂) * (b₁ * b₂) := by
      rw [e, e₁, e₂]
      have c := (hc _ _ (L₀.mul_mem hα la₂) lb₁).eq
      calc a₁ * b₁ * α * (a₂ * b₂) = a₁ * (b₁ * (α * a₂)) * b₂ := by simp only [mul_assoc]
        _ = _ := by rw [← c]; simp only [mul_assoc]
    have hb : b₁ * b₂ = 1 := by
      refine hd _ ?_ (L₁.mul_mem lb₁ lb₂)
      have : b₁ * b₂ = (a₁ * α * a₂)⁻¹ * s a := by rw [e', inv_mul_cancel_left]
      rw [this]
      exact L₀.mul_mem (L₀.inv_mem (L₀.mul_mem (L₀.mul_mem la₁ hα) la₂)) (hsL a ha)
    exact ⟨a₁, ⟨(hK _ la₁).1 ha₁, la₁⟩, a₂, ⟨(hK _ la₂).1 ha₂, la₂⟩, by rw [e', hb, mul_one]⟩
  · rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have hxL : x ∈ L₀ := hx ▸ L₀.mul_mem (L₀.mul_mem h₁.2 hα) h₂.2
    obtain ⟨a, ⟨ha, haJ⟩, hu⟩ := hDC.2 (φ x) ⟨⟨φ k₁, hKJ _ h₁⟩, ⟨φ k₂, hKJ _ h₂⟩, by rw [hx, map_mul, map_mul]⟩
    have hL : (s a)⁻¹ * x ∈ L₀ := L₀.mul_mem (L₀.inv_mem (hsL a ha)) hxL
    refine ⟨s a, ⟨Finset.mem_image_of_mem s ha, (hK _ hL).1 ((hJ _ (hLN _ hL)).1 ?_), hL⟩, ?_⟩
    · rwa [map_mul, map_inv, hs2]
    · rintro γ ⟨hγ, hγK⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
      have := hKJ _ hγK
      rw [map_mul, map_inv, hs2] at this
      rw [hu b ⟨hb, this⟩]
  · intro W _ F
    rw [Finset.sum_image fun a _ b _ h => hsinj h]
    simp only [hs2]

def rightTr {H G : Type} [Group H] [Group G] (φ : H →* G) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (G → W) where
  toFun g := { toFun := fun F h => F (h * φ g), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  map_one' := by ext F h; simp
  map_mul' g g' := by ext F h; simp [mul_assoc]

theorem supp_both {D : D7} (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) (h : SuppF V f g) (h' : SuppF V (1 - f) g) :
    g = 1 := by
  apply Subtype.ext
  apply Units.ext
  have : Formalism.L2.Theta.mt V g - 1 = 0 := by
    ext i j
    have a := h i j
    have b := h' i j
    rw [sub_mul, one_mul, a, sub_self] at b
    exact b.symm
  exact sub_eq_zero.1 this


set_option maxHeartbeats 1000000 in
open GlobalTheory.SplitHeckeAdj in
theorem dcOp_eq_label : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → ∀ (d : List ℤ) (x : Bridge.Gf V) (B : Finset (Bridge.Gf V)), d.Pairwise (fun a b => b ≤ a) → IsLabElt V P d x → (∀ a ∈ B, IsLocElt V P a) → Bridge.IsDC (levEnv V β L).J x B → IsLab V P d ∧ ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Φ : Bridge.Gf V → W), (∀ h (k : (levEnv V β L).J), IsLocElt V P k → Φ (h * k) = Φ h) → Bridge.dcOp B Φ = hkF V P (Finsupp.single d 1) Φ := by
  intro D V β Λ N L hβ P hN hoff d x B hd hx hB hDC
  obtain ⟨e, f, ϖ, α, hP, hϖ, hϖ', -, hxα, hα, hdiv⟩ := hx
  have hG := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have h01 := hG.2.2.1 P e f hP
  have hff := h01.1
  have hcf := h01.2.1
  have hff' : (1 - f) * (1 - f) = 1 - f := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hff, sub_self, sub_zero]
  have hcf' : cA D (1 - f) = 1 - f := by rw [map_sub, map_one, hcf]
  obtain ⟨L₀, hL₀⟩ := (hG.1 f hff hcf).1
  obtain ⟨L₁, hL₁⟩ := (hG.1 _ hff' hcf').1
  have h03 := (GlobalTheory.LevSplit.lev_split V β Λ N (flag1L L) hβ).2 P e f hP hN hoff
  have hK := h03.1
  have hsp := h03.2.2
  have hx' : x = fin V α := Subtype.ext hxα
  subst hx'
  have hB' : ∀ a ∈ B, ∃ g ∈ L₀, fin V g = a := fun a ha => by
    obtain ⟨e', f', g, hP', -, h1, h2⟩ := hB a ha
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at h2
    exact ⟨g, (hL₀ g).2 h2, Subtype.ext h1.symm⟩
  have main := lift_cosets (fin V) (GfC V) (levG V β (flag1L L)) L₀ L₁ (levEnv V β L).J (KsphC V ∅)
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L)
    (fun g hg => h01.2.2.1 g ((hL₀ g).1 hg))
    (fun g g' h h' => commute_compl V _ hff hcf ((hL₀ g).1 h) ((hL₁ g').1 h'))
    (fun g h h' => supp_both V f g ((hL₀ g).1 h) ((hL₁ g).1 h'))
    (fun g h => hK g ((hL₀ g).1 h))
    (fun k hk => by
      obtain ⟨k₁, h₁, k₂, h₂, s₁, s₂, h⟩ := hsp k hk
      exact ⟨k₁, h₁, k₂, h₂, (hL₀ _).2 s₁, (hL₁ _).2 s₂, h⟩)
    α ((hL₀ α).2 hα) B hB' hDC
  obtain ⟨R, r1, r2, r3, r4⟩ := main
  simp only [hL₀] at r1 r2 r3
  have hR : SphOp V P d R :=
    ⟨e, f, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), hP, hϖ, hϖ', hd, fun _ _ => Iff.rfl, fun _ _ _ => rfl,
      hα, hdiv, r1, fun γ hγ => ⟨h01.2.2.1 γ (r1 γ hγ), r2 γ hγ⟩, r3⟩
  refine ⟨⟨R, hR⟩, fun W _ _ Φ hΦ => ?_⟩
  have hfix : ∀ k ∈ GlobalTheory.Hk3.hyp V P, rightTr (fin V) W k Φ = Φ := by
    rintro k ⟨hk, e', f', hP', hs⟩
    have h3 : f' = f := (h01.2.2.2.1 e' f' hP').2
    rw [h3] at hs
    have hkf := h01.2.2.1 k hs
    funext h
    exact hΦ h ⟨fin V k, (mem_J V β L hkf).2 ((hK k hs).2 hk)⟩ ⟨e, f, k, hP, hkf, rfl, hs⟩
  have h := ((_root_.GlobalTheory.SphLabelOps.label_operators V P).1 d R hR).2 _ (rightTr (fin V) W) Φ hfix
  funext g
  have h1 := congrFun h g
  have h2 : Bridge.dcOp B Φ g = ∑ γ ∈ R, Φ (g * fin V γ) := r4 W fun a => Φ (g * a)
  rw [h2]
  simp only [opOf, hkF, zero_smul, Finsupp.sum_single_index, one_smul, Finset.sum_apply, LinearMap.sum_apply] at h1 ⊢
  exact h1

end GlobalTheory.HkDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequality
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.Cong

theorem eigen_small_sub_finite_approx : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  intro l _ ι V X J I _ _ _ T ev hT v₀ θ x₀ hθ hx₀ v η hη ε hε
  classical
  have hmap : ∀ (w : J → ℂ) (P : MvPolynomial J ℤ),
      ι.symm (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  let u : MvPolynomial J ℤ → V := fun P =>
    MvPolynomial.aeval θ P • v₀ + ∑ i, MvPolynomial.aeval (η i) P • v i
  have good : ∀ P, ∀ x, ‖ι.symm (ev x (u P))‖ ≤ ε := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C n =>
      intro x
      have e : u (MvPolynomial.C n) = (n : ℂ) • (v₀ + ∑ i, v i) := by
        simp [u, smul_add, Finset.smul_sum]
      rw [e, map_smul, smul_eq_mul, map_mul, norm_mul, map_intCast]
      have h1 : ‖((n : ℤ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
      have h2 := hε x
      have h3 := norm_nonneg (ι.symm (ev x (v₀ + ∑ i, v i)))
      nlinarith
    | add p q hp hq =>
      intro x
      have e : u (p + q) = u p + u q := by
        simp only [u, map_add (f := _), add_smul, Finset.sum_add_distrib]; abel
      rw [e, map_add (f := _), map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp x) (hq x))
    | mul_X p j hp =>
      intro x
      have e : u (p * MvPolynomial.X j) = T j (u p) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [u, map_add (f := _), map_sum, map_smul, hθ, hη, map_mul, MvPolynomial.aeval_X, smul_smul]
      rw [e]
      exact hT (u p) ε hp j x
  have hb0 : ι.symm (ev x₀ v₀) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨Finset.univ.image (fun i => fun j => ι.symm (η i j)),
    fun z => - ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
      ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀), ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact ⟨i, rfl⟩
  · intro P
    have key : ∑ z ∈ Finset.univ.image (fun i => fun j => ι.symm (η i j)),
        (- ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
          ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀)) * MvPolynomial.aeval z P
        = - ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => fun j => ι.symm (η i j))
        (t := Finset.univ.image (fun i => fun j => ι.symm (η i j)))
        (fun i hi => Finset.mem_image_of_mem _ hi), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hi]
    have hexp : ι.symm (ev x₀ (u P)) =
        (MvPolynomial.aeval (fun j => ι.symm (θ j)) P + ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P) * ι.symm (ev x₀ v₀) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, map_add (f := _), map_sum, map_smul, smul_eq_mul, map_mul, hmap, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [key, sub_neg_eq_add]
    have h := good P x₀
    rw [hexp, norm_mul, hx₀, mul_one] at h
    exact h

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntryUnramifiedUnit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

namespace GlobalTheory.KerJ

theorem unUnit_of_mtType : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ u μ, MtType u (t.O u μ).mt) → t.ent.UnUnit := by
  intro D L hT Gi Gl K Y cX ex t hm u μ w hw i hi c c'
  have h3 := _root_.GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType D u (D.chTw u μ) _ (hm u μ)
  have hb := CharVal.brRho_holds D _ _ h3
  rw [t.kf_un u μ w hw i hi c c']
  exact (t.kf u μ w hw).norm_un ((t.kf u μ w hw).unUnit_of t.idl t.idl_ok hb (_root_.GlobalTheory.SatakeUnitDeterminantBasis.detB _ _ _ _ _ _ _ _ _)) hi c c'

end GlobalTheory.KerJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLowerBlockFlag
section
namespace GlobalTheory.LowerBlockFlag

def f0 {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ} (e : (i : Fin s) × Fin (d i) ≃ Fin a) (c : Fin s) :
    Submodule k (Fin a → k) where
  carrier := {v | ∀ p : Fin a, c < GlobalTheory.SmGL.blk e p → v p = 0}
  add_mem' {u v} hu hv p hp := by
    rw [Pi.add_apply, hu p hp, hv p hp, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r {v} hv p hp := by
    rw [Pi.smul_apply, hv p hp, smul_zero]

end GlobalTheory.LowerBlockFlag
end

