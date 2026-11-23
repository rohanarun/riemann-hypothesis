module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0007
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0008
public import GroundTheory.AutomorphicForms.Bundle0011
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0001

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ContinuousKinv2
section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem continuous_Kmat (jj : Fin (m + 1)) :
    Continuous (Kmat jj : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · simp only [Kmat, Matrix.of_apply, if_pos hp]; exact continuous_apply q
    · simp only [Kmat, Matrix.of_apply, if_neg hp]; exact continuous_const

theorem continuous_Kinv2 (jj : Fin (m + 1)) :
    Continuous (Kinv2 jj : (Fin (m + 1) → k) × k → Matrix (Fin (m + 1)) (Fin (m + 1)) k) :=
  continuous_matrix fun p q => by
    by_cases hp : p = jj
    · by_cases hq : q = jj
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_pos hq]; exact continuous_snd
      · simp only [Kinv2, Matrix.of_apply, if_pos hp, if_neg hq]
        exact ((continuous_apply q).comp continuous_fst).neg.mul continuous_snd
    · simp only [Kinv2, Matrix.of_apply, if_neg hp]; exact continuous_const

theorem kappa_nbhd (S : Set (GL (Fin (m + 1)) k)) (hS : IsOpen S) (h1 : (1 : GL (Fin (m + 1)) k) ∈ S)
    (jj : Fin (m + 1)) : ∃ γ : (ValueGroupWithZero k)ˣ, ∀ a : Fin (m + 1) → k,
      (∀ i, valuation k (a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ) →
      ∃ κ : GL (Fin (m + 1)) k, κ ∈ S ∧ (κ : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kmat jj a ∧
        ((κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = Kinv jj a := by
  obtain ⟨O, hO, hOS⟩ := Units.isInducing_embedProduct.isOpen_iff.1 hS
  let H : (Fin (m + 1) → k) → Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun a => (Kmat jj a, MulOpposite.op (Kinv jj a))
  have hee : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj = 1 := by simp
  have hHc : ContinuousAt H (Pi.single jj 1) := by
    have hinv : ContinuousAt (fun a : Fin (m + 1) → k => (a jj)⁻¹) (Pi.single jj 1) := by
      have h0 : (Pi.single jj (1 : k) : Fin (m + 1) → k) jj ≠ 0 := by rw [hee]; exact one_ne_zero
      exact ((continuous_apply jj).continuousAt (x := Pi.single jj 1)).inv₀ h0
    exact (continuous_Kmat jj).continuousAt.prodMk (MulOpposite.continuous_op.continuousAt.comp
      ((continuous_Kinv2 jj).continuousAt.comp (continuousAt_id.prodMk hinv)))
  have hHe : H (Pi.single jj 1) ∈ O := by
    have h1' : (1 : GL (Fin (m + 1)) k) ∈ (Units.embedProduct (Matrix (Fin (m + 1)) (Fin (m + 1)) k)) ⁻¹' O := by
      rw [hOS]; exact h1
    have hH1 : H (Pi.single jj 1) = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) := by
      simp only [H, Units.embedProduct_apply, Units.val_one, inv_one, Kmat_single, Kinv_single]
    rw [hH1]; exact h1'
  have hcomp : ContinuousAt (fun b : Fin (m + 1) → k => H (Pi.single jj 1 + b)) 0 :=
    hHc.comp_of_eq ((continuous_const.add continuous_id).continuousAt) (by simp)
  have hN := hcomp.preimage_mem_nhds (hO.mem_nhds (by show H (Pi.single jj 1 + 0) ∈ O; rw [add_zero]; exact hHe))
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hT : (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} ∈ 𝓝 (0 : k) :=
    Filter.inter_mem (Filter.iInter_mem.2 ht) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ hx => hx⟩)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hT
  refine ⟨γ, fun a ha => ?_⟩
  have hb : ∀ i, a i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i ∈
      (⋂ i, t i) ∩ {x : k | valuation k x < ((1 : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)} :=
    fun i => hγ (ha i)
  have hmem : H a ∈ O := by
    have := hIt (a := a - Pi.single jj 1) (fun i _ => Set.mem_iInter.1 (hb i).1 i)
    simpa using this
  have haj : a jj ≠ 0 := by
    intro h0
    have h2 := (hb jj).2
    simp [h0] at h2
  refine ⟨⟨Kmat jj a, Kinv jj a, Kmat_mul_Kinv jj a haj, Kinv_mul_Kmat jj a haj⟩, ?_, rfl, rfl⟩
  rw [← hOS]
  show Units.embedProduct _ _ ∈ O
  rw [Units.embedProduct_apply]
  exact hmem

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DualSumEqZero
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) {c : kˣ} (hc : HasConductor ψ c)


include hc in
theorem dual_sum_eq_zero {s t : kˣ} {b : k} (hbt : b ∈ ball t) (hbs : b ∉ ball s) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) * b)) : Circle) : ℂ) = 0 := by
  obtain ⟨ξ0, hξ0, hne⟩ := hc.exists_ne_one (c * s⁻¹) (x := b)
    (by rw [show c * (c * s⁻¹)⁻¹ = s by rw [mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]]; exact hbs)
  let φ : k → ℂ := fun ξ => ((ψ (-(ξ * b)) : Circle) : ℂ)
  have hφ : ∀ ξ, ∀ h ∈ ball (c * t⁻¹), φ (ξ + h) = φ ξ := by
    intro ξ h hh
    show ((ψ (-((ξ + h) * b)) : Circle) : ℂ) = ψ (-(ξ * b))
    rw [add_mul, neg_add, ch_add ψ, psi_neg_triv hc hh hbt, Circle.coe_one, mul_one]
  let ξ0' : ↥(ball (c * s⁻¹)) := ⟨ξ0, hξ0⟩
  have shift : ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) =
      φ ξ0 * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) := by
    rw [Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ξ0' : Q (c * t⁻¹) (c * s⁻¹)))]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.coe_addRight, apply_out φ hφ (Quotient.out f + ξ0') _
      (by rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq'])]
    simp only [φ, AddSubgroup.coe_add, ξ0']
    rw [add_mul, neg_add, ch_add ψ, mul_comm]
  have hne' : φ ξ0 ≠ 1 := by
    intro h1
    apply hne
    have := ch_neg_mul ψ (ξ0 * b)
    simp only [φ] at h1
    rw [h1, one_mul] at this
    exact Circle.coe_eq_one.1 this
  have h2 : (1 - φ ξ0) * ∑ f : Q (c * t⁻¹) (c * s⁻¹), φ ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) = 0 := by
    rw [sub_mul, one_mul, ← shift, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne'.symm)


include hc in
theorem sum_avg {s t : kˣ} {x : V} (hx : ∀ h ∈ ball s, σ h x = x) :
    ∑ f : Q (c * t⁻¹) (c * s⁻¹), avg ψ σ s t ((Quotient.out f : ↥(ball (c * s⁻¹))) : k) x =
      ((Fintype.card (Q (c * t⁻¹) (c * s⁻¹)) : ℕ) : ℂ) • x := by
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single (0 : Q s t)]
  · rw [hx _ out_zero_mem]
    congr 1
    have h1 : ∀ f : Q (c * t⁻¹) (c * s⁻¹), ((ψ (-(((Quotient.out f : ↥(ball (c * s⁻¹))) : k) *
        ((Quotient.out (0 : Q s t) : ↥(ball t)) : k))) : Circle) : ℂ) = 1 := fun f => by
      rw [psi_neg_triv hc (out_mem f) out_zero_mem, Circle.coe_one]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · intro q _ hq
    rw [dual_sum_eq_zero ψ hc (out_mem q) (fun h => hq ((out_mem_iff q).1 h)), zero_smul]
  · intro h; exact absurd (Finset.mem_univ _) h

end DiscreteGroups.sglob.LConvGenF
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvBig
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

section Irr

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem irr_mem [ρ.IsIrreducible] (S : Submodule ℂ V) (hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S) {v : V} (hv0 : v ≠ 0)
    (hv : v ∈ S) (w : V) : w ∈ S := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv0
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this

theorem eq_zero_of_forall [ρ.IsIrreducible] (l : Module.Dual ℂ V) {v₀ : V} (hv₀ : l v₀ ≠ 0) {b : V}
    (hb : ∀ g, l (ρ g b) = 0) : b = 0 := by
  by_contra hb0
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ g, l (ρ g x) = 0}
      add_mem' := fun {x y} hx hy g => by rw [map_add (f := _), map_add (f := _), hx g, hy g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c x hx g => by rw [map_smul, map_smul, hx g, smul_zero] }
  have hS : ∀ h, ∀ ⦃x⦄, x ∈ S → ρ h x ∈ S := fun h x hx g => by
    rw [← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have := irr_mem S hS hb0 hb v₀ 1
  rw [map_one, Module.End.one_apply] at this
  exact hv₀ this

end Irr

theorem bigCell : BigCell := by
  intro k _ _ _ _ ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ hW ⟨v₁, v₂, hX, h0⟩
  have := π₁.irr
  have := π₂.irr
  obtain ⟨ω₁, -, h₁⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₁.smooth π₁.irr
  obtain ⟨ω₂, -, h₂⟩ := GlobalTheory.LocGL.exists_smooth_hasCentralChar π₂.smooth π₂.irr
  obtain rfl := centralChar_eq hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hX h0
  have hall : ∀ (a : π₁.V) (b : π₂.V), (∀ g : GL (Fin m) k, l₁ (π₁.ρ (corner g) a) = l₂ (π₂.ρ (corner g) b)) →
      ∀ g, l₁ (π₁.ρ g a) = l₂ (π₂.ρ g b) := fun a b hab g =>
    agree_all hm π₁.smooth π₂.smooth h₁ h₂ hl₁ hl₂ hW hab g
  let Y : Submodule ℂ (π₁.V × π₂.V) :=
    { carrier := {x | ∀ g, l₁ (π₁.ρ g x.1) = l₂ (π₂.ρ g x.2)}
      add_mem' := fun {x y} hx hy g => by
        rw [Prod.fst_add, Prod.snd_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx g, hy g]
      zero_mem' := fun g => by simp
      smul_mem' := fun c x hx g => by
        rw [Prod.smul_fst, Prod.smul_snd, map_smul, map_smul, map_smul, map_smul, hx g] }
  have hY : ∀ h (x : π₁.V × π₂.V), x ∈ Y → (π₁.ρ h x.1, π₂.ρ h x.2) ∈ Y := fun h x hx g => by
    show l₁ (π₁.ρ g (π₁.ρ h x.1)) = l₂ (π₂.ρ g (π₂.ρ h x.2))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact hx (g * h)
  have hv : (v₁, v₂) ∈ Y := hall v₁ v₂ hX
  have h0' : l₂ v₂ ≠ 0 := by
    have := hv 1
    rw [map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
    rwa [← this]
  have hv₁ : v₁ ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have hv₂ : v₂ ≠ 0 := fun e => h0' (by rw [e, map_zero])

  let f₁ : Y →ₗ[ℂ] π₁.V := (LinearMap.fst ℂ π₁.V π₂.V).comp Y.subtype
  let f₂ : Y →ₗ[ℂ] π₂.V := (LinearMap.snd ℂ π₁.V π₂.V).comp Y.subtype
  have inj₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun y hy => ?_
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := hy
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := eq_zero_of_forall (ρ := π₂.ρ) l₂ h0' fun g => by
      rw [← y.2 g, hy1, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have inj₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero f₂).2 fun y hy => ?_
    have hy2 : (y : π₁.V × π₂.V).2 = 0 := hy
    have hy1 : (y : π₁.V × π₂.V).1 = 0 := eq_zero_of_forall (ρ := π₁.ρ) l₁ h0 fun g => by
      rw [y.2 g, hy2, map_zero, map_zero]
    exact Subtype.ext (Prod.ext hy1 hy2)
  have surj₁ : Function.Surjective f₁ := fun a => by
    have := irr_mem (ρ := π₁.ρ) (LinearMap.range f₁) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₁ ⟨⟨_, hv⟩, rfl⟩ a
    exact this
  have surj₂ : Function.Surjective f₂ := fun b => by
    have := irr_mem (ρ := π₂.ρ) (LinearMap.range f₂) (fun h x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨_, hY h _ y.2⟩, rfl⟩) hv₂ ⟨⟨_, hv⟩, rfl⟩ b
    exact this
  let e₁ := LinearEquiv.ofBijective f₁ ⟨inj₁, surj₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨inj₂, surj₂⟩
  let T : π₁.V ≃ₗ[ℂ] π₂.V := e₁.symm.trans e₂
  have hT : ∀ a, (a, T a) ∈ Y := fun a => by
    have h1 : ((e₁.symm a : Y) : π₁.V × π₂.V).1 = a := e₁.apply_symm_apply a
    have := (e₁.symm a).2
    rw [← Prod.mk.eta (p := ((e₁.symm a : Y) : π₁.V × π₂.V)), h1] at this
    exact this
  have hint : ∀ g a, T (π₁.ρ g a) = π₂.ρ g (T a) := fun g a => by
    have h1 : e₁.symm (π₁.ρ g a) = ⟨_, hY g _ (hT a)⟩ := e₁.injective (by rw [e₁.apply_symm_apply]; rfl)
    show e₂ (e₁.symm (π₁.ρ g a)) = _
    rw [h1]
    rfl
  let Tint : Representation.IntertwiningMap π₁.ρ π₂.ρ :=
    { toLinearMap := T.toLinearMap
      isIntertwining' := fun g => LinearMap.ext fun a => hint g a }
  exact ⟨Tint.ofBijective T.bijective⟩

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvGlue
section
set_option linter.unusedSectionVars false

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConv

section Theta

variable {k : Type} [Field k]

theorem longElt_mul_self (n : ℕ) : longElt n k * longElt n k = 1 := Units.ext (antidiag_mul_self n k)


variable (k) in
def theta (n : ℕ) : GL (Fin n) k →* GL (Fin n) k :=
  (MulAut.conj (longElt n k)).toMonoidHom.comp (GlobalTheory.CuspRep.invT n k)

theorem theta_apply {n : ℕ} (g : GL (Fin n) k) :
    theta k n g = longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := by
  simp [theta, MulAut.conj_apply, inv_eq_of_mul_eq_one_right (longElt_mul_self (k := k) n)]

theorem theta_theta {n : ℕ} (g : GL (Fin n) k) : theta k n (theta k n g) = g := by
  rw [theta_apply, theta_apply, _root_.GlobalTheory.longElt_invT_involution]

theorem tilde_eq {n : ℕ} (g : GL (Fin n) k) : tilde g = theta k n g * longElt n k := by
  rw [theta_apply, mul_assoc, longElt_mul_self, mul_one]
  rfl

theorem corner_mul {m : ℕ} (g h : GL (Fin m) k) : corner (g * h) = corner g * corner h := by
  simp only [corner]
  rw [← map_mul, Prod.mk_mul_mk, mul_one]

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isFunctional_theta {ψ : AddChar k Circle} {ρ : Representation ℂ (GL (Fin n) k) V} {l : Module.Dual ℂ V}
    (hl : IsFunctional ψ ρ l) : IsFunctional ψ⁻¹ (ρ.comp (theta k n)) l := by
  intro u hu x
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.UnipFlip.longElt_invT_conj_unipB k n u hu
  show l (ρ (theta k n u) x) = _
  rw [theta_apply, hl _ h1, h2, AddChar.inv_apply]

theorem isIrreducible_comp_surjective {G G' : Type} [Group G] [Group G'] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (f : G' →* G) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G' V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G' V) ≃o Subrepresentation ρ :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact W.apply_mem_toSubmodule g' hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff.2 hρ

end Theta

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_theta (n : ℕ) : Continuous (theta k n) := by
  have hinvc : Continuous (GlobalTheory.CuspRep.invT n k) :=
    Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩
  have : (theta k n : GL (Fin n) k → GL (Fin n) k) =
      fun g => longElt n k * GlobalTheory.CuspRep.invT n k g * longElt n k := funext theta_apply
  rw [this]
  exact (continuous_const.mul hinvc).mul continuous_const

theorem continuous_corner (m : ℕ) : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
  (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))

def thetaIrr {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : IrrRep (GL (Fin n) k) :=
  ⟨σ.V, σ.ρ.comp (theta k n), fun x => (σ.smooth x).preimage (continuous_theta n),
    isIrreducible_comp_surjective σ.irr _ fun g => ⟨_, theta_theta g⟩⟩

theorem isLocallyConstant_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hs : IsSmooth ρ) (v : V) :
    IsLocallyConstant fun g => ρ g v := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' {x | ρ x v = v},
    (hs v).preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have h : ρ (g⁻¹ * x) v = v := hx
  conv_rhs => rw [← h]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem continuous_inv_addChar {ψ : AddChar k Circle} (h : Continuous ψ) :
    Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun x => ψ (-x) := funext (AddChar.inv_apply ψ)
  rw [this]
  exact h.comp continuous_neg

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem IsWhitTest.sub {m : ℕ} {ψ : AddChar k Circle} {f f' : GL (Fin m) k → ℂ} (h : IsWhitTest ψ f)
    (h' : IsWhitTest ψ f') : IsWhitTest ψ fun g => f g - f' g :=
  _root_.UpperTheory.Reformulated.B.P6.BlockTriangularLevi.DiscreteGroups.sglob.LConv.IsWhitTest.sub h h'

theorem isWhitTest_tilde {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ}
    (π : IrrRep (GL (Fin (m + 1)) k)) (hcusp : IsCuspidal π.ρ) {l : Module.Dual ℂ π.V} (hl : IsFunctional ψ π.ρ l)
    (v : π.V) : IsWhitTest ψ⁻¹ fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v) := by
  have hs2 : IsSmooth (π.ρ.comp (theta k (m + 1))) := (thetaIrr π).smooth
  have hl2 := isFunctional_theta hl
  have hJ : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer π.ρ (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have := Submodule.Quotient.subsingleton_iff.1
      (hcusp.2 2 ![a, b] (stdBlocks ![a, b] h) (_root_.GlobalTheory.unipRad_stdBlocks_two_ne_bot k (m + 1) a b h ha hb))
    rw [this]
    exact Submodule.mem_top
  have hJ2 : ∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b →
      ∀ x : π.V, x ∈ twKer (π.ρ.comp (theta k (m + 1))) (unipRad k (stdBlocks ![a, b] h)) 1 := by
    intro a b h ha hb x
    have h' : ∑ i, ![b, a] i = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h ⊢
      omega
    refine (Submodule.span_le.2 ?_) (hJ b a h' hb ha x)
    rintro _ ⟨n, y, rfl⟩
    refine Submodule.subset_span ⟨⟨theta k (m + 1) n, ?_⟩, y, ?_⟩
    · rw [theta_apply]
      exact _root_.GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad k (m + 1) b a h' h n n.2
    · simp only [MonoidHom.one_apply, Units.val_one, one_smul, MonoidHom.comp_apply]
      rw [theta_theta]
  have hψ'1 : (ψ⁻¹ : AddChar k Circle) ≠ 1 := fun h => hψ1 (inv_eq_one.1 h)
  obtain ⟨C2, hC2, hsupp2⟩ := exists_compact_mod_unipB_whittaker k ψ⁻¹ (continuous_inv_addChar hψc) hψ'1 m π.V
    (π.ρ.comp (theta k (m + 1))) hs2 hJ2 l hl2 (π.ρ (longElt (m + 1) k) v)
  have key : (fun g : GL (Fin m) k => l (π.ρ (tilde (corner g)) v)) =
      fun g => l ((π.ρ.comp (theta k (m + 1))) (corner g) (π.ρ (longElt (m + 1) k) v)) := by
    funext g
    rw [tilde_eq, map_mul, Module.End.mul_apply]
    rfl
  rw [key]
  refine ⟨fun u hu g => ?_, ?_, C2, hC2, hsupp2⟩
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.CornerUnip.corner_unipB_superDiag k m u hu
    beta_reduce
    rw [corner_mul, map_mul, Module.End.mul_apply, hl2 _ h1, h2]
  · exact ((isLocallyConstant_orbit hs2 _).comp_continuous (continuous_corner m)).comp l

end Local

theorem glue : Glue := by
  intro hGen hKir hBig hSep k _ _ _ _ _ ψ hψc hψ1 m hm π₁ π₂ hc₁ hc₂ H
  have hn₁ : Nontrivial π₁.V := nontrivial_of_irreducible π₁.irr
  have hn₂ : Nontrivial π₂.V := nontrivial_of_irreducible π₂.irr
  obtain ⟨l₁, hl₁0, hl₁⟩ := hGen k ψ hψc hψ1 _ _ π₁.ρ hn₁ hc₁
  obtain ⟨l₂, hl₂0, hl₂⟩ := hGen k ψ hψc hψ1 _ _ π₂.ρ hn₂ hc₂
  refine hBig k ψ m hm π₁ π₂ l₁ l₂ hl₁ hl₂ (fun v₁ v₂ hv => ?_) ?_
  · obtain ⟨I, hI, hS⟩ := hSep k m
    have hT := (isWhitTest_tilde hψc hψ1 π₁ hc₁ hl₁ v₁).sub (isWhitTest_tilde hψc hψ1 π₂ hc₂ hl₂ v₂)
    have h0 := hS ψ⁻¹ (continuous_inv_addChar hψc) _ hT fun σ l hl v => by
      rw [inv_inv] at hl
      obtain ⟨e, he₁, he₂⟩ := H (thetaIrr σ)
      obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar (thetaIrr σ).smooth (thetaIrr σ).irr
      have hl' : IsFunctional ψ⁻¹ (thetaIrr σ).ρ l := isFunctional_theta hl
      have e₁ := he₁ ω hω l₁ l hl₁ hl' I hI v₁ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have e₂ := he₂ ω hω l₂ l hl₂ hl' I hI v₂ (σ.ρ (theta k m (longElt m k))⁻¹ v)
      have ht : ∀ g : GL (Fin m) k,
          (thetaIrr σ).ρ (tilde g) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v := fun g => by
        show σ.ρ (theta k m (tilde g)) (σ.ρ (theta k m (longElt m k))⁻¹ v) = σ.ρ g v
        rw [tilde_eq, map_mul, theta_theta, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
      simp only [ht] at e₁ e₂
      simp only [hv] at e₁
      have e₃ := sub_eq_zero.2 (e₁.trans e₂.symm)
      rw [← map_sub] at e₃
      rw [← e₃]
      congr 1
      funext g
      exact sub_mul _ _ _
    have h1 := congrFun h0 1
    have hw : tilde (corner (1 : GL (Fin m) k)) = longElt (m + 1) k := by
      rw [corner_one, tilde_eq, map_one, one_mul]
    simp only [hw, Pi.zero_apply] at h1
    exact sub_eq_zero.1 h1
  · obtain ⟨a₁, ha₁⟩ : ∃ a, l₁ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₁0
      exact ⟨(l₁ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    obtain ⟨a₂, ha₂⟩ : ∃ a, l₂ a = 1 := by
      obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 hl₂0
      exact ⟨(l₂ a)⁻¹ • a, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ (by simpa using ha)]⟩
    let ρ : Representation ℂ (GL (Fin (m + 1)) k) (π₁.V × π₂.V) :=
      { toFun := fun g => (π₁.ρ g).prodMap (π₂.ρ g)
        map_one' := by ext <;> simp
        map_mul' := fun g h => by ext <;> simp }
    have hρ : ∀ g v, ρ g v = (π₁.ρ g v.1, π₂.ρ g v.2) := fun _ _ => rfl
    have hs : IsSmooth ρ := fun v => by
      have : {g | ρ g v = v} = {g | π₁.ρ g v.1 = v.1} ∩ {g | π₂.ρ g v.2 = v.2} := by
        ext g
        simp [hρ, Prod.ext_iff]
      rw [this]
      exact (π₁.smooth _).inter (π₂.smooth _)
    obtain ⟨v, hv⟩ := hKir k ψ hψc hψ1 m _ ρ hs (a₁, a₂)
    have hA := (hv (l₁.comp (LinearMap.fst ℂ _ _)) fun u hu x => hl₁ u hu x.1).1
    have hB := (hv (l₁.comp (LinearMap.fst ℂ _ _) - l₂.comp (LinearMap.snd ℂ _ _)) fun u hu x => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply, hρ,
        hl₁ u hu, hl₂ u hu]
      ring).2 (by simp [ha₁, ha₂])
    refine ⟨v.1, v.2, fun g => sub_eq_zero.1 (hB g), ?_⟩
    have : l₁ v.1 = 1 := hA.trans ha₁
    rw [this]
    exact one_ne_zero

end DiscreteGroups.sglob.LConv

end
end

