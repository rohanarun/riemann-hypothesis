module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedLem
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.UnimodP
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AdUnimod

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EFinSmulEqOfFinPart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FDMSubCompact
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def PhiM (m n : ℕ) (x : Mx D m n) : Fin m → Fin n → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)

theorem cont_PhiM (m n : ℕ) (i j k) : Continuous fun x : Mx D m n => PhiM m n x i j k :=
  (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp (continuous_id.matrix_elem i j))


end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
section
noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sobolev₂

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sobCont_zero : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ} (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) :
    Sobolev₂ Lie σ (ℓ₁ + ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hb₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hb₂⟩ := h₂
  refine ⟨S₁ ++ S₂, max C₁ 0 + max C₂ 0, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hS₁ l hl X hX
    · exact hS₂ l hl X hX
  · have n₁ : 0 ≤ (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have n₂ : 0 ≤ (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have e₁ : C₁ * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum ≤
        max C₁ 0 * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) n₁
    have e₂ : C₂ * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum ≤
        max C₂ 0 * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) n₂
    have m₁ : 0 ≤ max C₁ 0 := le_max_right _ _
    have m₂ : 0 ≤ max C₂ 0 := le_max_right _ _
    rw [List.map_append, List.sum_append, LinearMap.add_apply]
    calc ‖ℓ₁ w + ℓ₂ w‖ ≤ ‖ℓ₁ w‖ + ‖ℓ₂ w‖ := norm_add_le _ _
      _ ≤ C₁ * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum + C₂ * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
        add_le_add (hb₁ w hw) (hb₂ w hw)
      _ ≤ max C₁ 0 * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum +
          max C₂ 0 * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum := add_le_add e₁ e₂
      _ ≤ (max C₁ 0 + max C₂ 0) * ((S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum +
          (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum) := by nlinarith

theorem sobCont_smul {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ) (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, hS, hb⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb w hw) (norm_nonneg c)

end Sobolev₂

variable {D : D7}


open Classical in
def ContAt {V : HSp D} {S : D.what₂.Tau → SPar} (M : Mult.DSModel V S) (T : Mult.MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

open Classical in
theorem contAt_of_mem {V : HSp D} {S : D.what₂.Tau → SPar} {M : Mult.DSModel V S}
    {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {T : Mult.MMap M} (hT : T ∈ Mult.Mult θ M J χ) : ContAt M T := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.cont
  | zero =>
    intro τ v x
    exact ⟨0, sobCont_zero, fun w => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    intro τ v x
    obtain ⟨ℓ₁, hc₁, he₁⟩ := h₁ τ v x
    obtain ⟨ℓ₂, hc₂, he₂⟩ := h₂ τ v x
    exact ⟨ℓ₁ + ℓ₂, sobCont_add hc₁ hc₂, fun w => by simp [he₁, he₂]⟩
  | smul c T _ h =>
    intro τ v x
    obtain ⟨ℓ, hc, he⟩ := h τ v x
    exact ⟨c • ℓ, sobCont_smul c hc, fun w => by simp [he]⟩

open Classical in
theorem ioUniqueAt_holds (D : D7) : IoUniqueAt D := by
  intro V S M θ J χ Kf Sinf Ds _ _ _ _ T hdense hspan u hu hvan
  rw [Mult.mem_multT] at hu
  have hcont : ContAt M (PiTensorProduct.lift.symm u) := contAt_of_mem hu
  have hsub : Submodule.span ℂ {x | ∃ φ w, T φ w = x} ≤ LinearMap.ker u := by
    rw [Submodule.span_le]
    rintro x ⟨φ, w, rfl⟩
    exact hvan φ w
  have hvK : ∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) → u (PiTensorProduct.tprod ℂ v) = 0 :=
    fun v hv => hsub (hspan v hv)
  have hTe : ∀ v, PiTensorProduct.lift.symm u v = u (PiTensorProduct.tprod ℂ v) := fun v => by simp
  have main : ∀ s : Finset D.what₂.Tau, ∀ v : ∀ τ, M.sm τ, (∀ τ ∉ s, v τ ∈ Kf τ) →
      PiTensorProduct.lift.symm u v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hTe]
      exact hvK v fun τ => hv τ (Finset.notMem_empty τ)
    | insert τ s hτ ih =>
      intro v hv
      funext x
      obtain ⟨ℓ, hℓ, hℓv⟩ := hcont τ v x
      have h0 : ∀ w ∈ Kf τ, ℓ (w : M.H τ) = 0 := by
        intro w hw
        rw [hℓv w, ih (Function.update v τ w) ?_, Pi.zero_apply]
        intro ρ hρ
        by_cases h : ρ = τ
        · subst h
          simpa using hw
        · rw [Function.update_of_ne h]
          exact hv ρ (by simp [Finset.mem_insert, h, hρ])
      have h1 := hdense τ ℓ hℓ h0 (v τ)
      rw [hℓv (v τ), Function.update_eq_self] at h1
      exact h1
  have hall : ∀ v, u (PiTensorProduct.tprod ℂ v) = 0 := fun v => by
    rw [← hTe]
    exact main Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h
  apply PiTensorProduct.ext
  ext v
  simp [hall]

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RightInv
section
noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Formalism.IndefR.Eqv

theorem rightInv_holds : RightInv := by
  intro H _ _ _ Γ _ ν _ _ 𝓕 h𝓕 ψ hψ k
  have hψ' : ∀ (g : Γ) (x : H), ψ (g • x) = ψ x := fun g x => hψ g g.2 x
  have h2 : IsFundamentalDomain Γ (MulOpposite.op k • 𝓕) ν := h𝓕.smul_of_comm (MulOpposite.op k)
  have himg : MulOpposite.op k • 𝓕 = (fun h => h * k) '' 𝓕 := by
    ext x
    simp [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨x * k⁻¹, hx, by simp⟩
  have hmp := measurePreserving_mul_right ν k
  have hme := measurableEmbedding_mulRight (G := H) k
  constructor
  · have e1 := (hmp.integrableOn_image hme (f := ψ) (s := 𝓕)).symm
    rw [← himg] at e1
    exact e1.trans (h2.integrableOn_iff h𝓕 hψ')
  · calc ∫ h in 𝓕, ψ (h * k) ∂ν = ∫ y in (fun h => h * k) '' 𝓕, ψ y ∂ν :=
          (hmp.setIntegral_image_emb hme ψ 𝓕).symm
      _ = ∫ y in MulOpposite.op k • 𝓕, ψ y ∂ν := by rw [himg]
      _ = ∫ h in 𝓕, ψ h ∂ν := h2.setIntegral_eq h𝓕 hψ'

section GA

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end GA

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def jf (x : (UI.instV fr).Gf) : GA D V := UI.brg fr (1, x)

theorem jf_isClosedEmbedding : Topology.IsClosedEmbedding (jf fr) := by
  haveI : T2Space (Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ℂ)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (UI.instV fr).Ginf := inferInstance
  have hemb : Topology.IsEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) :=
    Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd
      (continuous_const.prodMk continuous_id)
  have hcl : IsClosed (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := by
    have hr : (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) =
        ({1} : Set (UI.instV fr).Ginf) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨y, hy⟩
        simp only [Prod.mk.injEq] at hy
        exact ⟨hy.1.symm, Set.mem_univ _⟩
      · rintro ⟨ha, -⟩
        have ha' : a = 1 := ha
        exact ⟨b, by rw [ha']⟩
    rw [hr]
    exact isClosed_singleton.prod isClosed_univ
  have h1 : Topology.IsClosedEmbedding
      (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := ⟨hemb, hcl⟩
  exact (UI.brg fr).toHomeomorph.isClosedEmbedding.comp h1

theorem gf_facts : T2Space (UI.instV fr).Gf ∧ LocallyCompactSpace (UI.instV fr).Gf ∧
    SecondCountableTopology (UI.instV fr).Gf := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  have he := jf_isClosedEmbedding fr
  exact ⟨he.isEmbedding.t2Space, he.locallyCompactSpace, he.isInducing.secondCountableTopology⟩

end Fin

theorem uJ_rightInv {n : ℕ} (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsHaarMeasure) :
    μ.IsMulRightInvariant := by
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := unitary_unimodular_right_inv n ε
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by rw [Measure.map_smul _ (continuous_mul_const g).aemeasurable,
    hR.map_mul_right_eq_self]⟩

theorem unimodGA_of_frames {D : D7} {V : HSp D} (fr : UI.Frames D V) : UnimodGA V := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  obtain ⟨h1, h2, h3, h4, h5⟩ := G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram
  obtain ⟨g1, g2, g3⟩ := gf_facts fr
  have hinf : ∀ μ : Measure (UI.instV fr).Ginf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    Leaf.Proofs.piStatement_holds (InfinitePlace D.host.F) (fun v => Formalism.REAL.UJ (fr.ε v))
      (fun v μ hμ => uJ_rightInv (fr.ε v) μ hμ)
  have hf : ∀ μ : Measure (UI.instV fr).Gf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    fun μ hμ => adUnimod_closed (UI.instV fr) μ hμ
  have hprod := Leaf.Proofs.prodStatement_holds (UI.instV fr).Ginf (UI.instV fr).Gf hinf hf
  exact Leaf.Proofs.transferStatement_holds (UI.instV fr).GA (GA D V) (UI.brg fr) hprod

theorem unimodGA_holds {D : D7} (V : HSp D) : UnimodGA V :=
  unimodGA_of_frames (UI.frames_nonempty D V).some

end Formalism.IndefR.Eqv

end
end

