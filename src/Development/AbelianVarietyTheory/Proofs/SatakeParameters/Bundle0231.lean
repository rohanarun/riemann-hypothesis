module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GlobDet

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S₁ S₂ : Submodule ℂ (GAf L n → a.W)) (h₁ : NG.IsIrrRep a.ρ S₁) (h₂ : NG.IsIrrRep a.ρ S₂), (∀ s : SplitPlace L, ∃ σ₁ σ₂ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS S₁ s σ₁ ∧ IsLocS S₂ s σ₂ ∧ Nonempty (σ₁.ρ.Equiv σ₂.ρ)) → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), (∀ s : SplitPlace L, s.v ≠ v) → ∃ (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v ∧ NG.SatAt { a with S := S₁, irrS := h₁ } Dv α ∧ NG.SatAt { a with S := S₂, irrS := h₂ } Dv α) → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n a S₁ S₂ h₁ h₂ hsplit hinert
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁.2.1
  obtain ⟨N, hN, hNf⟩ := (h₁.1.le hf).2
  have hfix : ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f := fun κ hκ => funext fun g => hNf κ hκ g
  obtain ⟨φ, hφ1, hφ2, hφ3⟩ := GlobalTheory.T.algebraicModularForms_heckeModules_iso_all_places L n a S₁ S₂ h₁ h₂ hsplit (fun v hv => by
    obtain ⟨w, Dv, α, hw, hs1, hs2⟩ := hinert v hv
    have k1 : ∃ f ∈ S₁, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs1
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    have k2 : ∃ f ∈ S₂, f ≠ 0 ∧ ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := by
      obtain ⟨f, hf, hf0, U, hfU, hU, -⟩ := hs2
      exact ⟨f, hf, hf0, fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)⟩
    exact ⟨w, Dv, α, hw, k1, k2, fun U hU h hh =>
      ⟨fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₁ h₁ v w Dv α hw hs1 U hU f hf hfU h hh,
       fun f hf hfU => GlobalTheory.InertSph.satU_of_fixed L n a S₂ h₂ v w Dv α hw hs2 U hU f hf hfU h hh⟩⟩) N hN ⟨f, hf, hfix, hf0⟩
  exact GlobalTheory.HeckeRecon.recon L n a a S₁ S₂ h₁ h₂ N hN φ hφ1 hφ2 hφ3

end GlobalTheory.GlobDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.LimAtLU

variable {a : ℕ}

theorem int_of_mem_inf {lam : DomWeight a} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((a : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩


open Classical in
noncomputable def jumpsOf (lam : DomWeight a) : Multiset ℤ :=
  (infOfWeight lam).map fun z => if h : ∃ n : ℤ, ((a : ℂ) - 1) / 2 - z = n then h.choose else 0

theorem jumpsOf_map (lam : DomWeight a) :
    (jumpsOf lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [jumpsOf, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  have h := int_of_mem_inf hz
  simp only [Function.comp_apply, dif_pos h]
  exact h.choose_spec.symm

theorem eq_jumpsOf {lam : DomWeight a} {J : Multiset ℤ}
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : J = jumpsOf lam :=
  Multiset.map_injective Int.cast_injective (hJ.trans (jumpsOf_map lam).symm)

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem overPl_of_induced {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : GlobalTheory.Pst.Induces Bw) {τ : E →+* Qbar l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1}
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : OverPl ι (ι.toRingHom.comp τ) w := by
  intro x hx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.symm_apply_apply]
  rw [hτ]
  have h1 := norm_algHom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ < 1 := (hj.valuation_lt_one_iff _).1 ((h x).2 hx)
  exact h1 ▸ h2

end GlobalTheory.CongL.LimAtLU


open Classical GlobalTheory.CongL.LimAtLU in
theorem GlobalTheory.CongL.crysDRU_of_linApprox : ClosedAtL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → (∀ τ : E →+* ℂ, ∃ lam, HasWeightAt U τ lam) → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Continuous r → IsSSRep r → ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C → (∀ ρ ∈ C, Continuous ρ ∧ ∃ U' : Submodule ℂ (UA E a → ℂ), SameWtAt ι w U U' ∧ CrysDRU U' ι ρ w) → CrysDRU U ι r w := by
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U _ hW r w hwl hr hss C hlin hCC
  intro P AI hT A hA O _ _ _ Bw hBw
  choose lamF hlamF using hW
  have key : ∀ lamG : (E →+* ℂ) → DomWeight a, (∀ σ, HasWeightAt U σ (lamG σ)) →
      (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (jumpsOf (lamG (ι.toRingHom.comp τ)))) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) := by
    intro lamG hG
    refine hC E Ω l a ha P AI hT w A hA O Bw hBw (fun τ => jumpsOf (lamG (ι.toRingHom.comp τ))) r hr hss C hlin
      (fun ρ hρ => ?_)
    obtain ⟨hcont, U', hWW, hcd⟩ := hCC ρ hρ
    have h := hcd P AI hT A hA O Bw hBw
    exact ⟨hcont, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ h.1,
      fun τ LL' τ' hi => h.2.2 τ LL' τ' hi _ _ ((hWW _ (overPl_of_induced ι hA hBw hi) _).1 (hG _)) (jumpsOf_map _)⟩
  refine ⟨(key lamF hlamF).2 fun ρ hρ => ?_, (key lamF hlamF).1.1, fun τ LL' τ' hi lam J hl hJ => ?_⟩
  · obtain ⟨-, U', -, hcd⟩ := hCC ρ hρ
    exact (hcd P AI hT A hA O Bw hBw).1
  · let lamG := Function.update lamF (ι.toRingHom.comp τ) lam
    have hG : ∀ σ, HasWeightAt U σ (lamG σ) := by
      intro σ
      rcases eq_or_ne σ (ι.toRingHom.comp τ) with h | h
      · rw [h]
        simpa [lamG] using hl
      · show HasWeightAt U σ (Function.update lamF (ι.toRingHom.comp τ) lam σ)
        rw [Function.update_of_ne h]
        exact hlamF σ
    have e := (key lamG hG).1.2 τ LL' τ' hi
    rw [eq_jumpsOf hJ]
    simpa [lamG] using e
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosed
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.CMSub

section Crit

open _root_.NumberField.ComplexEmbedding InfinitePlace IntermediateField

theorem isCMField_of_forall_isConj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    {σ : K ≃ₐ[ℚ] K} (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  first
  | exact @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj
  | (apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMFieldCriterion.isCMField_of_forall_isConj ..)

end Crit

def conjStable (Ω : Type) [Field Ω] : Subfield Ω where
  carrier := {x | ∃ y : Ω, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)}
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y * z, fun φ => by simp [hy, hz]⟩
  one_mem' := ⟨1, fun φ => by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨y + z, fun φ => by simp [hy, hz]⟩
  zero_mem' := ⟨0, fun φ => by simp⟩
  neg_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨-y, fun φ => by simp [hy]⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨y⁻¹, fun φ => by simp [hy]⟩

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]

theorem nonempty_ringHom_complex (E Ω : Type) [Field Ω] [Field E] [NumberField E] [Algebra E Ω]
    [IsAlgClosure E Ω] : Nonempty (Ω →+* ℂ) := by
  let ψ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  letI : Algebra E ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨(IsAlgClosed.lift : Ω →ₐ[E] ℂ).toRingHom⟩

theorem exists_extend (M : IntermediateField E Ω) (ψ : M →+* ℂ) :
    ∃ φ : Ω →+* ℂ, ∀ x : M, φ x = ψ x := by
  letI : Algebra M ℂ := ψ.toAlgebra
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic M Ω := Algebra.IsAlgebraic.tower_top (K := E) M
  let f : Ω →ₐ[M] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem mem_of_conj {L : IntermediateField E Ω} {x y : Ω} (hx : x ∈ L)
    (hy : ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x)) : y ∈ L := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have hτx : τ x = x := (mem_fixingSubgroup_iff _).mp hτ x hx
  apply φ₀.injective
  have h1 : φ₀ (τ y) = starRingEnd ℂ (φ₀ (τ x)) := hy (φ₀.comp τ.toRingHom)
  rw [h1, hτx, hy φ₀]

theorem algebraMap_mem_conjStable [IsCMField E] (e : E) : algebraMap E Ω e ∈ conjStable Ω :=
  ⟨algebraMap E Ω (IsCMField.complexConj E e), fun φ =>
    IsCMField.complexEmbedding_complexConj E (φ.comp (algebraMap E Ω)) e⟩

def conjField (E Ω : Type) [Field Ω] [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] :
    IntermediateField E Ω :=
  (conjStable Ω).toIntermediateField algebraMap_mem_conjStable

theorem le_conjField [IsCMField E] (M : IntermediateField E Ω) [NumberField M] [IsCMField M] :
    M ≤ conjField E Ω := fun x hx =>
  ⟨(IsCMField.complexConj M ⟨x, hx⟩ : M), fun φ =>
    IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M Ω)) ⟨x, hx⟩⟩

theorem isCMField_of_le [IsCMField E] (M : IntermediateField E Ω) [NumberField M]
    (h : M ≤ conjField E Ω) : IsCMField M := by
  haveI : IsTotallyComplex M := isTotallyComplex_of_algebra E M
  have hc : ∀ x : M, ∃ y : M, ∀ φ : Ω →+* ℂ, φ y = starRingEnd ℂ (φ x) := fun x => by
    obtain ⟨y, hy⟩ := h x.2
    exact ⟨⟨y, mem_of_conj x.2 hy⟩, hy⟩
  choose c hc using hc
  obtain ⟨φ₀⟩ := nonempty_ringHom_complex E Ω
  have inj : ∀ a b : M, φ₀ a = φ₀ b → a = b := fun a b hab => Subtype.ext (φ₀.injective hab)
  let f : M →+* M :=
    { toFun := c
      map_one' := inj _ _ (by simp [hc])
      map_mul' := fun a b => inj _ _ (by simp [hc])
      map_zero' := inj _ _ (by simp [hc])
      map_add' := fun a b => inj _ _ (by simp [hc]) }
  have hff : ∀ x, c (c x) = x := fun x => inj _ _ (by simp [hc])
  let g : M ≃+* M := RingEquiv.ofRingHom f f (by ext x; exact congrArg Subtype.val (hff x))
    (by ext x; exact congrArg Subtype.val (hff x))
  let σ : M ≃ₐ[ℚ] M := AlgEquiv.ofRingEquiv (f := g) (fun q => by
    rw [eq_ratCast (algebraMap ℚ M) q, map_ratCast])
  refine isCMField_of_forall_isConj M (σ := σ) fun ψ => ?_
  obtain ⟨φ, hφ⟩ := exists_extend M ψ
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  have e1 : ((σ : M →+* M) x) = c x := rfl
  rw [e1, ← hφ, ← hφ, hc]

theorem isCMField_sup_le_adjoin : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω], (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N] [NumberField ↥(M ⊔ N)], IsCMField M → IsCMField N → IsCMField ↥(M ⊔ N)) ∧ (∀ (M N : IntermediateField E Ω) [NumberField M] [NumberField N], N ≤ M → IsCMField M → IsCMField N) ∧ ∀ (M : IntermediateField E Ω) [NumberField M] (S : Set Ω), (∀ x ∈ S, ∀ φ : Ω →+* ℂ, (φ x).im = 0) → M = IntermediateField.adjoin E S → IsCMField M := by
  intro Ω _ E _ _ _ _ _
  refine ⟨fun M N _ _ _ hM hN => isCMField_of_le _ (sup_le (le_conjField M) (le_conjField N)),
    fun M N _ _ hNM hM => isCMField_of_le _ (hNM.trans (le_conjField M)),
    fun M _ S hS hMS => isCMField_of_le _ ?_⟩
  rw [hMS, IntermediateField.adjoin_le_iff]
  intro x hx
  exact ⟨x, fun φ => (Complex.conj_eq_iff_im.mpr (hS x hx φ)).symm⟩

end GlobalTheory.CMSub

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.satake_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ → (∀ B, (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ ↔ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL w (n := a)) ≠ ⊥) := by
  intro E _ _ _ a π w σ hσ
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  refine ⟨fun B => ⟨fun hB => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ h⟩, ?_⟩
  · have hB' : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := hB
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
    obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a w)) σ.ρ σ.irred
      (fun f : LocSph.Maps π w σ => f.1) (fun f => f.2.2) (GlobalTheory.LFun.KGL w (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
      (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
      (by rw [LocSph.iSup_range_eq π w σ hσ]; exact x.2)
    obtain ⟨B', hB''⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred
      ((Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩)
    exact (GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hσ hB'').unique hB' ▸ hB''
  · unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
    rw [hK]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem cg_hasSat_unique : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' :=
  fun _ _ _ _ _ _ _ _ _ h h' => CG.HasSat.unique h h'

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightTwistCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistGal

theorem twGL_coe {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (χ : Γ →* kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : kˣ) : k) • (ρ g : Matrix (Fin a) (Fin a) k) := by
  rw [Algebra.smul_def]
  rfl

theorem cont_twGL {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (hχ : Continuous fun g => ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) :
      Matrix (Fin a) (Fin a) k) := by
  simp only [twGL_coe]
  refine Continuous.smul (M := k) ?_ hρ
  exact hχ.matrix_det

theorem comp_twGL {Γ Γ' k : Type} [Group Γ] [Group Γ'] [CommRing k] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (χ : Γ →* GL (Fin 1) k) (f : Γ' →* Γ) :
    (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)).comp f =
      Formalism.MainNotions.SumRepresentations.At.twGL (ρ.comp f) (Matrix.GeneralLinearGroup.det.comp (χ.comp f)) :=
  MonoidHom.ext fun _ => rfl

end GlobalTheory.TwistGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryLocalComponentSplitPlaceHomeomorp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem GlobalTheory.Cong.cLoc_locU_bijective_open_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → Function.Bijective ((cLoc w).comp (locU a w).subtype) ∧ IsOpenMap ((cLoc w).comp (locU a w).subtype) ∧ Continuous ((cLoc w).comp (locU a w).subtype) := by
  intro E _ _ _ a w hw
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hf : ((cLoc w).comp (locU a w).subtype : locU a w → GL (Fin a) (w.adicCompletion E)) = (fun x => e x) := by
    funext x
    exact (he x).symm
  rw [hf]
  exact ⟨e.bijective, e.toHomeomorph.isOpenMap, e.continuous⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmul
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.DetIdealUnitary

theorem determinantIdeal_normOne_and_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  letI := fun D : D7 => D.host.cmStar
  intro D χ hχ N L hN hsd
  refine ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsd, ?_⟩
  intro e he
  have hu : e ∈ Matrix.unitaryGroup (Fin N) D.host.E := Matrix.mem_unitaryGroup_iff.2 he
  have h := GlobalTheory.Mem.NatEqui.chi_smulLat hχ (L := L) hsd ⟨e, hu⟩
  rw [Finset.prod_inv_distrib] at h
  exact h

end GlobalTheory.DetIdealUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlace
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
namespace GlobalTheory

theorem eventually_cofinite_under_of_eventually_cofinite :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
      (P : HeightOneSpectrum (𝓞 K) → Prop), (∀ᶠ v in Filter.cofinite, P v) →
      ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, P (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ P hP
  rw [Filter.eventually_cofinite] at hP ⊢
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      ((fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) ⁻¹' {v}).Finite := by
    intro v
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [← hw]
    rfl
  exact (hP.preimage' fun v _ => hfib v).subset fun w hw => hw

end GlobalTheory
end

