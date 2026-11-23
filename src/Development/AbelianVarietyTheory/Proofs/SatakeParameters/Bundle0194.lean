module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionExistence.LeOneIffOfMulEqOne
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.GalFirstClause

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem finextRep : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (a : ℕ) (r : G E Ω →* GL (Fin a) (Om l)), Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) →
    ∃ (K : FinExt l) (ρ : G E Ω →* GL (Fin a) ↥K.1), Continuous (fun g => (ρ g : Matrix (Fin a) (Fin a) ↥K.1)) ∧
      mapRep (algebraMap ↥K.1 (Om l)) ρ = r := by
  intro l _ E Ω _ _ _ _ _ a r hr
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a r hr (GlobalTheory.Pst.adjExt 0)
  let f : ↥L.1 →+* Om l := algebraMap ↥L.1 (Om l)
  let M : G E Ω → Matrix (Fin a) (Fin a) ↥L.1 := fun g => Matrix.of fun i j => ⟨(r g : Matrix (Fin a) (Fin a) (Om l)) i j, hL g i j⟩
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin a) (Fin a) ↥L.1 →+* Matrix (Fin a) (Fin a) (Om l)) :=
    fun A B h => Matrix.ext fun i j => f.injective (by simpa using congrFun (congrFun h i) j)
  have hM : ∀ g, f.mapMatrix (M g) = (r g : Matrix (Fin a) (Fin a) (Om l)) := fun g => Matrix.ext fun i j => rfl
  let ρ : G E Ω →* GL (Fin a) ↥L.1 :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hinj (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hinj (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hinj (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  refine ⟨L, ρ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_induced_rng.2 ((continuous_apply j).comp ((continuous_apply i).comp hr))
  · exact MonoidHom.ext fun g => Units.ext (hM g)

end GlobalTheory.GalFirstClause

open _root_.GlobalTheory

open scoped TensorProduct

namespace GlobalTheory.GalFirstClause.Emb

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def tensLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem tensLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    tensLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [tensLift]

theorem exists_approx (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖tensLift φ t - φ x‖ < ε ∧ ‖tensLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [tensLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : tensLift φ (t₁ + t₂) - φ (x₁ + x₂) = (tensLift φ t₁ - φ x₁) + (tensLift φ t₂ - φ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (tensLift φ t₁ - φ x₁) (tensLift φ t₂ - φ x₂)]
    · have e : tensLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (tensLift ψ t₁ - ψ x₁) + (tensLift ψ t₂ - ψ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (tensLift ψ t₁ - ψ x₁) (tensLift ψ t₂ - ψ x₂)]

theorem norm_tensLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖tensLift ψ t‖ ≤ ‖tensLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_approx φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖tensLift ψ t‖ ≤ ‖tensLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (tensLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - tensLift φ t‖ + ‖tensLift φ t‖ := by
    simpa using norm_add_le (φ x - tensLift φ t) (tensLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

theorem norm_eq_of_samePlace (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause.Emb

open scoped TensorProduct

theorem exists_isInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' := by
  intro l _ E Ω _ _ _ _ _ τ
  refine ⟨PI.CompDegEF.plOf τ, PI.CompDegEF.natCast_mem_plIdeal τ, ?_⟩
  intro A hA O _ _ _ Bw hj
  let jE : E →+* Om l := Bw.j.comp (algebraMap E Ω)
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 E, ‖jE (x : E)‖ < 1 ↔ x ∈ (PI.CompDegEF.plOf τ).asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_samePlace τ jE _ hw (fun x => Iff.rfl) hjE
  have hker : ∀ t ∈ RingHom.ker (tensLift jE), tensLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_tensLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (tensLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change tensLift jE (a ⊗ₜ y) ∈ _
      rw [tensLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (tensLift jE).range) := by
    haveI : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((tensLift jE).range : Set (Om l)) :=
    Submodule.isClosed_of_finiteDimensional (Subalgebra.toSubmodule (tensLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (tensLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change tensLift jE (1 ⊗ₜ x) = jE x; rw [tensLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (tensLift jE)) (tensLift τ) hker).comp
      (Ideal.quotientKerEquivRange (tensLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict Bw.LL.1.toSubalgebra (fun y => Bw.LL_split σ y), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (tensLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = tensLift jE (1 ⊗ₜ x)
    rw [tensLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (tensLift τ) hker ((Ideal.quotientKerEquivRange (tensLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = tensLift τ (1 ⊗ₜ x)
  rw [tensLift_tmul, map_one, one_mul]

end GlobalTheory.GalFirstClause.Emb

namespace GlobalTheory.GalFirstClause

open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Pst

theorem existsIsInduced : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (τ : E →+* Om l), ∃ w ∈ placesOver E l, ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        Induces Bw → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1, IsInduced Bw τ τ' :=
  Emb.exists_isInduced

end GlobalTheory.GalFirstClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesInjectiveAndExactness
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ParIndExact

theorem parInd_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ξ : Representation ℂ (Levi k m) X) (η : Representation ℂ (Levi k m) Y) (i : ξ.IntertwiningMap η), Function.Injective i → Function.Injective (parIndMap e i) ∧ ∀ (Z : Type) [AddCommGroup Z] [Module ℂ Z] (ζ : Representation ℂ (Levi k m) Z) (q : η.IntertwiningMap ζ), (∀ y, q y = 0 → ∃ x, i x = y) → ∀ φ, parIndMap e q φ = 0 → ∃ ψ, parIndMap e i ψ = φ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e X Y _ _ _ _ ξ η i hi
  have hval : ∀ (φ : IndSp e ξ) (g : GL n k), (parIndMap e i φ).1.1 g = i (φ.1.1 g) := fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hi ?_))
    rw [← hval, ← hval, hφψ]
  · intro Z _ _ ζ q hex φ hφ
    have h0 : ∀ g, q (φ.1.1 g) = 0 := fun g =>
      congrFun (congrArg (fun χ : IndSp e ζ => χ.1.1) hφ) g
    choose x hx using fun g => hex _ (h0 g)
    have hlaw : x ∈ indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := by
      intro p g
      apply hi
      rw [hx]
      have h1 := parInd_law e η φ p g
      rw [h1, ← hx g]
      show _ = i ((deltaHalf k m (leviProj k e p) : ℂ) • ξ (leviProj k e p) (x g))
      rw [map_smul, i.isIntertwining]
    let x' : indSpace (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) := ⟨x, hlaw⟩
    have hset : {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} =
        {g : GL n k | ind (parab k e) ((twist η (deltaHalf k m)).comp (leviProj k e)) g φ.1 = φ.1} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change x (y * g) = x y at hy
        change φ.1.1 (y * g) = φ.1.1 y
        rw [← hx, ← hx, hy]
      · intro h
        apply Subtype.ext
        funext y
        have hy := congrFun (congrArg Subtype.val h) y
        change φ.1.1 (y * g) = φ.1.1 y at hy
        change x (y * g) = x y
        apply hi
        rw [hx, hx, hy]
    have hsm : x' ∈ smoothPart (ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e))) := by
      have ho : IsOpen {g : GL n k | ind (parab k e) ((twist ξ (deltaHalf k m)).comp (leviProj k e)) g x' = x'} := by
        rw [hset]; exact φ.2
      exact ho
    refine ⟨⟨x', hsm⟩, ?_⟩
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hval]
    exact hx g

end GlobalTheory.ParIndExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiExteriorTensorIsSubquotientOfForall
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

open PiTensorProduct

theorem piTensor_isSubquotient_of_forall : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ a, Group (Γ a)] (X Y : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (ρ' : ∀ a, Representation ℂ (Γ a) (Y a)), (∀ a, IsSubquotient (ρ a) (ρ' a)) → IsSubquotient (piTensor ρ) (piTensor ρ') := by
  intro α _ _ Γ _ X Y _ _ _ _ ρ ρ' h
  choose S f hf using h
  let ι : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ') :=
    { toLinearMap := PiTensorProduct.map fun a => (S a).toSubmodule.subtype
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        rfl }
  let π : (piTensor fun a => (S a).toRepresentation).IntertwiningMap (piTensor ρ) :=
    { toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
      isIntertwining' := fun g => by
        apply PiTensorProduct.ext
        ext x
        simp [piTensor_tprod]
        congr 1
        funext a
        exact (f a).isIntertwining _ _ (g a) (x a) }
  have hι : Function.Injective ι := by
    choose r hr using fun a => LinearMap.exists_leftInverse_of_injective (S a).toSubmodule.subtype
      (S a).toSubmodule.ker_subtype
    have : (PiTensorProduct.map r) ∘ₗ (PiTensorProduct.map fun a => (S a).toSubmodule.subtype)
        = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hr]
      exact PiTensorProduct.map_id
    exact Function.LeftInverse.injective (g := PiTensorProduct.map r) fun z => LinearMap.congr_fun this z
  have hπ : Function.Surjective π := by
    show Function.Surjective (PiTensorProduct.map fun a => (f a).toLinearMap)
    rw [← LinearMap.range_eq_top]
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    choose y hy using fun a => hf a (x a)
    exact ⟨PiTensorProduct.tprod ℂ y, by
      show PiTensorProduct.map _ _ = _
      rw [PiTensorProduct.map_tprod]
      congr 1
      funext a
      exact hy a⟩
  exact (IsSubquotient.of_surjective π hπ).trans (IsSubquotient.of_injective ι hι)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PropertyDescendsFiniteLengthToIrreducibleSubquot
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExactIrr

theorem main : ∀ (H : Type) [Group H] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (P : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y], Representation ℂ H Y → Prop), HasFiniteLength ρ → (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y'] (σ : Representation ℂ H Y) (σ' : Representation ℂ H Y') (f : σ.IntertwiningMap σ'), Function.Injective f → P Y σ → P Y' σ') → (∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ H Y), P Y σ → Nontrivial Y) → (∀ A B : Subrepresentation ρ, B ≤ A → P _ A.toRepresentation → P _ B.toRepresentation ∨ P _ (subQuot A B)) → P V ρ → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (σ : Representation ℂ H Y), σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ P Y σ := by
  intro H _ V _ _ ρ P hl hinj hnt hsplit hP
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded ρ).1 hl
  let j : ρ.IntertwiningMap (⊤ : Subrepresentation ρ).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  have hjinj : Function.Injective j := fun a b h => congrArg Subtype.val h
  have hTop : P _ (⊤ : Subrepresentation ρ).toRepresentation := hinj _ _ _ _ _ hjinj hP
  obtain ⟨A, hA, hAmin⟩ := hLT.has_min {A : Subrepresentation ρ | P _ A.toRepresentation} ⟨⊤, hTop⟩
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    have hnt' := hnt _ _ hA
    have : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    exact not_subsingleton _ this
  obtain ⟨B, hBA, hB⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hAbot)
  rcases hsplit A B hB.le hA with h | h
  · exact absurd hB.lt (hAmin B h)
  · exact ⟨_, _, _, subQuot A B, isIrreducible_subQuot hB,
      ⟨A, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩, h⟩

end GlobalTheory.ExactIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompl

theorem exists_ringEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧ Continuous i.symm ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro L _ _ _ s

  have hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x :=
    fun x => PI.CompAtExist.muV_eq s x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf

  let g : maximalRealSubfield L →+* s.w.adicCompletion L :=
    (algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)
  have hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact s.i.commutes a
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hcomp y⟩
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have he : ∀ y, e.symm y = ψ y := fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)
  refine ⟨e.symm, ?_, ?_, fun x => ?_⟩
  · exact hψc.congr fun y => (he y).symm
  · exact hφc
  · have h := e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)
    exact (congrArg e.symm (hφ x)).symm.trans h

end GlobalTheory.SplitCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryWeightModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.UnitaryWeightModels

theorem rowTwU_of_models : OrbitPlaces.OrbitLetterBoundsAll 11 1 → ∀ {eps : ℝ} (Fm : FamP eps),
    (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∃ E : OrbitPlaces.Ent (Fm.D x i),
      OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) E) →
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ModelsOK (Fm.D x i) (Fm.Gy x i) (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw) →
    RowTwU Fm := by
  rintro h01 eps Fm ⟨xa, ha⟩ ⟨xb, hb⟩
  have hCL : OrbitPlaces.CLarge 11 1 Fm.GK Fm.cX.err :=
    OrbitPlaces.cLarge_of_fixed Fm.fixed.2.2.2.2.1 Fm.fixed.2.2.2.2.2.1 Fm.fixed.2.1
      (by rw [Fm.fixed.2.2.1]; norm_num)
  refine ⟨max xa xb, fun x hx h1 i => ?_⟩
  obtain ⟨E, hS⟩ := ha x (le_trans (le_max_left _ _) hx) h1 i
  obtain ⟨h0, LC, hLC⟩ := hb x (le_trans (le_max_right _ _) hx) h1 i
  exact ⟨LC,
    GlobalTheory.Proof.ColumnWeightComparison.cmpV_of_cmpLite _ _ _ _ _ LC h0 fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).1,
    _root_.GlobalTheory.TwU.SiteSys.sysTw_sites _ _ (Fm.gatT x i) _ _ _ _ _ _ _ E LC (Fm.latTied x h1 i) (Fm.ex x h1 i).fills_all
      (Fm.ex x h1 i).fdef h01 hS hCL fun μ hU u w hg hQ => (hLC μ hU u w hg hQ).2⟩

end GlobalTheory.Proof.UnitaryWeightModels
end

