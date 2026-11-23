module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcross

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN.V
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
section
variable (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
end
theorem WitQ.weak_admissible_iso (e : RepIso r r') (h : _root_.UpperTheory.V.Z.Win.WitAQ ι r) : _root_.UpperTheory.V.Z.Win.WitAQ ι r' := by
  intro K _ _ _ _ _ _ h2 hi
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed F, haveI := IsAlgClosure.isAlgebraic (R := F) (K := Ω); Algebra.IsAlgebraic.tower_top (K := F) K⟩
  obtain ⟨g, hg⟩ := e
  have e' : RepIso (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) (r'.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) :=
    ⟨g, fun s => hg _⟩
  have hirr : IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) := by
    obtain ⟨a, ha⟩ := e'.symm'
    let A := Matrix.mulVecLin (a : Matrix (Fin n) (Fin n) (Qbar l))
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    have hinv := hi.2.2 (W.comap A) le_top (fun s v hv => by
      have hmem := hW s _ (show A v ∈ W from hv)
      rw [ha s] at hmem
      simpa [A, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hmem)
    have hsurj : Function.Surjective A := fun v =>
      ⟨((a⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v, by
        dsimp only [A]
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    have hmap := Submodule.map_comap_eq_of_surjective hsurj W
    rcases hinv with hbot | htop
    · left
      rw [← hmap, hbot, Submodule.map_bot]
    · right
      rw [← hmap, htop, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  exact (h K h2 hirr).weak_admissible_iso e'
theorem IsAutCsdN.weak_admissible_iso [IsCMField F] (e : RepIso r r') (h0 : AutCsd0 ι r') (h : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r) :
    _root_.UpperTheory.V.Z.Win.IsAutCsdA ι r' := ⟨h0, fun c => (h.2 (continuous_of_iso c e.symm')).weak_admissible_iso e⟩
end UpperTheory.GalN.V
end
end
