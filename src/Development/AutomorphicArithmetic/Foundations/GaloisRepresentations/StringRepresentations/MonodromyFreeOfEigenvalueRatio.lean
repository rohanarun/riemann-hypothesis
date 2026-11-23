module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0037
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open _root_.GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace UpperTheory.GalN

section Lin
variable {V : Type} [AddCommGroup V] [Module ℂ V]

end Lin

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def EV (a : WDRep h V) (χ : ↥(Ine (F := E) A) → ℂ) (v : V) : Prop := ∀ s, a.ρ (ineIncl h s) v = χ s • v

def Win (a : WDRep h V) (S : Set ℝ) : Prop :=
  ∀ χ, (∀ v, EV a χ v → a.N v = 0) → ∀ r v, EV a χ v → v ∈ absSpace (a.ρ (frob h)) r → v ≠ 0 → r ∈ S

end UpperTheory.GalN
