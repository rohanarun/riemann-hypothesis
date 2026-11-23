module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem woConj (k : Lev.WO ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : Lev.WO ι r' y := IsWDOf.of_conj hl P hP k

end UpperTheory.GalN.V
