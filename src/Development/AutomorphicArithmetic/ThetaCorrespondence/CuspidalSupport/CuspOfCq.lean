module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.GaloisStatementWeakOfFull

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open _root_.GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace UpperTheory.Lit.Car

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end

theorem weak' {D : D7} (h : GaloisRepresentationsWeak D.nd D.naut) : GaloisRepresentationsWeak D.nd D.naut := h
theorem weakA' {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    (h : GaloisRepresentationsWeak N A) : GaloisRepresentationsWeak N A := h

end UpperTheory.Lit.Car
