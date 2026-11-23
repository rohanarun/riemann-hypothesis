module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449

@[expose] public section

noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

section Input

variable (D : D7) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
  (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)

end Input

end GlobalTheory.HTW.Rec.Model
