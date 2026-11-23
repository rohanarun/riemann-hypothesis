module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def SplW (c : G E Ω → ℂ) (t : ℕ) (y : WD h) : Prop :=
  ∃ a b : WD h, y = a.lpSum b ∧ b.lpDim = t ∧ b.mono0 ∧ ∀ σ ∈ Ine (F := E) A, b.inePol σ = (X - C (c σ)) ^ t

structure Aw (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y
  spl : ∀ (u : WD h) (c : G E Ω → ℂ) (t : ℕ), ∀ γ ∈ Ine (F := E) A,
    ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t → SplW c t (y.lpSum u) → SplW c t (x.lpSum u)

structure Ab (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim
  mono : y.mono0 → x.mono0
  ine : y.mono0 → (∀ g : ↥(Weil h), (g : G E Ω) ∈ ⁅Ine (F := E) A, Ine (F := E) A⁆ → LocalGlobalAboveLAlt.Triv y g) →
    ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

end UpperTheory.GalN
