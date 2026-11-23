module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import Formalism.LocalToGlobal.KernelLattices.KerStd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def SeedWtU : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), (Qbar l ≃+* ℂ) →
    HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Submodule ℂ (UA E a → ℂ) → Prop

def SeedWtU.noCondition : SeedWtU := fun _ _ _ _ _ _ _ _ _ _ _ _ => True

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def OverPl (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x ∈ w.asIdeal, ‖ι.symm (τ (x : E))‖ < 1

def SameWtAt (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SameWtOff (ι : Qbar l ≃+* ℂ) (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (∀ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u → Apart u w₀ ∧ Apart u v') →
    ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SeedWU2 (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU := SeedWtU.noCondition) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → SameWtOff ι w₀ v' U U' → Wt E l a ι w₀ v' U U' →
      Ty E l a w₀ U' → SphOffU w₀ S U' → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w)

theorem sameWtAt_of_off (ι : Qbar l ≃+* ℂ) {w₀ v' w : HeightOneSpectrum (𝓞 E)} {U U' : Submodule ℂ (UA E a → ℂ)}
    (h : SameWtOff ι w₀ v' U U') (hw : ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ u, OverPl ι τ u → u = w)
    (h₀ : Apart w w₀) (h' : Apart w v') : SameWtAt ι w U U' :=
  by
    unfold SameWtAt SameWtOff at *
    exact fun τ hτ lam => h τ (fun u hu => by rw [hw τ hτ u hu]; exact ⟨h₀, h'⟩) lam

end GlobalTheory.CongL

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
section
namespace GlobalTheory.NRows

structure HypothesesX : Prop where
  weil : GlobalTheory.Published.WeilRepresentationUnitaryPair
  ds : GlobalTheory.Published.DiscreteSeriesExists
  ana : GlobalTheory.Published.HarishChandraAnalyticity
  dsc : GlobalTheory.Published.DiscreteSeriesClassification
  trc : GlobalTheory.Published.CuspTraceClass
  dm : GlobalTheory.Published.DixmierMalliavinFactorisation
  flath : GlobalTheory.Published.FlathFactorisation
  pc : GlobalTheory.Published.PseudoCoefficientUpq
  hcc : GlobalTheory.Published.HarishChandraCharacters
  lc : GlobalTheory.Published.LanglandsClassification
  lw : GlobalTheory.Published.LabesseWaldspurger
  sw : GlobalTheory.Published.WeilSiegelFormulaUnitary
  ft : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm
  dbl : GlobalTheory.Published.DoublingMethod
  udbl : GlobalTheory.Published.UnramifiedDoublingGL
  hl : GlobalTheory.Published.HeckeLPartialContinuation
  ht : GlobalTheory.HeightCounting.HtCard

end GlobalTheory.NRows
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
section
noncomputable section

namespace GlobalTheory.AtG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker
open scoped ComplexConjugate

def JetSplitAmb : Prop :=
  ∀ {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b))
      (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Even a → Even b → Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' →
      s.StdAtP p N → s.StdAtP p N' → ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p →
      ¬ p ∣ D.host.d → (ambOf s B χ cD : Amb X).LaHyp a b S →
      ∀ (π : ℂ) (pE : 𝓞 X.E), Formalism.L2.AlgTh.IsQInt D.host.d π → π * conj π = (p : ℂ) → Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE →
      ∀ (c' : ℕ) (x : Formalism.L2.Col.HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ Formalism.L2.Col.divLat c' (Formalism.L2.Col.homAt S N N') → ∀ m : DVar X.Tau a b →₀ ℕ,
        ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1


open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound in
def TiesAt (D : D7) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup) : Prop :=
  ∃ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : _) (eta : _) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _),
    HostTie EX ∧ CharTie Ch mu0 eta sel ∧ AnTie D δ χ cD ∧
      ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ


open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat in
def RowPin {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : ColIn.Ok I) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) : Prop :=
  ∀ u : B.Word, ∃ e : (I.per l u a).Mt ≃ₗ[ℂ] (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Amb a,
    (a = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → HEq e ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMt u)) ∧ (a ≠ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.mu0 → e = (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).eMtTw u a) ∧
    (∀ v ∈ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Amb a → 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL,
      e (rowForm I l h u a z) = ∑ v ∈ ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Mtilde a).gen, (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.embLL ((c v : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL) : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.LL) • v

end GlobalTheory.AtG

end
end

