module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace Ysupp.IrreducibleSupport

open _root_.GlobalTheory GlobalTheory.SerSys

section Chain

open GlobalTheory.LocGL

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

end Chain

end Ysupp.IrreducibleSupport
