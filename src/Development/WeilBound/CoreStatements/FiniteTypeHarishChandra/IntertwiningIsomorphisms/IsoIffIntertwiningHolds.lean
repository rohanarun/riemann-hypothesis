module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0099
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0242

@[expose] public section

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem isIrr_of_simple (τ : FDRep ℂ Γ) [h : Simple τ] : IsIrr τ.ρ := (_root_.GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 Γ τ).1 h

theorem zIdemIdemCentral_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (hτ : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := _root_.GlobalTheory.CompanionTheory.TyFin.zIdemFacts.1 Γ τ hτ

theorem zIdemOrthogonal_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ)
    (h : ¬ Nonempty (τ ≅ σ)) : zIdem τ * zIdem σ = 0 := _root_.GlobalTheory.CompanionTheory.TyFin.zIdemFacts.2.1 Γ τ σ hτ hσ h

end Gen

section GeneralLinearIntegers

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]






end GeneralLinearIntegers

end ReciprocityTheory.Ty.Fin
