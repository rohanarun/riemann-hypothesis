module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementA
public import Formalism.GaussJetBounds.Bundle0004
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0003

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.IncomingBounds hiding mvExp
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK)

section Defs

variable {K0 K : Type} [Field K0] [Field K] {ι : Type} {d N0 N1 : ℕ} [NeZero d]

def xOfZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (x : Bool × ι × Fin N0 × Fin N1) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  PowerSeries.subst
    (if x.1 = false then
      ∑ s : ZMod d, if s.val % 2 = 0 then
        MvPowerSeries.C (j (σ^[s.val] (oms x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K) else 0
    else
      ∑ s : ZMod d, if s.val % 2 = 0 then 0 else
        MvPowerSeries.C (j (σ^[s.val] (om x.2.1))) *
          (MvPowerSeries.X (s, x.2.2.1, x.2.2.2) : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K))
    (expF K l)

def thetaInZ (l : ℕ) (j : K0 →+* K) (σ : K0 →+* K0) (om oms : ι → K0)
    (Tht : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K) :
    MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K :=
  MvPowerSeries.subst (xOfZ l j σ om oms) Tht

def sumE [Fintype ι] (be : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K :=
  ∑ e : ι × Fin N0 × Fin N1, MvPowerSeries.subst
    (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
      MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K)) be

def conjJ {ν : ℕ} (j : K0 →+* K) (σ : K0 →+* K0) (c : Fin ν → K0) : Fin ν → ZMod (2 * ν) → K :=
  fun r s => j (σ^[s.val] (c r))

end Defs

def B0 : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d N0 N1 : ℕ) [NeZero d] (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d → Even d →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K0), OwOK d σ om oms →
      TrDual d σ om oms → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ d - 1) →
    ∀ U0 Φ : MvPowerSeries (Bool × ι × Fin N0 × Fin N1) K, Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 → Simeq Φ (sumE (MvPowerSeries.map j be0)) →
      ∃ U : MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K, Integral U ∧
        ∀ g : Formalism.DworkPowerSeriesWeights.ZV d N0 N1 → MvPowerSeries (Formalism.DworkPowerSeriesWeights.ZV d N0 N1) K,
          (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
          (∀ y, MvPowerSeries.subst g (entLog (K := K) l y) = MvPowerSeries.X y) →
          thetaInZ l j σ om oms (_root_.Formalism.DworkPowerSeriesWeights.mvExp (-Φ) * U0) =
            thetaZ g U (-1) (MvPowerSeries.map j (beMean l σ be0 om oms ζ))

def OneLetterHalf : Prop :=
  ∀ (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] (l : ℕ) (σ : K0 →+* K0),
    UnrOK K0 l σ →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 → ∀ ζ : K0, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ ph : PowerSeries K0,
      Simeq (MvPowerSeries.C (2 : K0) * ph)
        (MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0) →
      Simeq (ph : MvPowerSeries Unit K0) (MvPowerSeries.C ((2 : K0)⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => lgF K0 l)
          (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ))

def OmOKOf : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    (l ν : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K), UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) →
    ∀ om oms : Fin ν → K0, OwOK (2 * ν) σ om oms → TrDual (2 * ν) σ om oms →
      OmOK l ν (conjJ j σ om) (conjJ j σ oms)

def ThetaInZIsSSub : Prop :=
  ∀ (K0 K : Type) [Field K0] [Field K] (l ν r0 r1 : ℕ) [NeZero ν] (σ : K0 →+* K0) (j : K0 →+* K)
    (om oms : Fin ν → K0) (Tht : MvPowerSeries (Bool × Fin ν × Fin r0 × Fin r1) K),
    thetaInZ (d := 2 * ν) l j σ om oms Tht =
      MvPowerSeries.subst (Formalism.InvariantFactorPaths.G7.sSub (conjJ j σ om) (conjJ j σ oms) (expF K l)) Tht

end Formalism.L2.Th1.D
