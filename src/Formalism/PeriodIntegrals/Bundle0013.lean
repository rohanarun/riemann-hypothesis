module

public import Formalism.PeriodIntegrals.Bundle0011
public import Mathlib
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PeriodIntegrals.JointBlockShapes.JointShape
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.BesselDeriv
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

section

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def thetaH (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  -(Hpk k r * Xᴴ * Hpk k r)

def dsigC (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  dsig (k := k) (r := r) σ ((1 / 2 : ℂ) • (X + thetaH k r X)) v +
    Complex.I • dsig (k := k) (r := r) σ ((-(Complex.I / 2)) • (X - thetaH k r X)) v

end

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.BesselLevi
section
noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace PI.BesselLevi

def BesselLevi : Prop :=
  ∀ (k r : ℕ) (T : ℝ), 0 < T → ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    s ∈ UH (Hpk k r) →
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → s i (eI k r a) = if i = eI k r a then 1 else 0) →
    (∀ i : Fin (2 * r + k + 1), r ≤ i.val →
      (s *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) i =
        (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) i) →
    s ∈ Sset k r (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))

end PI.BesselLevi
end
end

-- bundled from Formalism.PeriodIntegrals.FockDegreeTwoParts
section
noncomputable section

open Matrix FockH1Action

namespace PI.FockDegreeTwoParts

def WtDeg : Prop := ∀ p q r s : ℕ,
  (∀ d (μ : Ix p q → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct1 p q r s) μ P →
    degW (cPair r s) μ ≤ d) ∧
  (∀ d (μ : Ix r s → ℚ) P, P ∈ homog (Ix p q × Ix r s) d → IsHW (fockAct2 p q r s) μ P →
    degW (cPair p q) μ ≤ d)

def OneDeg : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
    (∀ Z : Mat r s, IsPC Z → minusPart ((fockAct2 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
  (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
    (∀ Z : Mat p q, IsPC Z → minusPart ((fockAct1 p q r s) Z) P = 0) →
    ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d)

def JointMult : Prop := ∀ p q r s : ℕ,
  (∀ (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s)) = 1) ∧
    (¬ JointShape p q r s μ μ' →
      hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (Jset p q r s) = ⊥))

def HarmSplit : Prop := ∀ p q r s : ℕ,
  (∀ (u1 u2 : Bool), (u1 || u2) = true → ∀ d : ℕ,
    homog (Ix p q × Ix r s) (d + 2) =
      (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (lowKer p q r s u1 u2)) ⊔
      Submodule.span ℂ (raised p q r s u1 u2 d))

end PI.FockDegreeTwoParts
end
end

-- bundled from Formalism.PeriodIntegrals.FoldDCUnfold
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldDCUnfold

def FoldDCUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
    Formalism.L2.SG.FoldBound.IsRightTransversal Γ S' D' →
  ∀ (R : Set G), Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (Formalism.L2.SG.PoincareSeriesSquareIntegrable.stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (g h : G → ℝ≥0∞), Measurable g → Measurable h →
    (∀ s ∈ S, ∀ y : G, g (s * y) = g y) → (∀ s ∈ S', ∀ y : G, h (s * y) = h y) →
    (∫⁻ x in FΓ, (∑' δ : D, g ((δ : G) * x)) * (∑' δ' : D', h ((δ' : G) * x)) ∂μ)
      = ∑' r : R, ∫⁻ x in Fs r, g x * h ((r : G)⁻¹ * x) ∂μ

end PI.FoldDCUnfold
end

-- bundled from Formalism.PeriodIntegrals.FoldMult
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldMult

def FoldMult : Prop :=
  ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G), DiscreteTopology Γ →
  ∀ (Ω : Set G), IsCompact Ω → (1 : G) ∈ Ω →
    (∀ x : G, 1 ≤ Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    (∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω x < ⊤) ∧
    (∀ γ ∈ Γ, ∀ x : G, Formalism.L2.SG.FoldBound.mult Γ Ω (γ * x) = Formalism.L2.SG.FoldBound.mult Γ Ω x) ∧
    Measurable (Formalism.L2.SG.FoldBound.mult Γ Ω)

end PI.FoldMult
end

-- bundled from Formalism.PeriodIntegrals.FoldUnfold
section
open MeasureTheory
open scoped ENNReal NNReal

namespace PI.FoldUnfold

def FoldUnfold : Prop :=
  ∀ (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S : Subgroup G) [Countable Γ], S ≤ Γ →
  ∀ (F : Set G), IsFundamentalDomain S F μ →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (D : Set G), Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D →
  ∀ (f : G → ℝ≥0∞), Measurable f → (∀ s ∈ S, ∀ y : G, f (s * y) = f y) →
    (∫⁻ x in FΓ, ∑' δ : D, f ((δ : G) * x) ∂μ) = ∫⁻ y in F, f y ∂μ

end PI.FoldUnfold
end

-- bundled from Formalism.PeriodIntegrals.LocJacTyp
section
noncomputable section

namespace PI.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0

end Meas

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

end Frames

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}

def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))

end Sets

section Stmt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

end Stmt

end PI.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.LowCyc
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

def LowSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w → w ∈ smoothVecs (k := k) (r := r) σ

def SmoothCyc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H), IsHCParam lam →
    IsDSHpk k r ε lam σ → IsLowUnitH k r ε lam σ w →
    ∀ x ∈ smoothVecs (k := k) (r := r) σ,
    ∀ Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)),
    (∀ w' ∈ Ws, ∀ Y ∈ w', InLieHpk k r Y) → ∀ δ : ℝ, 0 < δ →
    ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ i, g i ∈ UH (Hpk k r)) ∧
      (Ws.map fun w' => ‖dsigW (k := k) (r := r) σ w' (x - ∑ i, c i • σ (g i) w)‖).sum < δ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.OmFibreUniq
section
noncomputable section

namespace PI.OmFibreUniq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def dX (a : ℕ) : Measure (TupV (E := E) v n a) :=
  if h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ then h.choose else 0

def dT (a : ℕ) : Measure (HermR (Fv F v) σ a) :=
  if h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν then h.choose else 0

def IndepV (a : ℕ) : Set (TupV (E := E) v n a) := {X | LinearIndependent (Fv F v ⊗[F] E) X}

def IsOm (a : ℕ) (fib : HermR (Fv F v) σ a → Measure (TupV (E := E) v n a)) : Prop :=
  IsFibreFamily (dX σ J ψ v a) (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a)
    (dT σ ψ v a) Set.univ fib

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def OmUnique (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ fib, IsOm σ J ψ v a fib) ∧ ∀ fib fib', IsOm σ J ψ v a fib → IsOm σ J ψ v a fib' → fib = fib'

end Meas

end PI.OmFibreUniq
end
end

-- bundled from Formalism.PeriodIntegrals.SelfDualBridge
section
noncomputable section

namespace PI.SelfDualBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))

end Meas

end PI.SelfDualBridge
end
end

-- bundled from Formalism.PeriodIntegrals.SqPair
section
noncomputable section
open NumberField Matrix

namespace PI.SqPair

open Formalism.L2.PairingIndexBounds.Eq.SqG

def PLocal (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) (p : ℕ) : Prop :=
  ∃ e : Matrix (Fin N) (Fin N) E,
    (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
    ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
      ∀ y, (y ∈ L' ∨ y ∈ L'') →
        ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (s : E) • (M *ᵥ y) = (n : E) • m

def PLocalAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∀ p : ℕ, p.Prime → PLocal E N L' L'' n p

def LocCartanPair : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ ϖ : R₀, Irreducible ϖ →
    ∀ (N : ℕ), Even N → ∀ (k : ℕ) (h : Matrix (Fin N) (Fin N) R),
      (h.map σ)ᵀ * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) →
      ∃ e f : Matrix (Fin N) (Fin N) R, e * e = e ∧ (e.map σ)ᵀ = 1 - e ∧ e * h = h * f

end PI.SqPair
end
end

-- bundled from Formalism.PeriodIntegrals.StdCharTR
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PI.StdCharTR

def Target : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

end PI.StdCharTR
end
end

