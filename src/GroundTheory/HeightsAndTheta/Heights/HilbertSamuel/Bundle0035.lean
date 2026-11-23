module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def BergmanIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → Integrable (bergman W dV V n) dV.μ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockComplexGramMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    (fun n => blockCChi (d.withMetric A' P0' hdeg hc hle hp) n - blockCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * blockMetricInt d A') =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphImage
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockForms {κ : Type} (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ) : (Σ k, GlobalTheory κ k) → MRing ι :=
  fun q => ∑ i, C (M q i) * X ⟨k₀, i⟩

end Objects

def BlockGraphImage.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x →
    imageZ (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)) = coordIdeal ℤ x

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageArith.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsArithVar (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (D + 1)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageChi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockImageChi.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d₀.k₀) ℤ)
    (N : Matrix (ι d₀.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
    IsBlockImage d₀.y d₀.k₀ M N d'.x →
    (∀ z ∈ mcPts (mCoordIdeal d₀.y), d₀.A.h z = d'.m.ρ (blockMapC d₀.k₀ M z)) →
    (∀ g : (Ix (Fin r) → ℂ) → ℂ, ContinuousOn g {0}ᶜ → (∀ (c : ℂ) z, c ≠ 0 → g (c • z) = g z) →
      ∫ a, g (resPt d' a) ∂d'.dV = ∫ a, g (blockMapC d₀.k₀ M (blockPt d₀ a)) ∂d₀.dV) →
    ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = genDeg (mCoordIdeal y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageHilb.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsBlockImage y k₀ M N x → ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
          ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageInverse.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω) (J : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y →
      ∃ (F : MvPolynomial (Ix (Fin r)) ℤ) (e : ℕ) (G : MRing ι) (dG : K → ℕ),
        IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e) ∧ F ∉ coordIdeal ℤ x ∧
        IsMultiHomog G dG ∧ G ∉ mCoordIdeal y ∧
        (∀ z, eval z (map (Int.castRingHom ℂ) G) = eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F)) ∧
        (∀ u ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x), eval u (map (Int.castRingHom ℂ) F) ≠ 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), z ∉ mcPts J ∧ SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) u) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 → z ∉ mcPts J) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), ∀ z' ∈ mcPts (mCoordIdeal y),
          eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 →
          SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) (blockMapC k₀ M z') → SameOrbit z z')

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageMetrics
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def linPullMetric {κ J : Type} [Fintype κ] [Fintype J] (N : Matrix κ J ℤ)
    (hN : ∀ u : J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) : ConeMetric ℂ J where
  ρ u := (fsMetric (ι := κ)).ρ (fun i => ∑ j, (N i j : ℂ) * u j)
  pos u hu := (fsMetric (ι := κ)).pos _ fun h => hu (hN u h)
  smul c u := by
    have : (fun i => ∑ j, (N i j : ℂ) * (c • u) j) = c • fun i => ∑ j, (N i j : ℂ) * u j := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, (fsMetric (ι := κ)).smul]

def BlockImageMetrics.Statement : Prop :=
  (∀ (κ J : Type) [Fintype κ] [Fintype J] (N : Matrix κ (Ix J) ℤ)
      (hN : ∀ u : Ix J → ℂ, (fun i => ∑ j, (N i j : ℂ) * u j) = 0 → u = 0) (P : Ideal (MRing (GlobalTheory J))),
      IsSemipositiveRel ⊥ P (HermLine.ofCone (linPullMetric N hN))) ∧
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (k₀ : K) (P : Ideal (MRing ι)),
      IsSemipositiveRel ⊥ P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageTop.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (y : (Σ k, ι k) → Ω) (k₀ : K) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (M : Matrix (Ix κ) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω)
    (m : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ →
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsBlockImage y k₀ M N x → A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀ →
    IsSmoothHerm A → IsSmoothMetric m → (∀ z ∈ mcPts (mCoordIdeal y), A.h z = m.ρ (blockMapC k₀ M z)) →
    I K ι (mCoordIdeal y) (D + 1) (fun _ => A) = top I x m D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockRealGramComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def BlockRealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    (fun n => blockChi d n - blockCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A₀ A₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    A₀.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → A₁.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A₀ → IsSmoothHerm A₁ →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ C : ℝ, ∀ n : ℕ,
      |(Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) -
          mInt d.R.A (fun _ => blockInterpPot d A₀ A₁ t) (fun _ => 1) * (n : ℝ) ^ D / (D.factorial : ℝ)| ≤
        C * ((n : ℝ) + 1) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

