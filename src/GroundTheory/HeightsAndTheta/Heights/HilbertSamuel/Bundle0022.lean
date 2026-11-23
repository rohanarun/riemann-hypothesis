module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenericFibre.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (D : ℕ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Ix κ) ℚ ⧸
          (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) = ((D + 1 : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

def GenericFibreVar.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → IsProjVarF (KH.genIdeal y) D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGridSeparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine)

noncomputable section

def GridSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ Z : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ s ∈ chartLatNm y A.a τ, ∀ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0) ∧
      ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 → ∃ z ∈ Z, ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = u * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖ ≤
          ‖eval z (map (Int.castRingHom ℂ) g)‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHSMTransport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def matSubst {J : Type} [Fintype J] (B : Matrix J J ℚ) (b : MvPolynomial J ℚ) : MvPolynomial J ℚ :=
  aeval (fun i => ∑ j, C (B i j) * X j) b

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

def HSMTransport.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B →
    ∃ d' : HSMDatum D Ω κ, d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧
      ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ),
        resGram d' n b = resGram d n fun k => matSubst B (b k)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHeightsirationalHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockBirationalHilbert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → BlockBirational y k₀ → ∀ m : K → ℕ, ∃ c : ℕ, ∀ n : ℕ,
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else 0) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then (n : ℤ) else m k) ≤
        GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun k => if k = k₀ then ((n + c : ℕ) : ℤ) else 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbFnValueSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section ValueSpan

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) : Submodule ℚ Ω :=
  Submodule.span ℚ {s | ∃ g : MRing ι, IsMultiHomog g a ∧ aeval y g = s}

end ValueSpan

def HilbFnValueSpan.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun k => (a k : ℤ)) =
      (Module.finrank ℚ (valueSpan y a) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntegralAgainstPositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def IntegralAgainstPositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    P0 ≤ P → (∀ j, IsSemipositiveRel P0 P (L j)) → (∀ z ∈ mcPts P, g z ≤ 0) →
    ptsIntegral P (pot L) g ≤ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def NefOnGenericDeg (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ genDeg W 1 a

variable {Ω : Type} [Field Ω] [CharZero Ω]

def chartRingQ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)

def chartLatQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : Submodule ℚ Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingQ y c}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  smul_mem' := fun r s hs c hc => by
    rw [smul_mul_assoc]
    exact Subalgebra.smul_mem _ (hs c hc) r

end Objects

def KodairaGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a →
    0 < genDeg (mCoordIdeal y) D a →
    ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • a - 1) 1

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KodairaSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (M : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsNefBigDatum P0 y D M →
    ∃ (k : ℕ) (e : Ω) (C : ℝ), 1 ≤ k ∧ 0 ≤ C ∧ e ≠ 0 ∧ e ∈ chartLat y ((k : ℤ) • M.a - 1) 1 ∧
      IsBoundedH (mCoordIdeal y) y (HermLine.zcomb M (fsH ι) k (-1)) 1 (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKrullDimMatAct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KrullDimMatAct.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (J : Type) [Fintype J] (x : J → Ω) (B : Matrix J J ℚ), IsInvMat B →
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ (matAct B x)) = ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.AmpleV ℚ (KH.genIdeal y) N →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N) →
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat y (a • N) 1) ∧ KH.GeneratesOn y (a • N) x' ∧
        Birational (fun p : Σ _ : Unit, ι' => x' p.2)

section Inhabitant

end Inhabitant

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def LocalRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ),
    s ∈ chartLat y a n → z ∈ mcPts (mCoordIdeal y) →
    ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + n * a k) ∧ aeval y g = s * aeval y h ∧
      eval z (map (Int.castRingHom ℂ) h) ≠ 0

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

