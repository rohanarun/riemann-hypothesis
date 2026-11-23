module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0017

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace BoundedSectionTransfer

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_C (r : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) : g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hg]
  refine ⟨fun h ↦ C_eq_zero.mp ((mul_eq_zero.mp h).resolve_right
    (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero k))), fun h ↦ by rw [h, C_0, zero_mul]⟩

theorem aeval_xpow [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (ArakelovGeometry.xpow c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [ArakelovGeometry.xpow, map_prod]

end BoundedSectionTransfer

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSectionNormSqExtensionX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SectionNormSqExtension.closed : SectionNormSqExtension.Statement :=
  SectionNormSqExtension.proof LeviLogFlat.proof LeviHolPerturb.proof LeviCompHol.proof LeviFSInvariant.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StProjChartHolo
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ProjChartHolo.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)), IsCompatChart M.atlas e →
    ∀ γ : ℂ → (Σ k, ι k) → ℂ, AnalyticAt ℂ γ 0 → (∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y)) →
      M.proj (γ 0) ∈ e.source → AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0

end GroundTheory.Heights₂.Heights.NineStatements
end
end

