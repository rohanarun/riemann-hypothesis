module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
public import GroundTheory.AutomorphicForms.GL2.Bundle0003
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
section
namespace GroundTheory.Automorphic.GJMatrix

open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Matrix
open scoped NumberField.AdeleRing

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)


variable {K n} in
def matrixCoordEquiv {X : Type*} : Matrix (Fin n) (Fin n) X ≃ (Fin n × Fin n → X) where
  toFun := GroundTheory.Automorphic.GJMatrix.matrixCoord
  invFun z := Matrix.of fun i j ↦ z (i, j)
  left_inv _ := rfl
  right_inv _ := rfl


variable {K n} in
def matrixCoordTEquiv {X : Type*} : Matrix (Fin n) (Fin n) X ≃ (Fin n × Fin n → X) where
  toFun := GroundTheory.Automorphic.GJMatrix.matrixCoordT
  invFun z := Matrix.of fun i j ↦ z (j, i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem trace_mul_eq_sum' {R : Type*} [CommRing R] (x y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (y * x) = ∑ p, GroundTheory.Automorphic.GJMatrix.matrixCoordT y p * GroundTheory.Automorphic.GJMatrix.matrixCoord x p := by
  rw [trace_mul_comm, trace_mul_eq_sum]
  exact Finset.sum_congr rfl fun p _ ↦ mul_comm _ _

section Perm

variable {K} {ι : Type*} [Fintype ι]

theorem comp_perm_mem_schwartzBruhatPi (σ : ι ≃ ι) {F : (ι → 𝔸[K]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := K) (ι := ι)) : (fun z ↦ F (fun i ↦ z (σ i))) ∈ schwartzBruhatPi (K := K) (ι := ι) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    set L : (ι → mixedSpace K) ≃L[ℝ] (ι → mixedSpace K) :=
      (LinearEquiv.funCongrLeft ℝ (mixedSpace K) σ).toContinuousLinearEquiv
    have hL : ∀ u, L u = fun i ↦ u (σ i) := fun u ↦ rfl
    have hcont : Continuous fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ i) :=
      continuous_pi fun i ↦ continuous_apply (σ i)
    have hcont' : Continuous fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ.symm i) :=
      continuous_pi fun i ↦ continuous_apply (σ.symm i)
    have hemb : Topology.IsClosedEmbedding fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ i) :=
      Function.LeftInverse.isClosedEmbedding (f := fun z : ι → 𝔸ᶠ[K] ↦ fun i ↦ z (σ.symm i))
        (fun z ↦ funext fun i ↦ by simp) hcont' hcont
    have hg' : (fun z : ι → 𝔸ᶠ[K] ↦ g fun i ↦ z (σ i)) ∈ finiteSchwartzBruhatPi K :=
      ⟨hg.1.comp_continuous hcont, hg.2.comp_isClosedEmbedding hemb⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) hg'
      using 1
    funext z
    simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, hL]
    rfl
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

end Perm

def adelicMatrixMeasure : Measure (Matrix (Fin n) (Fin n) 𝔸[K]) :=
  matrixMeasure (adeleMeasure K)

def matrixSchwartzBruhat : Submodule ℂ (Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :=
  (schwartzBruhatPi (K := K) (ι := Fin n × Fin n)).comap
    (LinearMap.funLeft ℂ ℂ (matrixCoordEquiv (n := n) (X := 𝔸[K])).symm)

variable {K n}

theorem mem_matrixSchwartzBruhat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} :
    Φ ∈ matrixSchwartzBruhat K n ↔
      (fun z : Fin n × Fin n → 𝔸[K] ↦ Φ (Matrix.of fun i j ↦ z (i, j))) ∈
        schwartzBruhatPi (K := K) (ι := Fin n × Fin n) :=
  Iff.rfl


variable (K) in
def adelicMatrixFourier (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    ℂ :=
  ∫ x, Φ x * (adelicChar K (Matrix.trace (x * y)) : ℂ) ∂adelicMatrixMeasure K n

def coordFun (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) : (Fin n × Fin n → 𝔸[K]) → ℂ :=
  fun z ↦ Φ (Matrix.of fun i j ↦ z (i, j))

theorem coordFun_matrixCoord (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (x : Matrix (Fin n) (Fin n) 𝔸[K]) : coordFun Φ (GroundTheory.Automorphic.GJMatrix.matrixCoord x) = Φ x := rfl

theorem integral_matrixCoord (g : (Fin n × Fin n → 𝔸[K]) → ℂ) :
    ∫ x, g (GroundTheory.Automorphic.GJMatrix.matrixCoord x) ∂adelicMatrixMeasure K n = ∫ z, g z ∂adeleMeasurePi K :=
  (measurePreserving_matrixCoord (n := Fin n) (adeleMeasure K)).integral_comp
    (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm.measurableEmbedding g

theorem integral_matrixCoordT (g : (Fin n × Fin n → 𝔸[K]) → ℂ) :
    ∫ x, g (GroundTheory.Automorphic.GJMatrix.matrixCoordT x) ∂adelicMatrixMeasure K n = ∫ z, g z ∂adeleMeasurePi K := by
  have hT : GroundTheory.Automorphic.GJMatrix.matrixCoordT (n := Fin n) (X := 𝔸[K]) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ ↦ 𝔸[K]) (Equiv.prodComm (Fin n) (Fin n))) ∘
        ⇑(MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm := by
    funext x p
    simp only [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, MeasurableEquiv.coe_mk, GroundTheory.Automorphic.GJMatrix.matrixCoordT]
    rfl
  have hemb : MeasurableEmbedding (GroundTheory.Automorphic.GJMatrix.matrixCoordT (n := Fin n) (X := 𝔸[K])) := by
    rw [hT]
    exact (MeasurableEquiv.piCongrLeft (fun _ ↦ 𝔸[K])
      (Equiv.prodComm (Fin n) (Fin n))).measurableEmbedding.comp
      (MeasurableEquiv.curry (Fin n) (Fin n) 𝔸[K]).symm.measurableEmbedding
  exact (measurePreserving_matrixCoordT (n := Fin n) (adeleMeasure K)).integral_comp hemb g

theorem adelicMatrixFourier_eq (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ)
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    adelicMatrixFourier K Φ y = adelicFourierPi K (coordFun Φ) (GroundTheory.Automorphic.GJMatrix.matrixCoordT y) := by
  rw [adelicMatrixFourier, adelicFourierPi, ← integral_matrixCoord]
  simp only [trace_mul_eq_sum, coordFun_matrixCoord]

theorem coordFun_adelicMatrixFourier (Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ) :
    coordFun (adelicMatrixFourier K Φ) =
      fun z ↦ adelicFourierPi K (coordFun Φ) (fun p ↦ z p.swap) := by
  funext z
  rw [coordFun, adelicMatrixFourier_eq]
  rfl

theorem adelicMatrixFourier_mem {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) : adelicMatrixFourier K Φ ∈ matrixSchwartzBruhat K n := by
  rw [mem_matrixSchwartzBruhat]
  change coordFun (adelicMatrixFourier K Φ) ∈ _
  rw [coordFun_adelicMatrixFourier]
  exact comp_perm_mem_schwartzBruhatPi (Equiv.prodComm (Fin n) (Fin n))
    (adelicFourierPi_mem_schwartzBruhatPi (F := coordFun Φ) hΦ)

theorem adelicMatrixFourier_adelicMatrixFourier {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    adelicMatrixFourier K (adelicMatrixFourier K Φ) = fun x ↦ Φ (-x) := by
  funext x
  have h : adelicFourierPi K (adelicFourierPi K (coordFun Φ)) (GroundTheory.Automorphic.GJMatrix.matrixCoord x) =
      coordFun Φ (-GroundTheory.Automorphic.GJMatrix.matrixCoord x) :=
    congrFun (adelicFourierPi_adelicFourierPi (F := coordFun Φ) hΦ) (GroundTheory.Automorphic.GJMatrix.matrixCoord x)
  rw [adelicMatrixFourier, ← coordFun_matrixCoord Φ (-x), matrixCoord_neg, ← h, adelicFourierPi,
    ← integral_matrixCoordT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [adelicMatrixFourier_eq, trace_mul_eq_sum']

theorem poisson_matrix {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ} (hΦ : Φ ∈ matrixSchwartzBruhat K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K ↦ ‖Φ (ξ.map (algebraMap K 𝔸[K]))‖) ∧
      Summable (fun ξ : Matrix (Fin n) (Fin n) K ↦
        ‖adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K]))‖) ∧
      ∑' ξ : Matrix (Fin n) (Fin n) K, Φ (ξ.map (algebraMap K 𝔸[K])) =
        ∑' ξ : Matrix (Fin n) (Fin n) K, adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K])) := by
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (F := coordFun Φ) hΦ
  have eL : ∀ ξ : Matrix (Fin n) (Fin n) K, Φ (ξ.map (algebraMap K 𝔸[K])) =
      coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (matrixCoordEquiv ξ p)) := fun _ ↦ rfl
  have eR : ∀ ξ : Matrix (Fin n) (Fin n) K, adelicMatrixFourier K Φ (ξ.map (algebraMap K 𝔸[K])) =
      adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (matrixCoordTEquiv ξ p)) :=
    fun ξ ↦ by rw [adelicMatrixFourier_eq]; rfl
  simp only [eL, eR]
  refine ⟨(matrixCoordEquiv.summable_iff (f := fun z : Fin n × Fin n → K ↦
      ‖coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (z p))‖)).mpr h1,
    (matrixCoordTEquiv.summable_iff (f := fun z : Fin n × Fin n → K ↦
      ‖adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (z p))‖)).mpr h2, ?_⟩
  rw [matrixCoordEquiv.tsum_eq (fun z : Fin n × Fin n → K ↦
      coordFun Φ (fun p ↦ algebraMap K 𝔸[K] (z p))),
    matrixCoordTEquiv.tsum_eq (fun z : Fin n × Fin n → K ↦
      adelicFourierPi K (coordFun Φ) (fun p ↦ algebraMap K 𝔸[K] (z p)))]
  exact h3

end

end GroundTheory.Automorphic.GJMatrix
end

-- bundled from GroundTheory.AutomorphicForms.GL2.GodementSectionSplit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infChar (χ : HeckeCharacter K) : (InfiniteAdeleRing K)ˣ →* Circle :=
  χ.toIdele.comp ofInfinite

def infMod (a : (InfiniteAdeleRing K)ˣ) : ℝ :=
  ∏ w : InfinitePlace K, ‖(a : InfiniteAdeleRing K) w‖ ^ w.mult

def infVec (y : Fin 2 → InfiniteAdeleRing K) : Fin 2 → mixedSpace K :=
  fun i ↦ homeomorphMixedSpace K (y i)

def archSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (φ : (Fin 2 → mixedSpace K) → ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) : ℂ :=
  (infChar χ₁ (Matrix.GeneralLinearGroup.det g) : ℂ) *
    ((infMod (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s *
      ∫ a, φ (infVec (![0, (a : InfiniteAdeleRing K)] ᵥ*
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)))) *
        (infChar (χ₁ * χ₂⁻¹) a : ℂ) * ((infMod a : ℝ) : ℂ) ^ (2 * s) ∂infiniteIdeleMeasure K

theorem toInfinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toInfinite K ((IdeleGroup.prodEquiv K).symm p) = p.1 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).1 = p.1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toFinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toFinite K ((IdeleGroup.prodEquiv K).symm p) = p.2 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).2 = p.2
  rw [ContinuousMulEquiv.apply_symm_apply]

end

end GroundTheory.Automorphic.GodementSection
end

