module

public import Mathlib
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Bundle0002
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Bundle0001
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.AutomorphicForms.Bundle0016

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AdelicUnitaryGroups
section
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped _root_.RestrictedProduct NumberField.AdeleRing

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Congr

variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

attribute [local instance] tensorTopology

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S := by
  let b := Module.finBasis K E
  let f := unitaryMap K E H e.toAlgHom
  let f' := unitaryMap K E H e.symm.toAlgHom
  have hrepr :
      (∀ z : R ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis S b).repr (tensorMap E e.toAlgHom z) k =
          e ((Algebra.TensorProduct.basis R b).repr z k)) ∧
      (∀ z : S ⊗[K] E, ∀ k,
        (Algebra.TensorProduct.basis R b).repr (tensorMap E e.symm.toAlgHom z) k =
          e.symm ((Algebra.TensorProduct.basis S b).repr z k)) := by
    constructor <;> intro z k <;> induction z using TensorProduct.inductionOn with
    | tmul r x => simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hcoords :
      (∀ g p, unitaryCoords H S b (f g) p = e (unitaryCoords H R b g p)) ∧
      (∀ g p, unitaryCoords H R b (f' g) p = e.symm (unitaryCoords H S b g p)) := by
    exact ⟨fun g ⟨i, j, k⟩ => hrepr.1 (unitaryMat g i j) k,
      fun g ⟨i, j, k⟩ => hrepr.2 (unitaryMat g i j) k⟩
  have htensor :
      Continuous (tensorMap (E := E) e.toAlgHom) ∧
        Continuous (tensorMap (E := E) e.symm.toAlgHom) := by
    constructor
    · apply (tensorCoordsHomeomorph S b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he.comp ((continuous_apply k).comp (tensorCoordsHomeomorph R b).continuous)
      change Continuous (fun z => e (tensorCoordsHomeomorph R b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.1] using hk
    · apply (tensorCoordsHomeomorph R b).isEmbedding.continuous_iff.mpr
      refine continuous_pi fun k => ?_
      have hk := he'.comp ((continuous_apply k).comp (tensorCoordsHomeomorph S b).continuous)
      change Continuous (fun z => e.symm (tensorCoordsHomeomorph S b z k)) at hk
      simpa only [Function.comp_apply, tensorCoordsHomeomorph_apply, hrepr.2] using hk
  refine
    { toFun := f
      invFun := f'
      left_inv := ?_
      right_inv := ?_
      map_mul' := map_mul f
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro g
    apply unitaryCoords_injective H R b
    funext p
    rw [hcoords.2, hcoords.1, e.symm_apply_apply]
  · intro g
    apply unitaryCoords_injective H S b
    funext p
    rw [hcoords.1, hcoords.2, e.apply_symm_apply]
  · have hm : Continuous fun M : Matrix ι ι (R ⊗[K] E) => M.map (tensorMap E e.toAlgHom) :=
      continuous_id.matrix_map htensor.1
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f g : GL ι (S ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))
  · have hm : Continuous fun M : Matrix ι ι (S ⊗[K] E) => M.map (tensorMap E e.symm.toAlgHom) :=
      continuous_id.matrix_map htensor.2
    apply continuous_induced_rng.2
    rw [Units.continuous_iff]
    refine ⟨hm.comp (Units.continuous_val.comp continuous_subtype_val), ?_⟩
    change Continuous (fun g => ((f' g : GL ι (R ⊗[K] E))⁻¹).val)
    simp only [← Subgroup.coe_inv, ← map_inv]
    exact hm.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv))

theorem unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap K E H e.toAlgHom g := rfl

end Congr

variable [NumberField K]

variable (K) in
def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl

variable (K) in
def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl

variable (K) in
def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable (K) in
def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in
def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.TraceFormulaWeil
section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal NNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace RightCosetSpace

section Unimodular

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]


omit [LocallyCompactSpace H] [T2Space H] in
theorem isFundamentalDomain_preimage_mul_right (L : Subgroup H) [DiscreteTopology L]
    (ν : Measure H) (g : H) :
    IsFundamentalDomain L ((· * g) ⁻¹' fundamentalDomain L) ν := by
  refine IsFundamentalDomain.mk' ((measurableSet_fundamentalDomain L).preimage
    (measurable_mul_const g)).nullMeasurableSet fun h => ?_
  obtain ⟨l, hl, hlu⟩ := existsUnique_smul_mem_fundamentalDomain L (h * g)
  refine ⟨l, ?_, fun l' hl' => hlu l' ?_⟩
  · show (l • h) * g ∈ fundamentalDomain L
    rw [smul_mul_assoc]
    exact hl
  · have hl'' : (l' • h) * g ∈ fundamentalDomain L := hl'
    rw [smul_mul_assoc] at hl''
    exact hl''

theorem isMulRightInvariant_of_compactSpace (L : Subgroup H) [DiscreteTopology L]
    [CompactSpace (RightCosetSpace L)] (ν : Measure H) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  constructor
  intro g
  have hD := isFundamentalDomain_fundamentalDomain L ν
  have h0 : ν (fundamentalDomain L) ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have htop : ν (fundamentalDomain L) ≠ ∞ := by
    rw [← quotientMeasure_univ ν hD]
    exact measure_ne_top _ _
  set c : ℝ≥0 := Measure.haarScalarFactor (Measure.map (· * g) ν) ν
  have hc : Measure.map (· * g) ν = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map (· * g) ν (fundamentalDomain L) = ν (fundamentalDomain L) := by
    rw [Measure.map_apply (measurable_mul_const g) (measurableSet_fundamentalDomain L)]
    exact (isFundamentalDomain_preimage_mul_right L ν g).measure_eq hD
  have hc1 : c = 1 := by
    rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have : (c : ℝ≥0∞) * ν (fundamentalDomain L) = 1 * ν (fundamentalDomain L) := by
      rw [h2, one_mul]
    rwa [ENNReal.mul_left_inj h0 htop, ENNReal.coe_eq_one] at this
  rw [hc, hc1, one_smul]


omit [T2Space H] in
theorem inv_eq_self_of_isMulRightInvariant (ν : Measure H) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.inv = ν := by
  set c : ℝ≥0 := Measure.haarScalarFactor ν.inv ν
  have hc : ν.inv = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : Measure.map Inv.inv (Measure.map Inv.inv ν) = (c ^ 2 : ℝ≥0) • ν := by
    rw [← Measure.inv_def ν, hc, Measure.map_smul, ← Measure.inv_def ν, hc, smul_smul, pow_two]
    exact continuous_inv.measurable.aemeasurable
  have hν : ν = (c ^ 2 : ℝ≥0) • ν := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h2
    simpa only [inv_involutive, Involutive.comp_self, Measure.map_id] using h2
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have h3 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * ν K = 1 * ν K := by
    conv_rhs => rw [hν]
    simp
  have h4 : ((c ^ 2 : ℝ≥0) : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj ((isOpen_interior.measure_pos ν K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
      K.isCompact.measure_lt_top.ne).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

end Unimodular

section Weil

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]

end Weil

end RightCosetSpace

end

end GroundTheory.Automorphic
end

