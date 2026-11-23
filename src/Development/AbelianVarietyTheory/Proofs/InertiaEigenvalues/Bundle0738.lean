module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0069
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqId
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeOne


open Classical in
theorem heckeFunI_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  intro L _ _ _ n v w Dv U hU W _ _ f hf
  have hfU : ∀ κ ∈ U, ∀ g, f (g * κ) = f g := fun κ hκ g => congrFun (hf κ hκ) g
  have key : ∀ x : GAf L n, TrivOutside {v} x →
      Dv.hval (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) (Dv.loc x) = if x ∈ U then 1 else 0 := by
    intro x hx
    have hg := _root_.GlobalTheory.LocalUnitary.loc_mem_GU L n v w Dv x
    unfold InertDatum.hval
    rw [dite_eq_left hg]
    by_cases hxU : x ∈ U
    · rw [if_pos hxU]
      have hK := _root_.GlobalTheory.InertKU.loc_mem_KU L n v w Dv x ((hU x hx).1 hxU) hg
      unfold Formalism.UG.dosetInd
      rw [Set.indicator_of_mem]
      · rfl
      · rw [DoubleCoset.mem_doubleCoset]
        exact ⟨_, hK, 1, one_mem _, by simp⟩
    · rw [if_neg hxU]
      unfold Formalism.UG.dosetInd
      apply Set.indicator_of_notMem
      intro hmem
      rw [DoubleCoset.mem_doubleCoset] at hmem
      obtain ⟨a, ha, b, hb, e⟩ := hmem
      have hK : (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
        rw [e, mul_one]; exact mul_mem ha hb
      have hK' := hK
      simp only [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf] at hK'
      apply hxU
      refine (hU x hx).2 (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv x hx ?_)
      intro i j
      exact GlobalTheory.InertUmax.entries_mem_of_range _ _ hK'.2 i j
  funext g
  unfold heckeFunI
  have h1 : TrivOutside {v} (1 : GAf L n) := by
    intro u _
    simp
  rw [finsum_eq_single _ ((1 : GAf L n) : GAf L n ⧸ U)]
  · have hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = ((1 : GAf L n) : GAf L n ⧸ U) ∧ TrivOutside {v} x := ⟨1, rfl, h1⟩
    rw [dite_eq_left hc]
    have hmem : hc.choose ∈ U := by
      have := QuotientGroup.eq.1 hc.choose_spec.1.symm
      simpa using this
    rw [key _ hc.choose_spec.2, if_pos hmem, one_smul, hfU _ hmem]
  · intro c hc1
    split_ifs with hc
    · rw [key _ hc.choose_spec.2, if_neg, zero_smul]
      intro hmem
      apply hc1
      rw [← hc.choose_spec.1]
      exact QuotientGroup.eq.2 (by simpa using U.inv_mem hmem)
    · rfl

end GlobalTheory.InertHeckeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]


variable (V K) in
def absOfVal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) : AbsoluteValue K ℝ where
  toFun x := if x = 0 then 0 else c ^ (vV V x)
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, vV_mul hx hy, zpow_add₀ hc0.ne']
  nonneg' x := by
    show 0 ≤ (if x = 0 then 0 else c ^ (vV V x))
    split_ifs
    · exact le_rfl
    · positivity
  eq_zero' x := by
    show (if x = 0 then 0 else c ^ (vV V x)) = 0 ↔ x = 0
    split_ifs with h
    · simp [h]
    · simp [h, zpow_ne_zero _ hc0.ne']
  add_le' x y := by
    show (if x + y = 0 then 0 else c ^ (vV V (x + y))) ≤
      (if x = 0 then 0 else c ^ (vV V x)) + (if y = 0 then 0 else c ^ (vV V y))
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    have px := zpow_pos hc0 (vV V x)
    have py := zpow_pos hc0 (vV V y)
    by_cases hxy : x + y = 0
    · simp only [hxy, hx, hy, if_true, if_false]; positivity
    simp only [hxy, hx, hy, if_false]
    rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith

theorem absOfVal_of_ne (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) {x : K} (hx : x ≠ 0) :
    absOfVal V K c hc0 hc1 x = c ^ (vV V x) := by
  show (if x = 0 then 0 else c ^ (vV V x)) = _
  simp [hx]

end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

theorem isReading_ext : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr),
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  intro p _ F _ _ φ T io k hk T' i hi j hj
  have hji : ∀ y, j (i y) = k y := fun y => by rw [← hj]; rfl
  refine ⟨fun a => by rw [RingHom.comp_apply, hji]; exact hk.comp a, fun x => ?_⟩
  obtain ⟨hfin, r, hr, hv⟩ := hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by simpa using hπ.ne_zero
  set ρ := ‖k (algebraMap T.V T.Fr π)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 ((map_ne_zero k).2 hπ0)
  have hρ1 : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv'⟩ := (hk.int _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv', map_one, mul_inv_cancel₀ hπ0]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ρ ^ ((1 : ℝ) / r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hρ0 _
  have hc1 : c < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hcr : c ^ r = ρ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  letI NF : NontriviallyNormedField T.Fr :=
    { NormedField.induced T.Fr ℂ_[p] k k.injective with
      non_trivial := ⟨(algebraMap T.V T.Fr π)⁻¹, by
        show 1 < ‖k (algebraMap T.V T.Fr π)⁻¹‖
        rw [map_inv₀, norm_inv]
        exact (one_lt_inv₀ hρ0).2 hρ1⟩ }
  have hnk : ∀ y : T.Fr, ‖y‖ = ‖k y‖ := fun y => rfl
  haveI : IsUltrametricDist T.Fr :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnk, hnk, hnk, map_add (f := _)]
      exact IsUltrametricDist.norm_add_le_max _ _
  haveI : CompleteSpace T.Fr := Formalism.MainNotions.ExistsIdealDenominator.complete_of_adic (O := T.V) (K := T.Fr) (fun y => hk.int y) inferInstance
  letI := i.toAlgebra
  haveI : FiniteDimensional T.Fr T'.Fr := hfin
  have e1 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective) (fun y => by
      show ‖j (i y)‖ = ‖y‖
      rw [hji, hnk]) x
  have e2 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := absOfVal T'.V T'.Fr c hc0 hc1.le) (fun y => by
      show absOfVal T'.V T'.Fr c hc0 hc1.le (i y) = ‖y‖
      by_cases hy : y = 0
      · subst hy; simp
      rw [absOfVal_of_ne _ _ _ ((map_ne_zero i).2 hy), hv, zpow_mul, zpow_natCast, hcr, hnk,
        norm_eq_zpow T k hk.int hπ y hy]) x
  have hx : ‖j x‖ = absOfVal T'.V T'.Fr c hc0 hc1.le x := e1.trans e2.symm
  rw [hx]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [map_zero, zero_le_one, true_iff]
    exact ⟨0, map_zero _⟩
  rw [absOfVal_of_ne _ _ _ hx0]
  change _ ↔ ∃ a : T'.V, algebraMap T'.V T'.Fr a = x
  rw [GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := one_lt_zpow_of_neg₀ hc0 hc1 hn
    linarith
  · intro h
    exact zpow_le_one₀ hc0 hc1.le h

end GlobalTheory.GeoTie.ReadExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRatRay

theorem isRat_const_mul {D : D7} (T : CoreJ D) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (C : Cover T ((i : ℕ) + 1) σ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) (c : ℂ)
    (h : IsRat T i hV C κ φ) (hc : c ∈ C.σ₂.fieldRange) : IsRat T i hV C κ (fun g => c * φ g) := by
  obtain ⟨φ', ⟨f₂, hf₂, rfl⟩, rfl⟩ := h
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.1 hc
  refine ⟨C.rd (wtA κ) (c' • f₂), ⟨c' • f₂, ⟨(sec _ _ _ _).smul_mem c' hf₂.1, ?_⟩, rfl⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hf₂.2
  · funext g
    simp only [castDict, Cover.rd, map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end GlobalTheory.SerRatRay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicChar
section
open NumberField Matrix GlobalTheory.CuspRep

namespace GlobalTheory.StdCharStd

theorem stdPsi_adelicChar : ∀ (E : Type) [Field E] [NumberField E],
    GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) :=
  fun E _ _ => GlobalTheory.StdCharConductor.stdPsi_psi E

end GlobalTheory.StdCharStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPow
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.PolCharRes

theorem val_below_of_degree_one (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E) (s : ℝ)
    (hν : ν.IsAbsPow s) (χ : Formalism.L2.Host.HChar (maximalRealSubfield E))
    (hχ : compNorm E χ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) ∧
      ((χ.val (w.under (𝓞 (maximalRealSubfield E))) : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(2 * s : ℂ)) := by
  have hr : compNorm E (GlobalTheory.PolChar.resReal ν) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    change ν.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
      ν.1 x * ((ν.1 (Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom x))⁻¹)⁻¹
    rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, GlobalTheory.PolChar.ideleConj_eq, inv_inv]
  set ε := χ * (GlobalTheory.PolChar.resReal ν)⁻¹ with hε
  have hεc : compNorm E ε = 1 := by rw [hε, map_mul, map_inv, hχ, hr, mul_inv_cancel]
  have hχe : χ = GlobalTheory.PolChar.resReal ν * ε := by rw [hε, mul_comm χ, mul_inv_cancel_left]
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (maximalRealSubfield E) E).eventually
    (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)] with w hu hf he
  obtain ⟨hsp, hcard, hw'⟩ := GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield E w hf he
  refine ⟨hu, ?_⟩
  have hεv : ε.val (w.under (𝓞 (maximalRealSubfield E))) = 1 := GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split E ε hεc _ hsp _
  rw [hχe, Formalism.L2.Host.HChar.val_mul, hεv, mul_one, GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above E ν _ (fun w' h => ⟨hν.1 w', (hw' w' h).2⟩),
    Units.coe_prod, Finset.prod_congr rfl (fun w' h => by rw [hν.2.1 w', (hw' w' h).1]), Finset.prod_const, hcard,
    ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem restrict_eq_cycBar_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  intro E Ω _ _ _ _ _ _ l _ ι ν s hν ψ hψ k μ hμ m hm
  obtain ⟨hμc, art, n, hart, -, hlad⟩ := hμ
  have hχ : compNorm E (ψ * quadChar E ^ k) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, hψ]
  have hcyc : Continuous (cycBar E Ω l) :=
    (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (ReciprocityTheory.Gal.continuous_cycZ E Ω l)
  rw [← div_eq_one]
  refine GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius E Ω l _ ((hμc.comp (_root_.GlobalTheory.restrictScalarsHom_maximalRealSubfield_continuous E Ω)).div' (hcyc.zpow m)) ?_
  filter_upwards [val_below_of_degree_one E ν s hν _ hχ, GlobalTheory.HeightCounting.eventually_natCast_notMem E l] with w h1 hl hf he A σ hA hσ
  obtain ⟨hu, hv⟩ := h1 hf he
  set F := maximalRealSubfield E
  have hA' : IsPlaceOver (F := F) A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hσ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (AlgEquiv.restrictScalarsHom F σ) := by
    rw [_root_.GlobalTheory.NormDegOne.normV_under_eq F E w hf]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hl (by
    have := (Ideal.mem_comap).1 h
    simpa using this)
  have e1 := hlad.frob_unr hart (Or.inl hl') hu hA' hσ'
  have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ
  rw [MonoidHom.div_apply, div_eq_one]
  apply Units.ext
  rw [MonoidHom.comp_apply, e1, hv]
  have hN : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmC : (-(2 * (s : ℂ))) = (((-m : ℤ)) : ℂ) := by
    have : (2 * (s : ℂ)) = ((m : ℝ) : ℂ) := by rw [hm]; push_cast; ring
    rw [this]; push_cast; ring
  have e3 : ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
    rw [e2]; simp
  rw [hN, hmC, Complex.cpow_intCast, map_zpow₀, map_natCast, ← zpow_neg, neg_neg]
  change _ = (((cycBar E Ω l σ) ^ m : (Qbar l)ˣ) : Qbar l)
  rw [Units.val_zpow_eq_zpow_val, e3]

end GlobalTheory.PolCharRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.HalfLatFin

theorem isHalf_of_nsmul {D : D7} {m n : ℕ} (e : AE D) {N : ℕ} (hN : 0 < N) {t t' w : Mx D m n}
    (ht : IsHalf e t) (ht' : IsHalf e t') (hw : t = t' + N • w) : IsHalf e w := by
  intro i j
  have h0 : t i j = t' i j + N • w i j := by
    have := congrFun (congrFun hw i) j
    simpa using this
  have hw' : N • w i j = t i j - t' i j := by rw [h0]; abel
  have h1 : (N : D.host.F) • (e * w i j - w i j) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, smul_sub, ← mul_smul_comm, hw', mul_sub, ht i j, ht' i j, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN.ne'))

end GlobalTheory.HalfLatFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentMemMaxCompactGLIffMemMaxCompactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_mem_maxCompactGL_iff_mem_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w (n := n) ↔ y ∈ Umax L n) := by
  first | exact @GlobalTheory.LocInteg.cLoc_mem_KGL_iff | exact GlobalTheory.LocInteg.cLoc_mem_KGL_iff | (intros; apply GlobalTheory.LocInteg.cLoc_mem_KGL_iff <;> assumption)
end

