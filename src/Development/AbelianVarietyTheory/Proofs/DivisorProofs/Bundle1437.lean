module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0101
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldInertiaFixedIsAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaRes

def toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) : R →+* V :=
  ((algebraMap K Ω).comp (algebraMap R K)).codRestrict V (fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this)

theorem coe_toV (R K Ω : Type) [CommRing R] [Field K] [Algebra R K] [Field Ω] [Algebra K Ω]
    (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) (r : R) :
    ((toV R K Ω V hV r : V) : Ω) = algebraMap K Ω (algebraMap R K r) := rfl

theorem isLocalHom_toV (R K Ω : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    IsLocalHom (toV R K Ω V hV) := by
  constructor
  intro r hr
  obtain ⟨u, hu⟩ := hr
  have hx : algebraMap K Ω (algebraMap R K r) * ((u⁻¹ : Vˣ) : V) = 1 := by
    rw [← coe_toV R K Ω V hV r, ← hu]
    exact congrArg Subtype.val u.mul_inv
  have hx0 : algebraMap R K r ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_mul] at hx; exact zero_ne_one hx
  have hmem : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
    change algebraMap K Ω _ ∈ V
    rw [map_inv₀, inv_eq_of_mul_eq_one_right hx]
    exact ((u⁻¹ : Vˣ) : V).2
  rw [hV] at hmem
  obtain ⟨s, hs⟩ := hmem
  have h1 : r * s = 1 := IsFractionRing.injective R K (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
  exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

def resMap (R K Ω : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) :
    ResidueField R →+* ResidueField V :=
  haveI := isLocalHom_toV R K Ω V hV
  ResidueField.map (toV R K Ω V hV)

open Polynomial

theorem residue_algebraic (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (V : ValuationSubring Ω)
    (hV : IsAbove R K V.toSubring) (a : ResidueField V) :
    ∃ p : Polynomial (ResidueField R), p ≠ 0 ∧ p.eval₂ (resMap R K Ω V hV) a = 0 := by
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨w, rfl⟩ := residue_surjective a
  obtain ⟨p, hp0, hpw⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) ((w : V) : Ω)
  obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
  let b : nonZeroDivisors R := ⟨b, hbmem⟩
  set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
  have hφinj : Function.Injective (toV R K Ω V hV) := fun x y h =>
    IsFractionRing.injective R K ((algebraMap K Ω).injective (by
      have := congrArg Subtype.val h
      rwa [coe_toV, coe_toV] at this))
  have hq0 : q ≠ 0 :=
    (IsLocalization.integerNormalization_eq_zero_iff le_rfl p).not.mpr hp0
  have hcomp : V.subtype.comp (toV R K Ω V hV) = (algebraMap K Ω).comp (algebraMap R K) :=
    RingHom.ext fun r => coe_toV R K Ω V hV r
  have hqw : Polynomial.eval₂ (toV R K Ω V hV) w q = 0 := by
    apply Subtype.ext
    change V.subtype _ = V.subtype 0
    rw [map_zero, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hb, Algebra.smul_def,
      Polynomial.eval₂_mul]
    have : Polynomial.eval₂ (algebraMap K Ω) (V.subtype w) p = 0 := hpw
    rw [this, mul_zero]
  set pp := q.primPart
  have hpp : Polynomial.eval₂ (toV R K Ω V hV) w pp = 0 := by
    have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
    have := hqw
    rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
    exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
  refine ⟨pp.map (residue R), ?_, ?_⟩
  · intro h0
    have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
      simpa [RingHom.mem_ker] using h0
    rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, Ideal.mem_span_singleton] at hmem
    exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
  · rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((ResidueField.map (toV R K Ω V hV)).comp (residue R)) _ _ = 0
    rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]

theorem eq_of_residue_eq {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (q : A[X])
    (hs : (q.map (residue A)).Separable) (b c : A) (hb : q.IsRoot b) (hc : q.IsRoot c)
    (h : residue A b = residue A c) : b = c := by
  by_contra hne
  obtain ⟨q1, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hb
  have hc1 : q1.IsRoot c := by
    have := hc
    rw [IsRoot, eval_mul, eval_sub, eval_X, eval_C] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨q2, rfl⟩ := Polynomial.dvd_iff_isRoot.2 hc1
  rw [← _root_.mul_assoc, Polynomial.map_mul, Polynomial.map_mul] at hs
  have h2 := hs.of_mul_left
  simp only [Polynomial.map_sub, map_X, map_C, h] at h2
  exact not_isUnit_X_sub_C _ (isCoprime_self.1 h2.isCoprime)

theorem residueField_inertiaFixed_isAlgClosed : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → IsAlgClosed (IsLocalRing.ResidueField (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω))) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  haveI : IsLocalHom (toV R K Ω V hV) := isLocalHom_toV R K Ω V hV
  letI : Algebra (ResidueField R) (ResidueField V) := (resMap R K Ω V hV).toAlgebra
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField V) := ⟨fun a => by
    obtain ⟨p, hp, h⟩ := residue_algebraic R K Ω V hV a
    exact ⟨p, hp, h⟩⟩
  haveI : PerfectField (ResidueField V) := Algebra.IsAlgebraic.perfectField (ResidueField R)

  have hred : ∀ s : Multiset V, ((s.map fun b => X - C b).prod).map (residue V) =
      ((s.map (residue V)).map fun a => X - C a).prod := by
    intro s
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp

  haveI : IsSepClosed (ResidueField V) := IsSepClosed.of_exists_root _ fun p hm hirr hsep => by
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts p).2 (Polynomial.map_surjective _ residue_surjective p)) hm
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V q hqm (by rw [hq]; exact hsep)
    rw [← hq, hs, hred] at hirr ⊢
    obtain ⟨b, hb⟩ : ∃ b, b ∈ s := by
      by_contra h0
      push_neg at h0
      rw [Multiset.eq_zero_of_forall_notMem h0] at hirr
      simp at hirr
    refine ⟨residue V b, ?_⟩
    have hr := Polynomial.roots_multiset_prod_X_sub_C (s.map (residue V))
    have hmem : residue V b ∈ ((s.map (residue V)).map fun a => X - C a).prod.roots := by
      rw [hr]; exact Multiset.mem_map_of_mem _ hb
    exact (Polynomial.mem_roots'.1 hmem).2
  haveI : IsAlgClosed (ResidueField V) := inferInstance

  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  let jV : V' →+* V := ((algebraMap K' Ω).comp V'.subtype).codRestrict V (fun x => x.2)
  haveI : IsLocalHom jV := by
    constructor
    intro x hx
    obtain ⟨u, hu⟩ := hx
    have hx1 : ((x : K') : Ω) * ((u⁻¹ : Vˣ) : V) = 1 := by
      have : ((jV x : V) : Ω) = ((x : K') : Ω) := rfl
      rw [← this, ← hu]
      exact congrArg Subtype.val u.mul_inv
    have hx0 : (x : K') ≠ 0 := by
      intro h0; rw [h0] at hx1; simp at hx1
    have hmem : (x : K')⁻¹ ∈ V' := by
      change ((((x : K')⁻¹ : K')) : Ω) ∈ V
      rw [IntermediateField.coe_inv, inv_eq_of_mul_eq_one_right hx1]
      exact ((u⁻¹ : Vˣ) : V).2
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    exact mul_inv_cancel₀ hx0
  haveI : Algebra.IsSeparable (ResidueField R) (ResidueField V) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hsurj : Function.Surjective (ResidueField.map jV) := by
    intro a
    have hsep : (minpoly (ResidueField R) a).Separable := Algebra.IsSeparable.isSeparable _ a
    have hmon : (minpoly (ResidueField R) a).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ residue_surjective _)) hmon
    set gV := g.map (toV R K Ω V hV) with hgV
    have hgV' : gV.map (residue V) = (minpoly (ResidueField R) a).map (resMap R K Ω V hV) := by
      rw [hgV, Polynomial.map_map, ← ResidueField.map_comp_residue, ← Polynomial.map_map, hg]
      rfl
    have hsepV : (gV.map (residue V)).Separable := by rw [hgV']; exact hsep.map
    obtain ⟨s, hs⟩ := GlobalTheory.T.monic_splits_valuationSubring_of_separable_reduction Ω V gV (hgm.map _) hsepV
    have hroot : a ∈ (gV.map (residue V)).roots := by
      rw [Polynomial.mem_roots ((hgm.map _).map _).ne_zero, hgV', IsRoot, Polynomial.eval_map]
      exact minpoly.aeval _ a
    rw [hs, hred, Polynomial.roots_multiset_prod_X_sub_C] at hroot
    obtain ⟨b, hbs, rfl⟩ := Multiset.mem_map.1 hroot
    have hbroot : gV.IsRoot b := by
      have : b ∈ gV.roots := by rw [hs, Polynomial.roots_multiset_prod_X_sub_C]; exact hbs
      exact (Polynomial.mem_roots'.1 this).2
    have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
      intro σ hσ
      obtain ⟨-, h2⟩ := (mem_inertia_iff V σ).1 hσ
      have hlt := h2 b b.2
      have hd : σ (b : Ω) - b ∈ V := (V.valuation_le_one_iff _).1 hlt.le
      have hmem : σ (b : Ω) ∈ V := by simpa using add_mem hd b.2
      set c : V := ⟨σ b, hmem⟩ with hc
      have hres : residue V c = residue V b := by
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
        exact hlt
      have hcroot : gV.IsRoot c := by
        have key : ∀ y : V, ((gV.eval y : V) : Ω) = g.eval₂ ((algebraMap K Ω).comp (algebraMap R K)) (y : Ω) := by
          intro y
          rw [hgV, Polynomial.eval_map]
          change V.subtype _ = _
          rw [Polynomial.hom_eval₂]
          rfl
        have hb0 := key b
        rw [hbroot.eq_zero] at hb0
        have hcomm : (σ : Ω →+* Ω).comp ((algebraMap K Ω).comp (algebraMap R K)) =
            (algebraMap K Ω).comp (algebraMap R K) := by
          ext r; simp
        apply Subtype.ext
        rw [key c, show ((c : V) : Ω) = (σ : Ω →+* Ω) b from rfl, ← hcomm, ← Polynomial.hom_eval₂, ← hb0]
        simp
      have := eq_of_residue_eq gV hsepV c b hcroot hbroot hres
      exact congrArg Subtype.val this
    have hbK : (b : Ω) ∈ K' := by
      rw [hK', IntermediateField.mem_fixedField_iff]
      exact hfix
    have hbV' : (⟨b, hbK⟩ : K') ∈ V' := b.2
    refine ⟨residue V' ⟨⟨b, hbK⟩, hbV'⟩, ?_⟩
    rw [ResidueField.map_residue]
    rfl
  let e := RingEquiv.ofBijective (ResidueField.map jV) ⟨(ResidueField.map jV).injective, hsurj⟩
  exact IsAlgClosed.of_ringEquiv _ _ e.symm

end GlobalTheory.InertiaRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResiduePerfectAndChar
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRedRes

theorem residue_perfect_and_char :
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [PerfectField (ResidueField R)] (L W : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra W L] [IsFractionRing W L], IsAbove R K (algebraMap W L).range → PerfectField (ResidueField W) ∧ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → (m : ResidueField W) ≠ 0 := by
  intro R K _ _ _ _ _ _ _ L W _ _ _ _ _ _ _ _ h
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  set V : Subring L := (algebraMap W L).range with hV
  have memV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ (algebraMap R K).range := by
    intro x
    rw [← Subring.mem_comap, show V.comap (algebraMap K L) = (algebraMap R K).range from h]
  let e : W ≃+* V := RingEquiv.ofBijective (algebraMap W L).rangeRestrict
    ⟨fun a b hab => hWL (by simpa using congrArg Subtype.val hab), (algebraMap W L).rangeRestrict_surjective⟩
  have he : ∀ v : V, algebraMap W L (e.symm v) = v := by
    intro v
    have := congrArg Subtype.val (e.apply_symm_apply v)
    exact this
  let ψ : R →+* V := ((algebraMap K L).comp (algebraMap R K)).codRestrict V
    (fun r => (memV _).2 ⟨r, rfl⟩)
  let φ : R →+* W := e.symm.toRingHom.comp ψ
  have hφ : ∀ r, algebraMap W L (φ r) = algebraMap K L (algebraMap R K r) := by
    intro r; exact he (ψ r)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := congrArg (algebraMap W L) hab
    rw [hφ, hφ] at this
    exact hRK ((algebraMap K L).injective this)
  haveI : IsLocalHom φ := by
    constructor
    intro r hr
    obtain ⟨u, hu⟩ := hr
    have hx : algebraMap W L (φ r) * algebraMap W L (u⁻¹ : Wˣ) = 1 := by
      rw [← map_mul, ← hu]; simp
    rw [hφ] at hx
    have hx0 : algebraMap R K r ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx
    have hinv : algebraMap K L (algebraMap R K r)⁻¹ = algebraMap W L (u⁻¹ : Wˣ) := by
      rw [map_inv₀]; exact (eq_inv_of_mul_eq_one_right hx).symm
    obtain ⟨s, hs⟩ := (memV _).1 (by rw [hinv]; exact RingHom.mem_range_self _ _)
    have h1 : r * s = 1 := hRK (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hx0])
    exact ⟨⟨r, s, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  let f := ResidueField.map φ
  have hf : Function.Injective f := f.injective
  refine ⟨?_, fun m hm hW => hm (hf (by rw [map_natCast, map_zero]; exact hW))⟩
  letI : Algebra (ResidueField R) (ResidueField W) := f.toAlgebra
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := R)
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid R
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField W) := by
    constructor
    intro y
    obtain ⟨w, rfl⟩ := residue_surjective y
    have hint : IsIntegral K (algebraMap W L w) := Algebra.IsIntegral.isIntegral _
    set p := minpoly K (algebraMap W L w)
    obtain ⟨b, hbmem, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
    set q := IsLocalization.integerNormalization (nonZeroDivisors R) p
    have hp0 : p ≠ 0 := minpoly.ne_zero hint
    have hq0 : q ≠ 0 := by
      intro hq; rw [hq, Polynomial.map_zero] at hb
      have hb0 : (algebraMap R K b) ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem
      rw [Algebra.smul_def, Polynomial.algebraMap_apply] at hb
      exact hp0 ((mul_eq_zero.1 hb.symm).resolve_left (by simpa using hb0))
    have hqw : Polynomial.eval₂ φ w q = 0 := by
      apply hWL
      rw [map_zero, Polynomial.hom_eval₂]
      have : (algebraMap W L).comp φ = (algebraMap K L).comp (algebraMap R K) := RingHom.ext hφ
      rw [this, ← Polynomial.eval₂_map, hb]
      rw [Algebra.smul_def, Polynomial.eval₂_mul]
      have : Polynomial.eval₂ (algebraMap K L) (algebraMap W L w) p = 0 := minpoly.aeval K _
      rw [this, mul_zero]
    set pp := q.primPart
    have hpp : Polynomial.eval₂ φ w pp = 0 := by
      have hc : q.content ≠ 0 := (Polynomial.content_eq_zero_iff).not.2 hq0
      have := hqw
      rw [Polynomial.eq_C_content_mul_primPart q, Polynomial.eval₂_mul, Polynomial.eval₂_C] at this
      exact (mul_eq_zero.1 this).resolve_left (fun h0 => hc (hφinj (by rw [h0, map_zero])))
    refine ⟨pp.map (residue R), ?_, ?_⟩
    · intro h0
      have hmem : pp ∈ RingHom.ker (Polynomial.mapRingHom (residue R)) := by
        simpa [RingHom.mem_ker] using h0
      rw [Polynomial.ker_mapRingHom, ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
        Set.image_singleton, Ideal.mem_span_singleton] at hmem
      exact hϖ.not_isUnit (Polynomial.isPrimitive_primPart q ϖ hmem)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      change Polynomial.eval₂ (f.comp (residue R)) _ _ = 0
      rw [ResidueField.map_comp_residue, ← Polynomial.hom_eval₂, hpp, map_zero]
  exact Algebra.IsAlgebraic.perfectField (ResidueField R)

end GlobalTheory.AbVarRedRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedBlockSelfApply
section
noncomputable section

namespace GlobalTheory.LevelSpanCompare

section Move

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem reflects_half_of_move {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : IsLevMove ρ ν gM gA) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (b : KA l →+* k)
    (hx : x ≫ Xo.s = spMap b) (a : Dw.La) (ha : gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨hs, hM, -⟩ := h
  obtain ⟨-, J, -, -, hJM⟩ := Xo.univ.geom k (x ≫ ρ) b (by rw [Category.assoc, hs]; exact hx)
  have h1 : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime]; simp
  rw [Submodule.sup_smul] at h1
  obtain ⟨b, hb, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
  have hgb : gM b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := gM) hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hga : gM a' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.sub_mem _ ha hgb
    simpa using this
  have e1 : ρ ≫ (Xo.univ.eta a').left = ρ ≫ (Xo.univ.eta 0).left := by
    rw [← hM a', ← hM 0, Xo.univ.eta_ker _ hga, Xo.univ.eta_ker (gM 0) (by simp)]
  have e5 : J.ev l.M a' = J.ev l.M 0 := by
    rw [← hJM _ ha', ← hJM _ (Submodule.zero_mem _)]
    ext
    simpa using congrArg (x ≫ ·) e1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have e6 : J.ev l.M 0 = 1 := (J.ker l.M hM0 0).2 ⟨0, by simp⟩
  obtain ⟨b', hb'⟩ := (J.ker l.M hM0 a').1 (e5.trans e6)
  refine Submodule.add_mem _ hb ?_
  rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (GlobalTheory.LevelGroupTest.natCast_mem_half l) trivial

theorem levR_unique (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (gM : Dw.La →ₗ[𝓞 E] Dw.La)
    {S : Type} [CommRing S] [Algebra c.F S] [Nontrivial S] {y y' y'' : FrPt Xo c S}
    (h' : levR (gM, LinearMap.id) y y') (h'' : levR (gM, LinearMap.id) y y'') : y' = y'' := by
  obtain ⟨ρ, ν, i, h, hm⟩ := h'
  obtain ⟨ρ', ν', i', g, gm⟩ := h''
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let φ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  have hinj := reflects_half_of_move h (AlgebraicClosure (S ⧸ m)) (spMap φ ≫ y.x)
    (φ.comp ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)) (by
      rw [Category.assoc, y.x_over]
      unfold sOf spMap
      rw [← Spec.map_comp]; rfl)
  obtain ⟨rfl, e⟩ := GlobalTheory.T.levelMove_moduli_unique_universalTriple E H Dw l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h g
    (GlobalTheory.exists_sim_of_aut_mod E H Dw l l.A gM hpq l.A_pos hA hinj)
  exact (_root_.GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν' e.symm hm gm

end Move

section Idem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GoodLatCompare

end Idem

section Framed

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Framed

section Swap

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Swap

section Half

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Lev Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

end Half

end GlobalTheory.LevelSpanCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalDependsOnValueAtZero
section
namespace GlobalTheory.CharInvAtZero

theorem eq_of_eq_zero : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (ℓ : SchwartzMap Y ℂ →L[ℂ] ℂ),
    (∀ L : Y →ₗ[ℝ] ℝ, ∀ f g : SchwartzMap Y ℂ, ⇑g = (fun x => GlobalTheory.ArchSch.ech (L x) * f x) → ℓ g = ℓ f) →
    ∀ f g : SchwartzMap Y ℂ, f 0 = g 0 → ℓ f = ℓ g := by
  intro Y _ _ _ ℓ hinv f g h0
  refine GlobalTheory.SchwartzHadamard.eq_of_eqOn (⊥ : Submodule ℝ Y) ℓ (fun L _ => hinv L) f g ?_
  intro p hp
  rw [Submodule.mem_bot] at hp
  subst hp
  exact h0

end GlobalTheory.CharInvAtZero
end

