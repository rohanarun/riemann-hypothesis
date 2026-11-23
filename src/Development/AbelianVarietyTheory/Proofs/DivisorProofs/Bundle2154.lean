module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLiftOfGeometricPoint
section
noncomputable section

namespace GlobalTheory.GeomTrait

section Algebra

open IsLocalRing

theorem dimensionLEOne_of_forall_mem {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {f : R} (hf : f ≠ 0) (h : ∀ q : Ideal R, q.IsPrime → q ≠ ⊥ → f ∈ q) : Ring.DimensionLEOne R := by
  classical
  refine ⟨fun {q} hq0 hq => ?_⟩
  by_contra hqm
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})
  have hle : q ≤ maximalIdeal R := le_maximalIdeal hq.ne_top
  have hns : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal R)), (id i : Ideal R)) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun i hi _ _ => (hfin.mem_toFinset.1 hi).1.1)]
    rintro ⟨p, hp, hmp⟩
    have hp' := hfin.mem_toFinset.1 hp
    have h1 : p ≤ q := hp'.2 ⟨hq, (Ideal.span_singleton_le_iff_mem _).2 (h q hq hq0)⟩
      (hle.trans hmp)
    exact hqm (le_antisymm hle (le_trans hmp h1) ▸ maximalIdeal.isMaximal R)
  obtain ⟨g, hgm, hg⟩ := Set.not_subset.1 hns
  have hne : Ideal.span {g} ≠ ⊤ := fun e => hgm (Ideal.span_singleton_eq_top.1 e)
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hne
  have hpp : p.IsPrime := hp.1.1
  have hgp : g ∈ p := hp.1.2 (Ideal.subset_span rfl)
  have hht : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  have hfm : Ideal.span {f} ≠ ⊤ := fun e =>
    hq.ne_top (q.eq_top_of_isUnit_mem (h q hq hq0) (Ideal.span_singleton_eq_top.1 e))
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p', hp'⟩⟩ := Ideal.nonempty_minimalPrimes hfm
    exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', p'.zero_mem⟩)
  have hp0 : p ≠ ⊥ := fun e => hg0 (by simpa [e] using hgp)
  obtain ⟨p', hp', hp'p⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 (h p hpp hp0))
  have hp'p' : p'.IsPrime := hp'.1.1
  have hp'0 : p' ≠ ⊥ := fun e => hf (by simpa [e] using hp'.1.2 (Ideal.subset_span rfl))
  have e : p' = p := by
    by_contra hne'
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hp'p hne')
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hp'0)
    have h3 : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := ((add_le_add_left h2 1).trans h1).trans hht
    have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr; exact le_add_self) h3
    exact absurd h4 (by decide)
  exact hg (Set.mem_iUnion₂.2 ⟨p', hfin.mem_toFinset.2 hp', e ▸ hgp⟩)

theorem exists_prime_dimensionLEOne {O : Type*} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O}
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) :
    ∃ (P : Ideal O) (_ : P.IsPrime), f ∉ P ∧ Ring.DimensionLEOne (O ⧸ P) := by
  obtain ⟨P, ⟨hP, hfP⟩, hmax⟩ := set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian O O)
    {P : Ideal O | P.IsPrime ∧ f ∉ P} ⟨p₀, hp₀, hf⟩
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  refine ⟨P, hP, hfP, dimensionLEOne_of_forall_mem (f := Ideal.Quotient.mk P f)
    (fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 e)) fun q hq hq0 => ?_⟩
  by_contra hn
  refine hmax (q.comap (Ideal.Quotient.mk P)) ⟨inferInstance, hn⟩ (lt_of_le_of_ne ?_ fun e => hq0 ?_)
  · intro a ha
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [eq_bot_iff]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : a ∈ P := e ▸ ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 this

theorem exists_dvr_of_dimensionLEOne {R Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.DimensionLEOne R] (hR : ¬ IsField R) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : R →+* W) (ι : ResidueField W →+* Ω),
      Function.Injective ψ ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨V, hV, h⟩ := exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hR
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hi : Function.Injective ((algebraMap R (FractionRing R)).codRestrict V h1) :=
    fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)
  letI : Algebra R V := ((algebraMap R (FractionRing R)).codRestrict V h1).toAlgebra
  have : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hloc : IsLocalHom (algebraMap R V) := h2
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (isField_iff_maximalIdeal_eq.not.mp hR)
  have hfin := finite_quotient_span_of_birational (A := R) (B := V) (fun x => by
    obtain ⟨y, c, hc, hx⟩ := IsFractionRing.div_surjective (A := R) (x : FractionRing R)
    refine ⟨c, nonZeroDivisors.ne_zero hc, y, Subtype.ext ?_⟩
    change algebraMap R (FractionRing R) c * x = algebraMap R (FractionRing R) y
    rw [← hx]
    exact mul_div_cancel₀ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc)) ha0
  have hle : Ideal.span {algebraMap R V a} ≤ maximalIdeal V :=
    (Ideal.span_singleton_le_iff_mem _).2 (map_nonunit _ a ha)
  have hf2 : Module.Finite R (ResidueField V) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap (Ideal.Quotient.factor_surjective hle)
  have hf3 : Module.Finite (ResidueField R) (ResidueField V) := Module.Finite.of_restrictScalars_finite R _ _
  letI : Algebra (ResidueField R) Ω := (ResidueField.lift φ).toAlgebra
  let ι₀ : ResidueField V →ₐ[ResidueField R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let W := AdicCompletion (maximalIdeal V) V
  let e : ResidueField V ≃+* ResidueField W :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap V W)) (AdicCompletion.residueField_map_bijective V)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, (algebraMap V W).comp (algebraMap R V),
    ι₀.toRingHom.comp e.symm.toRingHom, (algebraMap_adicCompletion_injective_of_dvr V).comp hi, ?_⟩
  ext r
  have h3 : residue W (algebraMap V W (algebraMap R V r)) = e (residue V (algebraMap R V r)) := rfl
  change ι₀ (e.symm (residue W (algebraMap V W (algebraMap R V r)))) = φ r
  rw [h3, e.symm_apply_apply]
  exact ι₀.commutes (residue R r)

theorem exists_dvr {O Ω : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {f : O} (hfm : f ∈ maximalIdeal O)
    (p₀ : Ideal O) (hp₀ : p₀.IsPrime) (hf : f ∉ p₀) [Field Ω] [IsAlgClosed Ω] (φ : O →+* Ω) [IsLocalHom φ] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (ψ : O →+* W) (ι : ResidueField W →+* Ω),
      ψ f ≠ 0 ∧ (ι.comp (residue W)).comp ψ = φ := by
  obtain ⟨P, hP, hfP, hd⟩ := exists_prime_dimensionLEOne p₀ hp₀ hf
  have hl : IsLocalRing (O ⧸ P) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hF : ¬ IsField (O ⧸ P) := fun h =>
    hfP (eq_maximalIdeal (Ideal.Quotient.maximal_of_isField P h) ▸ hfm)
  have hk : ∀ a ∈ P, φ a = 0 := fun a ha => by
    by_contra h
    exact hP.ne_top (P.eq_top_of_isUnit_mem ha (isUnit_of_map_unit φ a (IsUnit.mk0 _ h)))
  have : IsLocalHom (Ideal.Quotient.lift P φ hk) := ⟨fun a ha => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (isUnit_of_map_unit φ a ha).map _⟩
  obtain ⟨W, _, _, _, _, ψ, ι, h1, h2⟩ := exists_dvr_of_dimensionLEOne hF (Ideal.Quotient.lift P φ hk)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, ψ.comp (Ideal.Quotient.mk P), ι,
    fun e => hfP (Ideal.Quotient.eq_zero_iff_mem.1 (h1 (e.trans (map_zero ψ).symm))), ?_⟩
  rw [← RingHom.comp_assoc, h2]
  rfl

end Algebra

open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

end GlobalTheory.GeomTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceOfPrimeElementOfNormalLocalModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.PrimeElementPlace

theorem main : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (T : Subring L) (hT : IsLocModel cL T) (ψ : T →+* K) (f : T), IsIntegrallyClosed T → (∀ a, ψ ⟨cL a, hT.const_mem a⟩ = cK a) → RingHom.ker ψ = Ideal.span {f} → f ≠ 0 → IsLocModel cK ψ.range → ∃ (S : Place cL) (hS : S.IsPrimeOf T) (ψS : S.ring →+* K), Function.Surjective ψS ∧ (∀ a, ψS (S.const a) = cK a) ∧ (∀ t : T, ψS ⟨t, hS.1 t t.2⟩ = ψ t) ∧ Irreducible (⟨f, hS.1 f f.2⟩ : S.ring) := by
  intro L K _ _ cL cK n T hT ψ f _ hc hker hf hR
  classical
  haveI hfr : IsFractionRing T L := IsFractionRing.of_field T L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hT.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  haveI hP : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let A : Subalgebra T L :=
    Localization.subalgebra.ofField L (RingHom.ker ψ).primeCompl (RingHom.ker ψ).primeCompl_le_nonZeroDivisors
  haveI : IsLocalization.AtPrime A (RingHom.ker ψ) := (inferInstance : IsLocalization (RingHom.ker ψ).primeCompl A)
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (RingHom.ker ψ)
  letI : Algebra ℂ T := (cL.codRestrict T hT.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ T := hT.essFiniteType
  haveI : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing ℂ T
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (RingHom.ker ψ).primeCompl A inferInstance
  have hinjA : Function.Injective (algebraMap T A) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A => (z : L)) h)
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap T A f} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ψ) A, hker, Ideal.map_span,
      Set.image_singleton]
  have hf' : algebraMap T A f ≠ 0 := fun h => hf (hinjA (h.trans (map_zero _).symm))
  have hprinc : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨_, hmax⟩⟩
  haveI : IsPrincipalIdealRing A :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := A)).out 1 5).2 hprinc
  haveI hdvrA : IsDiscreteValuationRing A := by
    refine ⟨?_⟩
    rw [hmax]
    intro h
    exact hf' ((Ideal.span_singleton_eq_bot).1 h)
  have hval : ∀ x : L, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring := fun x => by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨y, hy⟩ | ⟨y, hy⟩
    · left; rw [← hy]; exact y.2
    · right; rw [← hy]; exact y.2
  let V : ValuationSubring L := ValuationSubring.ofSubring A.toSubring hval
  let e : A ≃+* V :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun y => ⟨y.1, y.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  have hTA : ∀ t : L, t ∈ T → t ∈ V := fun t ht => A.algebraMap_mem (⟨t, ht⟩ : T)
  have hcV : ∀ a, cL a ∈ V := fun a => hTA _ (hT.const_mem a)
  have heft : (cL.codRestrict V hcV).EssFiniteType := by
    have h2 : (algebraMap T A).EssFiniteType := RingHom.essFiniteType_algebraMap.2
      (Algebra.EssFiniteType.of_isLocalization A (RingHom.ker ψ).primeCompl)
    have h3 := (hT.essFiniteType.comp h2).comp
      (RingHom.FiniteType.of_surjective e.toRingHom e.surjective).essFiniteType
    have e' : e.toRingHom.comp ((algebraMap T A).comp (cL.codRestrict T hT.const_mem)) =
        cL.codRestrict V hcV := RingHom.ext fun a => Subtype.ext rfl
    exact e' ▸ h3
  let S : Place cL := ⟨V, hcV, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, heft⟩
  have hS : S.IsPrimeOf T := by
    refine ⟨fun t ht => hTA t ht, fun x hx => ?_⟩
    obtain ⟨a, s, hs, rfl⟩ := hx
    have hs0 : (s : L) ≠ 0 := fun h => hs (by
      rw [show s = 0 from Subtype.ext h]; exact (RingHom.ker ψ).zero_mem)
    have hinv : (s : L)⁻¹ ∈ V := ⟨1, s, hs, by rw [map_one, one_mul]; rfl⟩
    have hsV : (s : L) ∈ V := hTA _ s.2
    have hu : IsUnit (⟨(s : L), hsV⟩ : S.ring) :=
      isUnit_iff_exists_inv.2 ⟨⟨(s : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
    have hord : S.ord (s : L) = 0 := S.ord_eq_zero (u := ⟨(s : L), hsV⟩) hu
    refine ⟨a, a.2, s, s.2, hs0, hord, ?_⟩
    change (a : L) * (s : L)⁻¹ * s = a
    rw [inv_mul_cancel_right₀ hs0]
  have hunit : ∀ y : (RingHom.ker ψ).primeCompl, IsUnit (ψ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)
  let ψS : S.ring →+* K :=
    (IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (S := A) hunit).comp e.symm.toRingHom
  have hgen : ∀ (t : T) (h : (t : L) ∈ S.ring), ψS ⟨t, h⟩ = ψ t := by
    intro t h
    have h1 : e.symm ⟨t, h⟩ = algebraMap T A t := Subtype.ext rfl
    show IsLocalization.lift _ (e.symm ⟨t, h⟩) = ψ t
    rw [h1, IsLocalization.lift_eq]
  refine ⟨S, hS, ψS, fun z => ?_, fun a => ?_, fun t => hgen t _, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb0, e1⟩ := hR.frac z
    have hb : b ∈ (RingHom.ker ψ).primeCompl := fun h => hb0 (RingHom.mem_ker.1 h)
    refine ⟨e (IsLocalization.mk' A a ⟨b, hb⟩), ?_⟩
    show IsLocalization.lift _ (e.symm (e _)) = z
    rw [RingEquiv.symm_apply_apply, IsLocalization.lift_mk'_spec]
    exact e1.symm.trans (mul_comm _ _)
  · exact (hgen ⟨cL a, hT.const_mem a⟩ _).trans (hc a)
  · have h1 : (⟨f, hS.1 f f.2⟩ : S.ring) = e (algebraMap T A f) := Subtype.ext rfl
    rw [h1, MulEquiv.irreducible_iff]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax

end GlobalTheory.FieldPair.PrimeElementPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8ThetaPowerOverModuliDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc

theorem exists_sharpOver_connected {g n : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) {S : Scheme.{0}} [ConnectedSpace S] (u : S ⟶ F.X) : ∃ P : PolAV S, SharpOver F W P u := by
  obtain ⟨L₁, -⟩ := abelianSchemeLaws_all
  have hG := L₁.globalFns
  let c := GlobalTheory.LowChart.siegPull F.univ u (u ≫ F.s) rfl
  have hpb : SiegPB c F.univ u := GlobalTheory.LowChart.siegPB_siegPull F.univ u _ rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ u _ rfl F.princ
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim_of_connected c.A c.ab
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := GlobalTheory.EighthPower.exists_power c.A c.ab hd 8
  have hb := GlobalTheory.EighthPower.isSymBilin hG c hc.1
  have hL : (GlobalTheory.MatrixBundle.matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  refine ⟨{ A := G, isAb := hA, g := 8 * d, smoothDim := hdim, L := GlobalTheory.MatrixBundle.matLB c.P pr W, isLB := hL
            rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb hpr, sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb hpr
            ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG _ _ 8 _ _ _ _ c G pr W hpr hu hc.1 hW.1
            ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }, c, hpb, pr, hpr, hu, ?_⟩
  exact PolBaseChange.lbIso_refl hL

theorem exists_sharpOver_domain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (R : Type) [CommRing R] [IsDomain R] (u : Sp R ⟶ F.X), ∃ P : PolAV (Sp R), SharpOver F W P u := by
  intro g n F W hW R _ _ u
  haveI : ConnectedSpace (Sp R) := by
    change ConnectedSpace (PrimeSpectrum R)
    infer_instance
  exact exists_sharpOver_connected F W hW u

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenFrameAlongArcFlagSpaceChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

namespace GlobalTheory.CompHS.ArcBridge

theorem arc_bridge : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι), W ≤ (L₀ TF.X Z la).U i → ∀ (ψ : ℂ → (Γ(Y₀ TF.X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap σ) → (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ bd₀ TF.X Z) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) → ∃ (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (fr : EigFrame TF.Y φ (x ≫ genι TF.Y)) (y : ℂ → FrPt Xo c (CAt σ)), IsBdArc TF.Y σ φ x ψ r ∧ (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) ∧ ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (u : ℂ), u ∈ Metric.ball (0 : ℂ) r → u ≠ 0 → ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 (y u)) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)
  let φ : c.F →+* Γ(Y₀ TF.X Z, W) := φ'.hom
  have hφ : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z = spMap φ := hφ'.symm
  have hxc : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z ≫ TF.X.π) ≫ TF.Y.s = spMap φ ≫ spMap (RingHom.id c.F) := by
    have hid : spMap (RingHom.id c.F) = 𝟙 _ := by unfold spMap; rw [CommRingCat.ofHom_id, Spec.map_id]
    rw [hid, Category.comp_id, ← hφ]
    simp only [Category.assoc]
  let x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y := pullback.lift _ _ hxc
  have hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y := by
    rw [Category.assoc]; exact (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr TF.Y = spMap φ := pullback.lift_snd _ _ _
  have hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit) := fun s _ => by
    have h1 : (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) s ∈ W := hW.range_fromSpec.le ⟨s, rfl⟩
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.1 (hWi h1)
  obtain ⟨fr, hfr⟩ := _root_.GlobalTheory.CompHS.exists_eigFrame_vecAt₀ TF Z W hW φ hφ (i PUnit.unit) hz _ hx
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp φ = σ := fun u hu => by
    have h1 := hs u hu
    rw [hφ, spMap_comp'] at h1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ (u : ℂ) (s : Sp ℂ), (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ (spMap (ψ u) ≫ x) s ∉ genBd TF.Y := by
    intro u s
    haveI := GlobalTheory.LogKS.isIso_fst TF.Y
    have e : (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) s ∈ U₀ TF.X Z ↔ genι TF.Y ((spMap (ψ u) ≫ x) s) ∈ Set.range TF.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι TF.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc TF.Y σ φ x ψ r := ⟨⟨hψ, hxs, hφu⟩, fun s => by
      have := hin s
      by_contra h
      exact this ((key 0 s).2 h), fun u hu h s => (key u s).1 (hout u hu h (Set.mem_univ s))⟩
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) r ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H Dw l Xo c c.F (RingHom.id c.F) TF.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r ∧ ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    have := hψ.1
    refine ⟨?_, by exact_mod_cast (half_pos this).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos this).le]
    exact half_lt_self this
  haveI : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! yy hyy using hy'
  refine ⟨φ, x, fr, yy, hb, fun u hu h => hyy u ⟨hu, h⟩, fun g u hu h hO hi => ?_⟩
  exact _root_.GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR TF Z la σ W hW i φ x hx hz fr hfr (ψ u) (yy u) (hφu u hu) (hyy u ⟨hu, h⟩) g hO hi

end GlobalTheory.CompHS.ArcBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndoPt

theorem exists_mulEquiv_points {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (T : Over S') :
    ∃ E : (T ⟶ G') ≃* (Over.mk (T.hom ≫ g) ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ g) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ g
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun x => rfl
  have inj : Function.Injective F := fun x y e => by
    apply Over.OverMorphism.ext
    refine h.1.hom_ext ?_ ?_
    · rw [← hF, ← hF, e]
    · rw [Over.w x, Over.w y]
  have sur : Function.Surjective F := fun z => by
    have w : z.left ≫ G.hom = T.hom ≫ g := Over.w z
    refine ⟨Over.homMk (h.1.lift z.left T.hom w) (h.1.lift_snd _ _ w), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ w
  refine ⟨{ Equiv.ofBijective F ⟨inj, sur⟩ with map_mul' := fun x y => ?_ }, hF⟩
  apply Over.OverMorphism.ext
  exact (h.2 T x y (F x) (F y) rfl rfl).symm

theorem exists_point_of_isMonHom {S S' : Scheme.{0}} {g : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G g φ) (f : G ⟶ G) [IsMonHom f] (m : ℕ) {T : Over S'}
    (x : T ⟶ G') (hx : x ^ m = 1) :
    ∃ x₂ : T ⟶ G', x₂.left ≫ φ = x.left ≫ φ ≫ f.left ∧ x₂ ^ m = 1 := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points h T
  refine ⟨E.symm (E x ≫ f), ?_, ?_⟩
  · rw [← hE, MulEquiv.apply_symm_apply, Over.comp_left, hE, Category.assoc]
  · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hx, map_one, MonObj.one_comp, map_one]

theorem exists_endo_point : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u f hf m x hx
  exact exists_point_of_isMonHom u.cart f m x hx

end GlobalTheory.EndoPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingOnOfMemModelLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

noncomputable section
namespace GlobalTheory.Poinc

theorem exists_eq_div_of_mem_O_affine : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z ∈ U, ∀ x ∈ M.O z, ∃ a ∈ M.ringOn (U : Set M.Z), ∃ b ∈ M.ringOn (U : Set M.Z), b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x = a / b := by
  intro o Ω _ _ _ M U hU z hz x hx
  obtain ⟨W, f, hzW, rfl⟩ := hx
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgW, hzg⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hzg⟩
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgW f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, U), M.res _ hg (algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen g) t) = M.res U hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_resG, res_apply, ← map_pow, res_apply, res_apply] at h1
  have hu := (isUnit_O_iff _).1 ((isUnit_valF_iff hz g).2 hzg)
  have hb : valF M.pt U (g ^ n) = valF M.pt U g ^ n := by
    rw [← M.res_apply U hne, map_pow, res_apply]
  have h0 : valF M.pt U (g ^ n) ≠ 0 := by
    rw [hb]
    exact pow_ne_zero _ hu.1
  refine ⟨_, (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, (mem_ringOn_iff_exists hne).2 ⟨g ^ n, rfl⟩, h0, ?_,
    (eq_div_iff h0).2 h1⟩
  rw [hb, ← inv_pow]
  exact pow_mem hu.2 n

end GlobalTheory.Poinc
end
end

