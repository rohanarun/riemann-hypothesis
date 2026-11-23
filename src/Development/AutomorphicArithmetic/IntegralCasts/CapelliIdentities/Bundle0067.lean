module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0057

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFixedPiIff
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GLw :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → UpperTheory.Reformulated.B.Gr29.Plc L → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) (w : UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gr29.GV :
    {L : Type} → [inst : Field L] → [NumberField L] → ℕ → {V : Type} → (V → UpperTheory.Reformulated.B.Gr29.Plc L) → Type :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {V : Type} (S : V → UpperTheory.Reformulated.B.Gr29.Plc L) ↦
      (v : V) → UpperTheory.Reformulated.B.Gr29.GLw n (S v)

noncomputable def UpperTheory.Reformulated.B.Gr29.atJ :
    {L : Type} →
      [inst : Field L] →
        [inst_1 : NumberField L] →
          (n : ℕ) →
            {q : ℕ} →
              (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) → (j : Fin q) → UpperTheory.Reformulated.B.Gr29.GLw n (w j) →* UpperTheory.Reformulated.B.Gr29.GV n w :=
    fun {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L) (j : Fin q) ↦
      MonoidHom.mulSingle (fun (j : Fin q) ↦ UpperTheory.Reformulated.B.Gr29.GLw n (w j)) j

private def UpperTheory.Reformulated.B.Gr29.stab {A P M : Type} [CommRing A] [Group P] [AddCommGroup M]
    [_root_.Module A M] (ρ : Representation A P M) (m : M) : Subgroup P where
  carrier := {g | ρ g m = m}
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a m = m := ha
    have hb' : ρ b m = m := hb
    change ρ (a * b) m = m
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change ρ 1 m = m
    rw [map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha
    have ha' : ρ a m = m := ha
    change ρ a⁻¹ m = m
    have h : ρ a⁻¹ (ρ a m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha'] at h

private theorem UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff {q : ℕ} {G : Fin q → Type} [∀ j, Group (G j)]
    {A M : Type} [CommRing A] [AddCommGroup M] [_root_.Module A M]
    (ρ : Representation A ((j : Fin q) → G j) M) (H : (j : Fin q) → Subgroup (G j)) (m : M) :
    m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      ∀ j : Fin q, m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (MonoidHom.mulSingle G j)) (H j) := by
  have key : m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
      Subgroup.pi Set.univ H ≤ UpperTheory.Reformulated.B.Gr29.stab ρ m := Iff.rfl
  rw [key, Subgroup.pi_le_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h k hk
    exact h (Subgroup.mem_map_of_mem _ hk)
  · rintro h _ ⟨k, hk, rfl⟩
    exact h k hk

theorem UpperTheory.Reformulated.B.Gr29.mem_pi :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {n q : ℕ} {w : Fin q → UpperTheory.Reformulated.B.Gr29.Plc L} {A M : Type}
      [inst_2 : CommRing A] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module A M]
      (ρ : Representation A (UpperTheory.Reformulated.B.Gr29.GV n w) M) (H : (j : Fin q) → Subgroup (UpperTheory.Reformulated.B.Gr29.GLw n (w j)))
      (m : M),
      m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ (Subgroup.pi Set.univ H) ↔
        ∀ (j : Fin q), m ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (MonoidHom.comp ρ (UpperTheory.Reformulated.B.Gr29.atJ n w j)) (H j) := by
  intro L _ _ n q w A M _ _ _ ρ H m
  exact UpperTheory.Reformulated.B.Gr29.mem_fixed_pi_iff (G := fun j : Fin q => UpperTheory.Reformulated.B.Gr29.GLw n (w j)) ρ H m
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NonemptyNormalModelOfPresentation
section
open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R S : Type) [CommRing R] [Nontrivial R] [Algebra ℂ R]
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hπ : Function.Surjective π) (hJ : RingHom.ker π = J)
    (hinj : Function.Injective (algebraMap R S))
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ algebraMap R S b * s = algebraMap R S a) :
    Nonempty (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := S)
  let φ : MvPolynomial (Fin n ⊕ Fin m) ℂ →+* S :=
    eval₂Hom ((algebraMap R S).comp (algebraMap ℂ R))
      (Sum.elim (fun i => algebraMap R S (π (X i))) s)
  have hcomp : φ.comp (rename Sum.inl :
      MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      = (algebraMap R S).comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have h : π (C r) = algebraMap ℂ R r := π.commutes r
      simp [φ, h]
    · intro i
      simp [φ]
  have hren : ∀ q, φ (rename Sum.inl q) = algebraMap R S (π q) := fun q =>
    RingHom.congr_fun hcomp q
  have hY : ∀ i, φ (X (Sum.inr i)) = s i := fun i => by simp [φ]
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hy
    choose p hp using fun i => hπ (c i)
    refine ⟨∑ i, rename Sum.inl (p i) * X (Sum.inr i), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hren, hY, hp, Algebra.smul_def]
  refine ⟨⟨m, RingHom.ker φ, RingHom.ker_isPrime _,
    IsIntegrallyClosed.of_equiv (RingHom.quotientKerEquivOfSurjective hsurj).symm, ?_, ?_, ?_⟩⟩
  · ext q
    rw [Ideal.mem_comap, RingHom.mem_ker, hren, ← hJ, RingHom.mem_ker,
      map_eq_zero_iff _ hinj]
  · intro i
    obtain ⟨Q, hQ, hQ0⟩ : IsIntegral R (s i) := Algebra.IsIntegral.isIntegral _
    obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
      (f := π.toRingHom) (Polynomial.mem_lifts_of_surjective hπ Q) hQ
    refine ⟨P, hPm, ?_⟩
    rw [RingHom.mem_ker, Polynomial.hom_eval₂, hcomp, hY, ← Polynomial.eval₂_map, hP, hQ0]
  · intro i
    obtain ⟨a, b, hb, hab⟩ := hfrac (s i)
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    refine ⟨a, b, ?_, ?_⟩
    · rw [← hJ, RingHom.mem_ker]
      exact hb
    · rw [RingHom.mem_ker, map_sub, map_mul, hren, hren, hY, hab, sub_self]

theorem UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation :
    ∀ {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type) [inst : CommRing R] [IsDomain R] [inst_2 : Algebra ℂ R]
    (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R),
    Function.Surjective (⇑π : MvPolynomial (Fin n) ℂ → R) →
      RingHom.ker π = J →
        Nonempty
          (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.NormalModel
            J) := by
  intro n J R _ _ _ π hπ hJ
  haveI : Algebra.FiniteType ℂ R := Algebra.FiniteType.of_surjective π hπ
  haveI : Module.Finite R (integralClosure R (FractionRing R)) := UpperTheory.integralClosure_finite ℂ R (FractionRing R)
  haveI : IsIntegrallyClosed (integralClosure R (FractionRing R)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  refine UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_extension J R
    (integralClosure R (FractionRing R)) π hπ hJ ?_ ?_
  · intro x y hxy
    exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hxy)
  · intro s
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (s : FractionRing R)
    refine ⟨a, b, nonZeroDivisors.coe_ne_zero b, Subtype.ext ?_⟩
    rw [mul_comm] at hab
    exact hab
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProofSimp
section
theorem UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof.{u} :
    GroundTheory.Heights₂.Heights.GenericNoetherNormalisation.Statement.{u} := by
  intro A _ _ n q _ hq _
  classical
  obtain ⟨f, hfq, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq
  obtain ⟨e, a, ha, hlc⟩ := UpperTheory.exists_monic_change_of_variables A n f hf
  have hg : e f ≠ 0 := fun h ↦ hf (e.injective (by simpa using h))
  let π : Polynomial (MvPolynomial (Fin n) A) →ₐ[A] MvPolynomial (Fin (n + 1)) A ⧸ q :=
    (Ideal.Quotient.mkₐ A q).comp e.symm.toAlgHom
  have hπf : π (e f) = 0 := by
    simpa [π, Ideal.Quotient.eq_zero_iff_mem] using hfq
  have hsurj : Function.Surjective π :=
    (Ideal.Quotient.mkₐ_surjective A q).comp e.symm.surjective
  let z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q :=
    fun i ↦ π (Polynomial.C (MvPolynomial.X i))
  have hz : ∀ c : MvPolynomial (Fin n) A, MvPolynomial.aeval z c = π (Polynomial.C c) := by
    intro c
    have : MvPolynomial.aeval z = π.comp (Polynomial.CAlgHom) := by
      ext i
      simp [z]
    rw [this]
    rfl
  let N := (e f).natDegree
  refine ⟨a, ha, z, (Finset.range N).image (fun j ↦ π Polynomial.X ^ j), fun d ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hsurj d
  obtain ⟨k, s, r, hk, hr⟩ := UpperTheory.pseudo_division (MvPolynomial (Fin n) A) (e f) p hg
  have h1 : a ^ k • π p = π r := by
    have := congrArg π hk
    rw [map_add (f := _), map_mul π (e f), hπf, zero_mul, zero_add, hlc, map_mul, ← hz, ← map_pow,
      MvPolynomial.aeval_C, ← Algebra.smul_def] at this
    exact this
  have h2 : r = ∑ j ∈ Finset.range N, Polynomial.C (r.coeff j) * Polynomial.X ^ j := by
    rw [Polynomial.degree_eq_natDegree hg] at hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        Polynomial.as_sum_range' r N ((Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hr)
  refine ⟨k, fun t ↦ ∑ j ∈ Finset.range N with π Polynomial.X ^ j = t, r.coeff j, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, h2, map_sum, ← Finset.sum_fiberwise_of_maps_to (g := fun j ↦ π Polynomial.X ^ j)
    (fun j hj ↦ Finset.mem_image_of_mem _ hj), ← h2]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [map_mul, map_pow, hz, (Finset.mem_filter.mp hj).2]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RangeExtension
section
open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.ext_aux {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {A B : CommRingCat.{0}} (i : A ⟶ B) (hi : Function.Injective i.hom)
    (a b : Spec A ⟶ X) (ha : ∀ z, a z ∈ U) (hb : ∀ z, b z ∈ U)
    (h : Spec.map i ≫ a = Spec.map i ≫ b) : a = b := by
  have : IsAffine U.toScheme := hU
  have hr : ∀ c : Spec A ⟶ X, (∀ z, c z ∈ U) → Set.range c ⊆ Set.range U.ι := by
    intro c hc
    rintro _ ⟨z, rfl⟩
    simpa using hc z
  let a' := IsOpenImmersion.lift U.ι a (hr a ha)
  let b' := IsOpenImmersion.lift U.ι b (hr b hb)
  have ha' : a' ≫ U.ι = a := IsOpenImmersion.lift_fac _ _ _
  have hb' : b' ≫ U.ι = b := IsOpenImmersion.lift_fac _ _ _
  have h' : Spec.map i ≫ a' = Spec.map i ≫ b' := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, ha', hb', h]
  let s := Spec.preimage (a' ≫ U.toScheme.isoSpec.hom)
  let t := Spec.preimage (b' ≫ U.toScheme.isoSpec.hom)
  have hs : Spec.map s = a' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have ht : Spec.map t = b' ≫ U.toScheme.isoSpec.hom := Spec.map_preimage _
  have h2 : s ≫ i = t ≫ i := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hs, ht, ← Category.assoc, ← Category.assoc, h']
  have hm : Mono i := ConcreteCategory.mono_of_injective i hi
  have h3 : s = t := (cancel_mono i).1 h2
  have h4 : a' = b' := by
    rw [← cancel_mono U.toScheme.isoSpec.hom, ← hs, ← ht, h3]
  rw [← ha', ← hb', h4]

open AlgebraicGeometry CategoryTheory in
private lemma UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card {X : Scheme.{0}} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type} [CommRing R] (φ : R →+* Ω)
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (hxU : ∀ z, x z ∈ U) (p : X) (hp : ξ (IsLocalRing.closedPoint Ω) ⤳ p) (hpU : p ∈ U)
    (hinj : Function.Injective
      (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom)
    (hreg : ∀ a, φ a ∈ (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ).hom.range) :
    p ∈ Set.range x := by
  have hi1 : Spec.map (X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ) ≫
      X.fromSpecStalk p = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  generalize X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo ξ = i at hinj hreg hi1
  let e : X.presheaf.stalk p ≃+* i.hom.range :=
    RingEquiv.ofBijective i.hom.rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ X.presheaf.stalk p, g ≫ i = CommRingCat.ofHom φ := by
    refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict i.hom.range hreg)), ?_⟩
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict i.hom.range hreg a))
  have hi2 : Spec.map i ≫ Spec.map g ≫ x = ξ := by
    rw [← Spec.map_comp_assoc, hg]
    exact hx
  have key : Spec.map g ≫ x = X.fromSpecStalk p := by
    refine UpperTheory.Reformulated.B.RangeExtension.ext_aux hU i hinj _ _ ?_ ?_ (hi2.trans hi1.symm)
    · intro z
      simpa using hxU _
    · intro z
      have hz : X.fromSpecStalk p z ∈ Set.range (X.fromSpecStalk p) := ⟨z, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hz
      exact Specializes.mem_open hz U.2 hpU
  have hmem : p ∈ Set.range (X.fromSpecStalk p) := ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← key] at hmem
  obtain ⟨z, hz⟩ := hmem
  exact ⟨Spec.map g z, by rw [← Scheme.Hom.comp_apply]; exact hz⟩

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar in
theorem UpperTheory.Reformulated.B.RangeExtension.mem_range
    {X : Scheme} {Ω : Type} [inst : Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} :
    IsCptGen ξ → ∀ {U : X.Opens}, IsAffineOpen U →
      ∀ {R : Type} [inst_1 : CommRing R] (φ : R →+* Ω) (x : Spec (@CommRingCat.of R inst_1) ⟶ X),
        Spec.map (CommRingCat.ofHom φ) ≫ x = ξ →
        (∀ z, x z ∈ U) → ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ a : R, φ a ∈ regAt ξ q) → q.1 ∈ Set.range x := by
  intro hξ U hU R _ φ x hx hxU q hqU hreg
  exact UpperTheory.Reformulated.B.RangeExtension.finiteRing_sq_sub_mul_sq_eq_of_card
    hU φ x hx hxU q.1 q.2 hqU (hξ.inj q) hreg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SimultaneousEigenvectors
section
theorem UpperTheory.Reformulated.B.SimultaneousEigenvectorInvariantSubspace.simEig :
    ∀ {K M : Type} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup M]
    [inst_3 : _root_.Module K M] [FiniteDimensional K M] {J : Type} (T : J → Module.End K M),
    (∀ (i j : J), T i * T j = T j * T i) →
      ∀ (d : ℕ) (U : Submodule K M),
        Module.finrank K ↥U = d →
          U ≠ ⊥ →
            (∀ (j : J), ∀ x ∈ U, (T j : M → M) x ∈ U) →
              ∃ v ∈ U, v ≠ (0 : M) ∧ ∀ (j : J), ∃ (c : K), (T j : M → M) v = c • v := by
  intro K M _ _ _ _ _ J T hT d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hU hinv
    by_cases h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨v, hv, hv0, fun j => ?_⟩
      obtain ⟨c, hc⟩ := h j
      exact ⟨c, hc v hv⟩
    · rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)
      obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
      have hw1 : T i (w : M) = c • (w : M) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : M) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : U ⊓ (T i).eigenspace c < U := by
        refine lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩
        rw [← heq] at hx
        exact Module.End.mem_eigenspace_iff.mp hx.2
      have hne : U ⊓ (T i).eigenspace c ≠ ⊥ := by
        intro h0
        have hm : (w : M) ∈ U ⊓ (T i).eigenspace c :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩
        rw [h0] at hm
        exact hw0 ((Submodule.mem_bot K).mp hm)
      have hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c := by
        intro j x hx
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h2 : T i x = c • x := Module.End.mem_eigenspace_iff.mp hx.2
        have h3 := LinearMap.congr_fun (hT i j) x
        simp only [Module.End.mul_apply] at h3
        rw [h3, h2, map_smul]
      obtain ⟨v, hv, hv0, hvj⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst
      exact ⟨v, hv.1, hv0, hvj⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpecialLinearTensor
section
noncomputable def UpperTheory.Reformulated.B.SpecialLinearTensor.sl :
    {I : Type} →
      [Fintype I] →
        [dI : DecidableEq I] →
          {W : I → Type} →
            [inst : (i : I) → AddCommGroup (W i)] →
              [inst_1 : (i : I) → _root_.Module ℂ (W i)] →
                (v : I) → ((i : I) → Module.Dual ℂ (W i)) → (PiTensorProduct ℂ fun (i : I) ↦ W i) →ₗ[ℂ] W v :=
  fun {I} _ dI {W} _ _ v f => by
    have prod_update_self (m : (i : I) → W i) (x : W v) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m v x j) =
          ∏ j ∈ Finset.univ.erase v, f j (m j) := by
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have prod_update_ne {i : I} (h : i ≠ v) (m : (j : I) → W j) (x : W i) :
        ∏ j ∈ Finset.univ.erase v, f j (Function.update m i x j) =
          f i x * ∏ j ∈ (Finset.univ.erase v).erase i, f j (m j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨h, Finset.mem_univ i⟩),
        Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    exact PiTensorProduct.lift
      { toFun := fun m => (∏ j ∈ Finset.univ.erase v, f j (m j)) • m v
        map_update_add' := by
          intro d m i x y
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, smul_add]
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              map_add, add_mul, add_smul]
        map_update_smul' := by
          intro d m i c x
          obtain rfl : d = dI := Subsingleton.elim _ _
          by_cases h : i = v
          · subst i
            simp only [prod_update_self, Function.update_self, RingHom.id_apply]
            exact smul_comm _ _ _
          · simp only [prod_update_ne h, Function.update_of_ne (Ne.symm h),
              RingHom.id_apply, map_smul, smul_eq_mul, mul_assoc, mul_smul] }

theorem UpperTheory.Reformulated.B.SpecialLinearTensor.sl_tprod :
    ∀ {I : Type} [inst : Fintype I] [dI : DecidableEq I] {W : I → Type} [inst_1 : (i : I) → AddCommGroup (W i)]
      [inst_2 : (i : I) → _root_.Module ℂ (W i)] (v : I) (f : (i : I) → Module.Dual ℂ (W i)) (m : (i : I) → W i),
      (UpperTheory.Reformulated.B.SpecialLinearTensor.sl v f : (PiTensorProduct ℂ fun (i : I) ↦ W i) → W v)
          ((PiTensorProduct.tprod ℂ : ((i : I) → W i) → PiTensorProduct ℂ fun (i : I) ↦ W i) m) =
        (∏ i ∈ Finset.univ.erase v, (f i : W i → ℂ) (m i)) • m v := by
  intro I _ _ W _ _ v f m
  rw [UpperTheory.Reformulated.B.SpecialLinearTensor.sl, PiTensorProduct.lift.tprod]
  rfl
end

