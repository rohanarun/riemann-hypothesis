module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
public import GroundTheory.ProfiniteCohomology.OpenNormal
public import GroundTheory.ProfiniteCohomology.Bundle0001
public import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
public import GroundTheory.TateCohomology.Bundle0005
public import GroundTheory.TateCohomology.Bundle0003

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.ColimitDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

theorem isLocallyConstant_comp_quotient_mk [IsTopologicalGroup G] (U : OpenNormalSubgroup G) {n : ℕ} {X : Type*}
    (y : (Fin n → G ⧸ (U : Subgroup G)) → X) :
    IsLocallyConstant fun g : Fin n → G => y fun i => (g i : G ⧸ (U : Subgroup G)) :=
  (IsLocallyConstant.of_discrete y).comp_continuous
    (continuous_pi fun i => continuous_quot_mk.comp (continuous_apply i))

noncomputable abbrev quotientMapOfLE {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    G ⧸ (V : Subgroup G) →* G ⧸ (U : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) fun _ hx => h hx

@[simp]
theorem quotientMapOfLE_mk {U V : OpenNormalSubgroup G} (h : V ≤ U) (g : G) :
    quotientMapOfLE h (g : G ⧸ (V : Subgroup G)) = (g : G ⧸ (U : Subgroup G)) :=
  rfl

section Level

variable (A : Rep.{u} k G)

noncomputable def invariantsInclusion {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    Rep.res (quotientMapOfLE h) (A.quotientToInvariants (U : Subgroup G)) ⟶
      A.quotientToInvariants (V : Subgroup G) :=
  Rep.ofHom ⟨Submodule.inclusion (invariants_comp_subtype_antitone A fun _ hx => h hx),
    fun g => QuotientGroup.induction_on g fun _ => LinearMap.ext fun _ => rfl⟩

noncomputable abbrev transitionCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶
      inhomogeneousCochains (A.quotientToInvariants (V : Subgroup G)) :=
  groupCohomology.cochainsMap (quotientMapOfLE h) (invariantsInclusion A h)

noncomputable def transition {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶
      groupCohomology (A.quotientToInvariants (V : Subgroup G)) n :=
  groupCohomology.map (quotientMapOfLE h) (invariantsInclusion A h) n

theorem transitionCochains_refl (U : OpenNormalSubgroup G) :
    transitionCochains A (le_refl U) = 𝟙 _ := by
  rw [← groupCohomology.cochainsMap_id]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)

theorem transitionCochains_trans {U V W : OpenNormalSubgroup G} (hVU : V ≤ U) (hWV : W ≤ V) :
    transitionCochains A (hWV.trans hVU) =
      transitionCochains A hVU ≫ transitionCochains A hWV := by
  rw [← groupCohomology.cochainsMap_comp]
  exact groupCohomology.cochainsMap_congr
    (MonoidHom.ext fun g => QuotientGroup.induction_on g fun _ => rfl) (LinearMap.ext fun _ => rfl)


noncomputable def levelCochains :
    (OpenNormalSubgroup G)ᵒᵖ ⥤ CochainComplex (ModuleCat k) ℕ where
  obj U := inhomogeneousCochains (A.quotientToInvariants (U.unop : Subgroup G))
  map f := transitionCochains A (leOfHom f.unop)
  map_id U := transitionCochains_refl A U.unop
  map_comp f g := transitionCochains_trans A (leOfHom f.unop) (leOfHom g.unop)

variable [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable abbrev infCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (QuotientGroup.mk' (U : Subgroup G))
    (Rep.ofHom (A.ρ.quotientToInvariants_lift (U : Subgroup G)))

noncomputable def inflationCochainsX (U : OpenNormalSubgroup G) (n : ℕ) :
    (inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G))).X n ⟶
      (cochainsComplex A).X n :=
  ModuleCat.ofHom <| LinearMap.codRestrict (locallyConstantCochains A n)
    ((infCochains A U).f n).hom
    fun x => isLocallyConstant_comp_quotient_mk U fun q => (x q : A)

theorem inflationCochainsX_comp_ι (U : OpenNormalSubgroup G) (n : ℕ) :
    inflationCochainsX A U n ≫ (cochainsComplexι A).f n = (infCochains A U).f n :=
  rfl

noncomputable def inflationCochains (U : OpenNormalSubgroup G) :
    inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G)) ⟶ cochainsComplex A where
  f n := inflationCochainsX A U n
  comm' i j _ := by
    rw [← cancel_mono ((cochainsComplexι A).f j), Category.assoc, Category.assoc,
      ← (cochainsComplexι A).comm i j, ← Category.assoc, inflationCochainsX_comp_ι,
      inflationCochainsX_comp_ι, HomologicalComplex.Hom.comm]

@[simp]
theorem inflationCochains_f_hom_apply (U : OpenNormalSubgroup G) (n : ℕ)
    (x : (Fin n → G ⧸ (U : Subgroup G)) →
      Representation.invariants (A.ρ.comp (U : Subgroup G).subtype)) (g : Fin n → G) :
    ((cochainsComplexι A).f n).hom (((inflationCochains A U).f n).hom x) g =
      (x fun i => (g i : G ⧸ (U : Subgroup G)) : A) :=
  rfl

noncomputable def inflation (U : OpenNormalSubgroup G) (n : ℕ) :
    groupCohomology (A.quotientToInvariants (U : Subgroup G)) n ⟶ cohomology A n :=
  HomologicalComplex.homologyMap (inflationCochains A U) n

theorem transitionCochains_comp_inflationCochains {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    transitionCochains A h ≫ inflationCochains A V = inflationCochains A U := by
  ext n : 1
  rw [← cancel_mono ((cochainsComplexι A).f n), HomologicalComplex.comp_f, Category.assoc]
  ext x : 2
  rfl

theorem transition_comp_inflation {U V : OpenNormalSubgroup G} (h : V ≤ U) (n : ℕ) :
    transition A h n ≫ inflation A V n = inflation A U n := by
  unfold transition inflation
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [transitionCochains_comp_inflationCochains]

noncomputable def inflationCochainsCocone : Limits.Cocone (levelCochains A) where
  pt := cochainsComplex A
  ι :=
    { app U := inflationCochains A U.unop
      naturality U V f := by
        exact (transitionCochains_comp_inflationCochains A (leOfHom f.unop)).trans
          (Category.comp_id _).symm }

end Level

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.ColimitUnion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

section Union

variable (A : Rep.{u} k G) {ι : Type u} [Preorder ι] (W : ι → Submodule k A) (hW : Monotone W)
  (hstable : ∀ i g, W i ≤ (W i).comap (A.ρ g))

noncomputable def subrepInclusion {i j : ι} (h : i ≤ j) :
    A.subrepresentation (W i) (hstable i) ⟶ A.subrepresentation (W j) (hstable j) :=
  Rep.ofHom ⟨Submodule.inclusion (hW h), fun _ => LinearMap.ext fun _ => rfl⟩

theorem subrepInclusion_refl {i : ι} (h : i ≤ i) : subrepInclusion A W hW hstable h = 𝟙 _ := by
  ext
  rfl

theorem subrepInclusion_trans {i j l : ι} (h₁ : i ≤ j) (h₂ : j ≤ l) :
    subrepInclusion A W hW hstable (h₁.trans h₂) =
      subrepInclusion A W hW hstable h₁ ≫ subrepInclusion A W hW hstable h₂ := by
  ext
  rfl

theorem subrepInclusion_comp_subtype {i j : ι} (h : i ≤ j) :
    subrepInclusion A W hW hstable h ≫ Rep.subtype A (W j) (hstable j) =
      Rep.subtype A (W i) (hstable i) := by
  ext
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable def subrepCochains : ι ⥤ CochainComplex (ModuleCat k) ℕ where
  obj i := cochainsComplex (A.subrepresentation (W i) (hstable i))
  map h := cochainsMap (subrepInclusion A W hW hstable (leOfHom h))
  map_id i := by rw [subrepInclusion_refl, cochainsMap_id]
  map_comp f g := by rw [← cochainsMap_comp, ← subrepInclusion_trans]

noncomputable def subrepCochainsCocone : Cocone (subrepCochains A W hW hstable) where
  pt := cochainsComplex A
  ι :=
    { app i := cochainsMap (Rep.subtype A (W i) (hstable i))
      naturality i j h := by
        refine (cochainsMap_comp _ _).symm.trans ?_
        rw [subrepInclusion_comp_subtype]
        exact (Category.comp_id _).symm }

theorem subrepCochainsCocone_inj (n : ℕ) (i : ι)
    (y : ((subrepCochains A W hW hstable).obj i).X n)
    (hy : (((subrepCochainsCocone A W hW hstable).ι.app i).f n).hom y = 0) :
    ∃ (j : ι) (f : i ⟶ j), (((subrepCochains A W hW hstable).map f).f n).hom y = 0 := by
  refine ⟨i, 𝟙 i, ?_⟩
  have : Mono (Rep.subtype A (W i) (hstable i)) :=
    (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  have hinj : Function.Injective ((cochainsMap (Rep.subtype A (W i) (hstable i))).f n).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact hinj (hy.trans (map_zero _).symm)

variable [CompactSpace G]


omit [IsTopologicalGroup G] [IsDiscreteRep A] in
include hW in
theorem exists_forall_mem_of_isLocallyConstant [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) {n : ℕ} {f : (Fin n → G) → A} (hf : IsLocallyConstant f) :
    ∃ j, ∀ g, f g ∈ W j := by
  classical
  choose idx hidx using hunion
  obtain ⟨j, hj⟩ := Finset.exists_le (hf.range_finite.toFinset.image idx)
  exact ⟨j, fun g => hW (hj _ (Finset.mem_image_of_mem _ (by simp))) (hidx (f g))⟩

theorem subrepCochainsCocone_surj [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : (subrepCochainsCocone A W hW hstable).pt.X n) :
    ∃ (j : ι) (y : ((subrepCochains A W hW hstable).obj j).X n),
      (((subrepCochainsCocone A W hW hstable).ι.app j).f n).hom y = x := by
  have hx : IsLocallyConstant (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) :=
    (show locallyConstantCochains A n from x).2
  obtain ⟨j, hj⟩ := exists_forall_mem_of_isLocallyConstant A W hW hunion hx
  have hy : IsLocallyConstant fun g : Fin n → G =>
      (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro b
    have : (fun g : Fin n → G => (⟨((cochainsComplexι A).f n).hom x g, hj g⟩ : W j)) ⁻¹' {b} =
        (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) ⁻¹' {(b : A)} := by
      ext g
      simp [Subtype.ext_iff]
    rw [this]
    exact hx.isOpen_fiber _
  refine ⟨j, ⟨_, hy⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι A).f n)).1 inferInstance
  rfl


include hW in
theorem exists_cohomologyMap_subtype_eq [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (x : cohomology A n) :
    ∃ (i : ι) (y : cohomology (A.subrepresentation (W i) (hstable i)) n),
      (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = x :=
  exists_homologyMap_eq_of_cocone (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion n)
    (subrepCochainsCocone_inj A W hW hstable _) x

theorem exists_cohomologyMap_subrepInclusion_eq_zero [Nonempty ι] [IsDirectedOrder ι]
    (hunion : ∀ a : A, ∃ i, a ∈ W i) (n : ℕ) (i : ι)
    (y : cohomology (A.subrepresentation (W i) (hstable i)) n)
    (hy : (cohomologyMap (Rep.subtype A (W i) (hstable i)) n).hom y = 0) :
    ∃ (j : ι) (h : i ≤ j), (cohomologyMap (subrepInclusion A W hW hstable h) n).hom y = 0 := by
  obtain ⟨j, f, hf⟩ := exists_homologyMap_map_eq_zero_of_cocone
    (subrepCochainsCocone A W hW hstable) n
    (subrepCochainsCocone_surj A W hW hstable hunion _)
    (subrepCochainsCocone_inj A W hW hstable n) i y hy
  exact ⟨j, leOfHom f, hf⟩

end Union

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.CyclicCupDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

section Generic

universe u

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

noncomputable def cupRight (h : p + q = n) (b : groupCohomology B q) :
    groupCohomology A p ⟶ groupCohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cupH h).flip b)

end Generic

variable {G : Type} [Group G]

noncomputable def charClass (χ : Additive G →+ AddCircle (1 : ℚ)) : H2 (Rep.trivial ℤ G ℤ) :=
  groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ)

noncomputable def cupCharClassH0 (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :
    H0 A ⟶ H2 A :=
  cupRight (A := A) (B := 𝟙_ (Rep ℤ G)) (zero_add 2) (charClass χ) ≫ map (MonoidHom.id G) (ρ_ A).hom 2

noncomputable def cupCharClass (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :=
  (groupCohomology.H0Iso A).inv ≫ cupCharClassH0 A χ

end GroundTheory.ProfCoh
end

