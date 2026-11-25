module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplex
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMoveDefiniteSimilitudePairMarked
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexMumfordBundleOrigin
section
attribute [-instance] Formalism.BasicNotions.LocLat.modO Formalism.BasicNotions.LocLat.towO Formalism.BasicNotions.LocLat.modFun Formalism.BasicNotions.LocLat.modSubFun Formalism.BasicNotions.LocLat.modT
attribute [-instance] GlobalTheory.AdmLoc.modTens GlobalTheory.AdmLoc.modFun GlobalTheory.AdmLoc.modProd GlobalTheory.AdmLoc.modQuot GlobalTheory.AdmLoc.twistedModuleH1 GlobalTheory.AdmLoc.twistedSubmoduleH1 GlobalTheory.AdmLoc.moduleH1Alt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.MumfordLocalComplex
open GlobalTheory.CechPic GlobalTheory.StabFlat GlobalTheory.PrimitiveOverValuationRing

theorem exists_ideal_complex_cech (hG : GlobalFnsSt) {V : Type} [CommRing V] (B : Over (Spec (CommRingCat.of V)))
    [GrpObj B] [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ}
    (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a) :
    ∃ (I : Ideal A) (C : CochainComplex (ModuleCat.{0} A) ℕ), (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧
      (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧
      Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] A ⧸ I) ∧
      (∀ p : Ideal A, p.IsPrime → ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p ∧
        ∀ i, (¬ I ≤ p ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧
      (∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
        (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
          I ≤ RingHom.ker φ) ∧
      ∀ (K : Type) [Field K] (φ : A →+* K),
        (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
        ∀ (X' : Scheme.{0}) (π' : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)),
        IsPullback π' f' B.hom (Spec.map (CommRingCat.ofHom φ) ≫ a ≫ B.hom) →
        ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
        ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K]
          (cechLB f' (LB.triv X') D).homology i) := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃, c₄⟩ := _root_.GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, C, c₁, c₂, ⟨eC.trans eI⟩, fun p _ => ?_, fun R _ _ φ =>
    (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans (hI R φ _ _ _ (IsPullback.of_hasPullback _ _)), ?_⟩
  · let K := AlgebraicClosure p.ResidueField
    let φ : A →+* K := (algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)
    have hk : RingHom.ker φ = p := by
      rw [RingHom.ker_comp_of_injective _ (algebraMap p.ResidueField K).injective, Ideal.ker_algebraMap_residueField]
    refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
    rcases hi with hi | hi
    · exact Or.inr fun ht => hi (hk ▸ (hI K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)
    · exact Or.inl hi
  · intro K _ φ hy X' π' f' hX κ _ _ D hD hc i
    let π : X' ⟶ B'.left := pullback.lift π' (f' ≫ Spec.map (CommRingCat.ofHom φ)) (by
      simp only [Category.assoc]
      exact hX.w)
    have hπ : IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hpb
      rw [pullback.lift_fst]
      exact hX
    have ht : Triv (F.pull π) := (test K φ X' π f' hπ).2 hy
    obtain ⟨w, hw⟩ := (CechPic.iso_triv_iff (F.pull π)).2 ht
    obtain ⟨e⟩ := c₄ K φ X' π f' hπ κ D hD hc i
    exact ⟨e.trans (HomologicalComplex.homologyMapIso
      (cechLBCongr f' D (LB.isLB_triv X') (pull_isLB hF π) w hw) i).symm.toLinearEquiv⟩

end GlobalTheory.MumfordLocalComplex

namespace GlobalTheory.MumfordLocalComplex

theorem exists_ideal_free_complex_at_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), L.IsLB → IsProjBy A.hom → (∃ t : LB.Gen (Theta A L), t.IsGen) → IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → (∀ (T : Over (Sp K)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∃ (J : Ideal (A.left.presheaf.stalk x₀)) (C : CochainComplex (ModuleCat.{0} (A.left.presheaf.stalk x₀)) ℕ) (φ : A.left.presheaf.stalk x₀ →+* K), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) ∧ RingHom.ker φ = IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∧ (∀ i, Module.Free (A.left.presheaf.stalk x₀) (C.X i) ∧ Module.Finite (A.left.presheaf.stalk x₀) (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual (A.left.presheaf.stalk x₀) (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A.left.presheaf.stalk x₀] (A.left.presheaf.stalk x₀ ⧸ J)) ∧ (∀ p : PrimeSpectrum (A.left.presheaf.stalk x₀), ∃ (K' : Type) (_ : Field K') (φ' : A.left.presheaf.stalk x₀ →+* K'), RingHom.ker φ' = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀) ∨ g < i) → (((ModuleCat.extendScalars φ').mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty (((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i) ≃ₗ[K] (cechLB A.hom (LB.triv A.left) D).homology i) := by
  intro K _ _ A _ g hA hg L H _ j hL hp hΘ _ hjc hfin hH x₀ hx₀
  have := hA.comm
  have := hA.smooth
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A L hL
  let ηK : Sp K ⟶ A.left := (η[A]).left
  have hηK : ηK ≫ A.hom = 𝟙 _ := Over.w η[A]
  obtain ⟨e, rfl⟩ := hx₀
  obtain rfl : e = IsLocalRing.closedPoint K := @Subsingleton.elim (Sp K) inferInstance _ _
  let φ : A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K)) →+* K := (Scheme.stalkClosedPointTo ηK).hom
  have hφl : IsLocalHom φ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo ηK).hom)
  have hφa : Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) = ηK :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ηK
  have h1 : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨z, hz⟩ := (hH (𝟙_ _) η[A]).1 (h1 ▸ memKL_one hL (𝟙_ (Over (Sp K))))
  have hy : ∃ y : Spec (CommRingCat.of K) ⟶ H.left,
      y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) :=
    ⟨z.left, by rw [hφa]; exact congrArg (·.left) hz⟩
  haveI hN : IsNoetherianRing (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) := inferInstance
  obtain ⟨I, C, c₁, c₂, eC, c₃, hI, c₅⟩ := @exists_ideal_complex_cech globalFns_holds _ _ A _ _ hA hp g hg L _ hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x)) (A.left.presheaf.stalk (ηK (IsLocalRing.closedPoint K))) _ hN _
    (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) K _ φ hφl hy
  refine ⟨I, C, φ, fun R' _ ψ => _root_.GlobalTheory.factor_closedImmersion_iff_of_local _ A.left H.left _ j.left hjc I hI R' ψ, ?_, c₁, c₂, eC,
    fun p => ?_, ?_⟩
  · exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (RingHom.ker_ne_top φ) fun x hx => by
      simpa [IsLocalRing.maximalIdeal_eq_bot] using map_nonunit φ x hx).symm
  · obtain ⟨K', _, φ', hk, hex⟩ := c₃ p.asIdeal p.isPrime
    refine ⟨K', inferInstance, φ', hk, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
    obtain ⟨y, hy'⟩ := (hI K' φ').2 (hk ▸ hIp)
    let q := Spec.map (CommRingCat.ofHom φ') (IsLocalRing.closedPoint K')
    have hq : q.asIdeal = RingHom.ker φ' := by
      show Ideal.comap φ' (IsLocalRing.maximalIdeal K') = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K')) =
        A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      congrArg (fun f => f (IsLocalRing.closedPoint K')) hy'
    have hc : IsClosed ({j.left (y (IsLocalRing.closedPoint K'))} : Set A.left) := by
      have := j.left.isClosedEmbedding.isClosedMap _
        (GlobalTheory.StabFlat.isClosed_of_isFinite H.hom (y (IsLocalRing.closedPoint K')) (Subsingleton.elim _ (IsLocalRing.closedPoint K)))
      rwa [Set.image_singleton] at this
    have hs : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ⤳ ηK (IsLocalRing.closedPoint K) := by
      have : A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q ∈
          Set.range (A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K))) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : ηK (IsLocalRing.closedPoint K) = A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) q :=
      (hs.mem_closed hc e.symm).trans e
    have hq' : q = IsLocalRing.closedPoint _ := (A.left.fromSpecStalk _).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, ← hq, hq']
    rfl
  · intro κ _ _ D hD hc i
    have hsq : IsPullback (𝟙 A.left) A.hom A.hom
        (Spec.map (CommRingCat.ofHom φ) ≫ A.left.fromSpecStalk (ηK (IsLocalRing.closedPoint K)) ≫ A.hom) := by
      rw [← Category.assoc, hφa, hηK]
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    exact c₅ K φ hy A.left (𝟙 _) A.hom hsq κ D hD hc i

end GlobalTheory.MumfordLocalComplex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

theorem isFundamentalDomain_inf {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}
    (hm : ∀ g : G, Measurable (g * ·)) (hinv : ∀ g : G, μ.map (g * ·) = μ)
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (S : Subgroup G) :
    ∃ 𝓓 : Set G, IsFundamentalDomain ↥(Γ ⊓ S) 𝓓 μ := by
  classical
  let Q' : Subgroup Γ := (Γ ⊓ S).subgroupOf Γ
  haveI : Countable (Γ ⧸ Q') := Function.Surjective.countable QuotientGroup.mk_surjective
  let rep : Γ ⧸ Q' → Γ := fun c => (Quotient.out c)⁻¹
  have hmp : ∀ g : G, MeasurePreserving (g * ·) μ μ := fun g => ⟨hm g, hinv g⟩
  have himg : ∀ (g : G) (s : Set G), g • s = (g⁻¹ * ·) ⁻¹' s := by
    intro g s; ext x; simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hnm : ∀ g : G, NullMeasurableSet (g • D) μ := fun g => by
    rw [himg]; exact hD.nullMeasurableSet.preimage (hmp g⁻¹).quasiMeasurePreserving
  refine ⟨⋃ c, ((rep c : Γ) : G) • D, ?_⟩
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun c => hnm _
  · filter_upwards [hD.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q' γ
    have hQ : ((h : Γ) : G) ∈ Γ ⊓ S := (Subgroup.mem_subgroupOf).1 h.2
    refine ⟨⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩, Set.mem_iUnion.2 ⟨(γ : Γ ⧸ Q'), ?_⟩⟩
    rw [himg, Set.mem_preimage]
    have e1 : ((rep (γ : Γ ⧸ Q') : Γ) : G)⁻¹ = (γ : G) * ((h : Γ) : G) := by
      simp only [rep, inv_inv]
      have := congrArg (fun y : Γ => (y : G)) hh
      simpa using this
    rw [e1]
    have : (γ : G) * ((h : Γ) : G) * ((⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩ : ↥(Γ ⊓ S)) • x) = γ • x := by
      rw [Subgroup.smul_def, Subgroup.smul_def]
      simp [smul_eq_mul, mul_assoc]
    rw [this]; exact hγ
  · intro g hg
    have hsm : g • ⋃ c, ((rep c : Γ) : G) • D = ⋃ c, ((g : G) * ((rep c : Γ) : G)) • D := by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun c => ?_
      rw [← smul_smul]; rfl
    rw [hsm, AEDisjoint.iUnion_left_iff]
    intro c
    rw [AEDisjoint.iUnion_right_iff]
    intro c'
    have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
    let γ₁ : Γ := ⟨g, hgΓ⟩ * rep c
    have hne : γ₁ ≠ rep c' := by
      intro heq
      have hmem : (Quotient.out c)⁻¹ * Quotient.out c' ∈ Q' := by
        rw [Subgroup.mem_subgroupOf]
        have : (Quotient.out c')⁻¹ = ⟨g, hgΓ⟩ * (Quotient.out c)⁻¹ := by
          simpa [γ₁, rep] using heq.symm
        have h2 : (Quotient.out c)⁻¹ * Quotient.out c' = (⟨g, hgΓ⟩ : Γ)⁻¹ := by
          rw [← inv_inj, mul_inv_rev, inv_inv, this, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
        simpa using inv_mem g.2
      have hcc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact (QuotientGroup.eq).2 hmem
      subst hcc
      apply hg
      have : (⟨g, hgΓ⟩ : Γ) = 1 := by simpa [γ₁] using heq
      ext; simpa using congrArg Subtype.val this
    exact hD.aedisjoint hne
  · intro g
    exact (hmp (g : G)).quasiMeasurePreserving

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

set_option synthInstance.maxHeartbeats 400000 in
theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

theorem exists_fundamentalDomain_ratStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' hT
  haveI := countable_ratU σ G.V.J
  have hgood := hT.geo.hM
  haveI := hgood.haar
  exact isFundamentalDomain_inf (measurable_mul_left σ G.V.J) (fun g => map_mul_left_eq_self G.M.μ g) hgood.dom _

end GlobalTheory.QDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
section
attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL GlobalTheory.SplitFlip.secondCountable_GL GlobalTheory.SplitFlip.t2Space_general_linear_group
noncomputable section
namespace GlobalTheory.StabHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

end GlobalTheory.StabHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergCoords
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.HeisCoords

open Matrix

section Cplx

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)

variable {J}

end Cplx

section Coords

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

end Coords

section Transfer

open Formalism.UG (cT bc UJ)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {ν : InfinitePlace F}

theorem archMat_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E ν) (g : HA ν.Completion σ J) :
    (GlobalTheory.Orb.archMat σ J τ g)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ g = J.map τ.1 :=
  (archEquiv J hcm τ g).2

end Transfer

open Formalism.UG (cT bc UJ)

end GlobalTheory.HeisCoords

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMoveDefiniteSimilitudePairMarkedStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_move_definiteSimilitudePair_marked : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → Odd G.n → ∀ (P0 : Polynomial G.F) (μ : ℂ) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → Irreducible P0 → P0.eval₂ v.embedding μ = 0 → ∃ A : Polynomial G.F, (∀ Q : DPair G, Q.pol = P0 → ∃ P : Pair G, P.γ = Q.γ ∧ P.c = Q.c ∧ (P.β : G.C) = Polynomial.aeval (Q.γ : G.C) A * Q.β ∧ P.Mark μ ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) ∧ (∀ P : Pair G, P.pol = P0 → P.Mark μ → ∃ Q : DPair G, Q.γ = P.γ ∧ Q.c = P.c ∧ (P.β : G.C) = Polynomial.aeval (P.γ : G.C) A * Q.β ∧ (∃ u : (AfP p ⊗[ℚ] G.C)ˣ, (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.γ : G.C) = inC G (AfP p) (Q.γ : G.C) * u ∧ (u : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (Q.β : G.C) * (starT G.star (AfP p) u).unop = inC G (AfP p) (P.β : G.C))) := by
  first | (exact @GlobalTheory.LKDef.move_definite) | (exact GlobalTheory.LKDef.move_definite) | (intros; apply GlobalTheory.LKDef.move_definite  <;> assumption)
end

