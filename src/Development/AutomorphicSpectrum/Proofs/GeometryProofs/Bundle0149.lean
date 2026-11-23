module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGeneric
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar

theorem finrank_lieModel_of_algebra (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] [Algebra A K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    (MV : LieModel G (spMap (algebraMap A K) ≫ x) V) : Module.finrank K V = Module.finrank A E₀ := by
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x = spMap (algebraMap A K) ≫ x := rfl
  have hsm : ∀ (a : A) (t : V), a • t = algebraMap A K a • t := fun a t => by
    rw [algebraMap_smul]
  have halg : (dualMap (algebraMap A K)).comp (algebraMap A (DualNumber A)) =
      (algebraMap K (DualNumber K)).comp (algebraMap A K) := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let b : epsAt (spMap (algebraMap A K) ≫ x) ⟶ epsAt x :=
    Over.homMk (spMap (dualMap (algebraMap A K))) (by
      change spMap (dualMap (algebraMap A K)) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap (algebraMap A K) ≫ x
      simp only [spMap]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, halg])
  have htan (e : E₀) : IsTanAt G (spMap (algebraMap A K) ≫ x) (b ≫ M₀.pt e) := by
    have h1 : (Over.homMk (spMap (algebraMap A K)) rfl : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := MonObj.comp_one _
    have h2 : spMap (algebraMap A K) ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap (algebraMap A K) ≫ x) ⟶ G).left := by rw [← h1]; rfl
    have hv := M₀.tan e
    unfold IsTanAt at hv ⊢
    rw [← h2, ← hv]
    change Spec.map _ ≫ spMap (dualMap (algebraMap A K)) ≫ (M₀.pt e).left = spMap (algebraMap A K) ≫ Spec.map _ ≫ (M₀.pt e).left
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    congr 1
    exact RingHom.ext fun a => by simp [dualMap]
  have ex : ∀ e, ∃ t, MV.pt t = b ≫ M₀.pt e :=
    fun e => MV.onto _ (htan e)
  choose f hf using ex
  let j : E₀ →ₗ[A] V :=
    { toFun := f
      map_add' := fun a b => MV.inj (by rw [MV.add, hf, hf, hf, M₀.add, comp_mul])
      map_smul' := fun c e => MV.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc]
        have hb : b ≫ LieTangent.epsScale x c =
            LieTangent.epsScale (spMap (algebraMap A K) ≫ x) (algebraMap A K c) ≫ b := by
          apply Over.OverMorphism.ext
          change spMap (dualMap (algebraMap A K)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
            Spec.map (CommRingCat.ofHom (epsMul (algebraMap A K c))) ≫ spMap (dualMap (algebraMap A K))
          simp only [spMap]
          rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
          congr 1
          congr 1
          refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_smul]
        rw [hb, Category.assoc]) }

  have hl : ∀ e, ((MV.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap A K)) ≫ (M₀.pt e).left) := fun e => by
    change (MV.pt (f e)).left ≫ 𝟙 G.left = _
    rw [hf, Category.comp_id]
    rfl
  have hbc : IsBaseChange K j := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange X G A K x E₀ V M₀ MV j hl
  obtain ⟨hfin, hproj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective X G A x E₀ M₀
  haveI : Module.Free A E₀ := Module.free_of_flat_of_isLocalRing
  rw [← LinearEquiv.finrank_eq hbc.equiv, Module.finrank_baseChange]

theorem finrank_lieModel_eq (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (A : Type) [CommRing A]
    [IsLocalRing A] (x : Sp A ⟶ X) (E₀ : Type) [AddCommGroup E₀] [Module A E₀] (M₀ : LieModel G x E₀) (K : Type)
    [Field K] (c : A →+* K) (y : Sp K ⟶ X) (hy : Spec.map (CommRingCat.ofHom c) ≫ x = y) (V : Type) [AddCommGroup V]
    [Module K V] (MV : LieModel G y V) : Module.finrank K V = Module.finrank A E₀ := by
  subst hy
  letI : Algebra A K := c.toAlgebra
  letI mR : Module A V := Module.compHom V c
  haveI tower : IsScalarTower A K V := ⟨fun a b t => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact finrank_lieModel_of_algebra X G A x E₀ M₀ K V MV

theorem lieModel_transport {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {Li : Type}
    [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) {L : Type} [Field L] {z z' : Sp L ⟶ X} (hz : z' = z)
    {T : Type} [AddCommGroup T] [Module L T] (TL : LieModel G z T) :
    ∃ MC : LieModel G z' T,
      (∀ t, (MC.pt t).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap L L))) ≫ (TL.pt t).left) ∧
      ∀ e t, M.ValAt z' e (MC.pt t) → M.ValAt z e (TL.pt t) := by
  subst hz
  have hd : dualMap (algebraMap L L) = RingHom.id _ := RingHom.ext fun a =>
    by ext <;> simp [dualMap]
  exact ⟨TL, fun t => by rw [hd, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp], fun _ _ h => h⟩

theorem lieModel_valFrame : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ zL T _ _ TL h Ix _ f hξ hli hsp hlat
  have ex : ∀ i, ∃ w, M.ValAt zL (f i) (TL.pt w) := fun i => by
    have hm : f i ∈ M.lat ⟨centre zL, h⟩ := by
      rw [hlat]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := (M.exists_valAt_iff zL (f i)).2 ⟨h, hm⟩
    obtain ⟨t, rfl⟩ := TL.onto v hv.isTanAt
    exact ⟨t, hv⟩
  choose w hw using ex
  have key : ∀ (A : Set Ix) (e : Li), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) →
      ∃ u ∈ Submodule.span L (w '' A), M.ValAt zL e (TL.pt u) := by
    intro A e he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨i, hi, rfl⟩ := he
      exact ⟨w i, Submodule.subset_span ⟨i, hi, rfl⟩, hw i⟩
    | zero => exact ⟨0, zero_mem _, by rw [TL.pt_zero]; exact M.valAt_zero h⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨u', hu', hv'⟩ := hb
      exact ⟨u + u', add_mem hu hu', by rw [TL.add]; exact hv.add hv'⟩
    | smul c a _ ha =>
      obtain ⟨u, hu, hv⟩ := ha
      obtain ⟨_, s, rfl⟩ := c
      refine ⟨(Scheme.stalkClosedPointTo zL).hom s • u, Submodule.smul_mem _ _ hu, ?_⟩
      rw [TL.pt_smul]
      exact hv.smul h s
  have hz : Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL = zL := by
    have e : CommRingCat.ofHom (algebraMap L L) = 𝟙 (CommRingCat.of L) := rfl
    rw [e, Spec.map_id, Category.id_comp]
  obtain ⟨MC, h1, h2⟩ := lieModel_transport M hz TL
  have hc : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap L L)) ≫ zL) :=
    (congrArg centre hz).symm ▸ h
  have hspan : ⊤ ≤ Submodule.span L (Set.range w) := by
    intro t _
    have ht : t ∈ M.fibAt M.lat zL MC :=
      (_root_.GlobalTheory.CompanionTheory.Ar.lieLat_fibAt_iff X G Ω ξ Li M L zL L T MC hξ inferInstance h hc t).2 ⟨TL.pt t, TL.tan t, h1 t⟩
    refine (Submodule.span_le.2 ?_ : M.fibAt M.lat zL MC ≤ _) ht
    rintro w' ⟨h', e, he, hv⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' Set.univ) := by
      rw [Set.image_univ, ← hlat]
      exact he
    obtain ⟨u, hu, hv'⟩ := key _ _ he'
    have := TL.inj ((h2 _ _ hv).unique hξ hv')
    rw [this]
    rwa [Set.image_univ] at hu
  obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre zL)) (X.fromSpecStalk (centre zL))
  have c1 := finrank_lieModel_eq X G _ _ E₀ M₀ Ω (genMap ξ ⟨centre zL, h⟩) ξ (LieTangent.spec_genMap ξ ⟨centre zL, h⟩) Li M
  have c2 := finrank_lieModel_eq X G _ _ E₀ M₀ L (Scheme.stalkClosedPointTo zL).hom zL (LieTangent.spec_centre zL) T TL
  have card : Fintype.card Ix = Module.finrank L T := by
    rw [c2, ← c1, Module.finrank_eq_card_basis (Module.Basis.mk hli hsp.ge)]
  refine ⟨w, hw, linearIndependent_of_top_le_span_of_card_eq_finrank hspan card, top_le_iff.1 hspan, ?_⟩
  intro A e u he hv
  obtain ⟨u', hu', hv'⟩ := key A e he
  rw [TL.inj (hv.unique hξ hv')]
  exact hu'

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalizationAtPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLie

open LieTangent

section SlopeTestRemainingChoices

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap]

theorem spec_dualMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) = spMap (dualMap (ψ.comp φ)) := by
  rw [← dualMap_comp]
  exact spec_comp _ _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X} {E : Type}
  [AddCommGroup E] [Module Ω E]

theorem lieValAt_base (M : LieModel G ξ E) (hξ : IsCptGen ξ) {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R']
    [IsLocalRing R'] (φ : R →+* R') {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : spMap φ ≫ z = z') {e : E}
    {w : epsAt z ⟶ G} {w' : epsAt z' ⟶ G} (h : M.ValAt z e w) (hw : w'.left = spMap (dualMap φ) ≫ w.left) :
    M.ValAt z' e w' := by
  subst hz
  obtain ⟨h1, v, hv, hw0⟩ := h
  have c := centre_specializes φ z
  have h2 := specializes_of_injective (p := ⟨_, h1⟩) (hξ.inj _) c
  have hσ : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes c).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (spMap φ ≫ z)) := Scheme.SpecMap_stalkSpecializes_fromSpecStalk c
  have base : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
      {x : Sp A ⟶ X} {y : Sp B ⟶ X} (hf : spMap f ≫ x = y)
      (u : epsAt x ⟶ G), IsTanAt G x u →
      ∃ b : epsAt y ⟶ epsAt x, b.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ∧ IsTanAt G y (b ≫ u) := by
    intro A B _ _ f x y hf u hu
    have ha : spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ spMap (algebraMap A (DualNumber A)) =
        spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
      rw [spec_comp, spec_comp]
      congr 2
      ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    let b : epsAt y ⟶ epsAt x := Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap f)) (by
      change _ ≫ _ ≫ x = _ ≫ y
      rw [← Category.assoc, ha, Category.assoc, hf])
    refine ⟨b, rfl, ?_⟩
    change _ ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ u.left = _
    have hh : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) =
        spMap f ≫ spMap (TrivSqZeroExt.fstHom A A A).toRingHom := by
      rw [spec_comp, spec_comp]
      congr 2
      exact RingHom.ext fun a => by simp [GlobalTheory.CompanionTheory.Ar.dualMap]
    rw [← Category.assoc, hh, Category.assoc, hu]
    exact congrArg (·.left) (comp_one (M := G) (Over.homMk (spMap f) hf : Over.mk y ⟶ Over.mk x))
  obtain ⟨b, hb, ht⟩ := base (X.presheaf.stalkSpecializes c).hom hσ v hv.1
  refine ⟨h2, b ≫ v, ⟨ht, ?_⟩, ?_⟩
  · change _ = _ ≫ (b.left ≫ v.left)
    rw [hb]
    have e : (genMap ξ ⟨_, h2⟩).comp (X.presheaf.stalkSpecializes c).hom = genMap ξ ⟨_, h1⟩ :=
      RingHom.ext fun s => genMap_specializes ⟨_, h1⟩ h2 c s
    rw [hv.2, ← Category.assoc, spec_dualMap, e]
  · change _ = _ ≫ (b.left ≫ v.left)
    rw [hb]
    have e : (Scheme.stalkClosedPointTo (spMap φ ≫ z)).hom.comp (X.presheaf.stalkSpecializes c).hom =
        φ.comp (Scheme.stalkClosedPointTo z).hom :=
      RingHom.ext fun s => congrArg (fun g => g.hom s) (stalk_base φ z)
    rw [hw, hw0, ← Category.assoc, ← Category.assoc, spec_dualMap, spec_dualMap, e]

omit [GrpObj G] [Module Ω E] in
theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {x : Sp R ⟶ S} {x' : Sp R' ⟶ S} (hx : spMap c ≫ x = x') {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G x' E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  subst hx
  exact (_root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.existsUnique_semilinear_lifts S G R R' c x E E' M M').exists

end SlopeTestRemainingChoices

theorem dvd_absNorm {L : Type} [Field L] [NumberField L] (c : 𝓞 L) (hc : c ≠ 0) :
    ∃ (n : ℕ) (c' : 𝓞 L), n ≠ 0 ∧ (n : 𝓞 L) = c * c' := by
  obtain ⟨c', h⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
  refine ⟨_, c', ?_, by rw [← h, mul_comm]⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hc

theorem exists_integral_form : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra (𝓞 L) A]
    [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L] (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) (f : Module.Dual Ω Li)
    (h : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) A) ≫ z)), IsCptGen ξ →
    (∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩) →
    (∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩) →
    ∃ g : B.carrier →ₗ[𝓞 L] A,
      (∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (u : L),
        M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
        ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (f e) u → algebraMap A L (g x) = u) ∧
      ∀ (e : Li) (u : A), e ∈ M.lat ⟨_, h⟩ → ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) u →
        ∃ (d : 𝓞 L) (n : ℕ) (x x' : B.carrier) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
          d ∉ 𝔭 ∧ n ≠ 0 ∧ g x = algebraMap (𝓞 L) A d * u ∧ M.ValAt _ ((n : Ω) • e) v ∧
          (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left) ∧ (n : 𝓞 L) • x = d • x' := by
  intro X G _ _ _ Ω _ ξ Li _ _ M L _ _ 𝔭 _ A _ _ _ _ _ _ z B MB f h hξ hreg hreg'
  have hzz : spMap (algebraMap A L) ≫ spMap (algebraMap (𝓞 L) A) ≫ z = spMap (algebraMap (𝓞 L) L) ≫ z := by
    rw [← Category.assoc, spec_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G A (spMap (algebraMap (𝓞 L) A) ≫ z)
  obtain ⟨EL, _, _, ⟨ML⟩⟩ := lieModel_exists X G L (spMap (algebraMap (𝓞 L) L) ≫ z)
  letI : Module (𝓞 L) EA := Module.compHom EA (algebraMap (𝓞 L) A)
  haveI : IsScalarTower (𝓞 L) A EA := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module (𝓞 L) EL := Module.compHom EL (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L EL := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨j₀, hj₀⟩ := exists_transport (algebraMap (𝓞 L) A) rfl MB MA
  obtain ⟨k, hk⟩ := exists_transport (algebraMap A L) hzz MA ML
  let j : B.carrier →ₗ[𝓞 L] EA :=
    { toFun := j₀, map_add' := j₀.map_add, map_smul' := fun c x => j₀.map_smulₛₗ c x }
  have hks : ∀ (c : 𝓞 L) (y : EA), k (c • y) = c • k y := fun c y => by
    have e : c • y = algebraMap (𝓞 L) A c • y := rfl
    have e' : c • k y = algebraMap (𝓞 L) L c • k y := rfl
    rw [e, e', k.map_smulₛₗ, IsScalarTower.algebraMap_apply (𝓞 L) A L]
  let jL : B.carrier →ₗ[𝓞 L] EL :=
    { toFun := fun x => k (j x), map_add' := fun x x' => by simp
      map_smul' := fun c x => by simp [hks] }
  have hj : ∀ x, ((MA.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) A)) ≫ (MB.pt x).left) := hj₀
  have hjL : ∀ x, ((ML.pt (jL x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) := fun x => by
    have h1 := hk (j x)
    have h2 := hj x
    rw [Category.comp_id] at h1 h2 ⊢
    change (ML.pt (k (j x))).left = _
    rw [h1, h2, ← Category.assoc, spec_dualMap, ← IsScalarTower.algebraMap_eq]
  have hbA : IsBaseChange A j := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange X G (𝓞 L) A z B.carrier EA MB MA j hj
  have hbL : IsBaseChange L jL := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_isBaseChange X G (𝓞 L) L z B.carrier EL MB ML jL hjL
  haveI : IsLocalizedModule 𝔭.primeCompl j := (isLocalizedModule_iff_isBaseChange 𝔭.primeCompl A j).2 hbA
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) jL :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L jL).2 hbL
  have hinj : Function.Injective jL := fun x y hxy => by
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors (𝓞 L)) jL).1 hxy
    exact smul_right_injective B.carrier (nonZeroDivisors.ne_zero c.2) hc
  have hL : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) :=
    specializes_of_injective (p := ⟨_, h⟩) (hξ.inj _) (hzz ▸ centre_specializes (algebraMap A L) (spMap (algebraMap (𝓞 L) A) ≫ z))
  obtain ⟨gA, hgA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional X G Ω ξ Li M A _ h EA MA f hξ hreg
  obtain ⟨gL, hgL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional X G Ω ξ Li M L _ hL EL ML f hξ (hreg' hL)
  obtain ⟨ev, hev, -, hspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ Li M A _ h EA MA hξ inferInstance
  have hlift : ∀ (e : Li) (y : EA), M.ValAt (spMap (algebraMap (𝓞 L) A) ≫ z) e (MA.pt y) →
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (ML.pt (k y)) := fun e y hv => by
    refine lieValAt_base M hξ (algebraMap A L) hzz hv ?_
    have h1 := hk y
    rwa [Category.comp_id] at h1
  have hcompat : ∀ y : EA, gL (k y) = algebraMap A L (gA y) := fun y => by
    have hy : y ∈ Submodule.span A (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨e, he⟩, rfl⟩ := hy
      have hv := (hev e _).2 ⟨he, rfl⟩
      obtain ⟨s, hs⟩ := hreg e he
      have hu : ValAt ξ (spMap (algebraMap (𝓞 L) A) ≫ z) (f e) _ := ⟨h, s, hs, rfl⟩
      have hu' := valAt_base hξ (algebraMap A L) hu
      rw [hzz] at hu'
      rw [hgA _ _ _ hv hu]
      exact hgL _ _ _ (hlift _ _ hv) hu'
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c y _ hy => simp [k.map_smulₛₗ, hy]
  refine ⟨(gA.restrictScalars (𝓞 L)).comp j, ?_, ?_⟩
  · intro x e v u hv hl hu
    have hvx : v = ML.pt (jL x) := by
      apply Over.OverMorphism.ext
      have h4 := hjL x
      rw [Category.comp_id] at hl h4
      exact hl.trans h4.symm
    subst hvx
    exact (hcompat (j x)).symm.trans (hgL _ _ _ hv hu)
  · intro e u he hu
    have hv := (hev e _).2 ⟨he, rfl⟩
    have hgy := hgA _ _ _ hv hu
    obtain ⟨⟨x, d⟩, hxd⟩ := IsLocalizedModule.surj 𝔭.primeCompl j (ev ⟨e, he⟩)
    replace hxd : (d : 𝓞 L) • ev ⟨e, he⟩ = j x := hxd
    obtain ⟨⟨x₀, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) jL (k (ev ⟨e, he⟩))
    replace hc : (c : 𝓞 L) • k (ev ⟨e, he⟩) = jL x₀ := hc
    obtain ⟨n, c', hn, hc'⟩ := dvd_absNorm (c : 𝓞 L) (nonZeroDivisors.ne_zero c.2)
    have hx' : jL (c' • x₀) = (n : 𝓞 L) • k (ev ⟨e, he⟩) := by
      rw [map_smul, ← hc, hc', mul_comm, mul_smul]
    refine ⟨d, n, x, c' • x₀, ML.pt (jL (c' • x₀)), d.2, hn, ?_, ?_, hjL _, ?_⟩
    · change gA (j x) = _
      rw [← hxd, ← algebraMap_smul A (d : 𝓞 L) (ev ⟨e, he⟩), map_smul, hgy, smul_eq_mul]
    · have hs := (hlift _ _ hv).smul hL (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
      rw [map_natCast, map_natCast] at hs
      have e1 : (n : 𝓞 L) • k (ev ⟨e, he⟩) = (n : L) • k (ev ⟨e, he⟩) := by
        rw [← algebraMap_smul L (n : 𝓞 L), map_natCast]
      rw [hx', e1, ML.pt_smul]
      exact hs
    · apply hinj
      rw [map_smul, map_smul, hx']
      change (n : 𝓞 L) • k (j x) = _
      rw [← hxd, hks, smul_comm]

end GlobalTheory.CompanionTheory.Ar.RootHt.FinLie
end
end

