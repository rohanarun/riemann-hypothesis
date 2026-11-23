module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Approx

private theorem eq_of_sp_complex_pts {K : Type} [Field K] (a b : ↥(Sp K)) : a = b := by
  revert a b
  change ∀ a b : PrimeSpectrum K, a = b
  intro a b
  exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)

private theorem nonempty_sp (K : Type) [Field K] : Nonempty ↥(Sp K) := by
  change Nonempty (PrimeSpectrum K)
  infer_instance

theorem connectedSpace_pullback_of_fieldHom {k K K' : Type} [CommRing k] [Field K] [Field K']
    {X : Scheme.{0}} (p : X ⟶ Sp k) (f : k →+* K) (j : K →+* K')
    (h : ConnectedSpace ↥(pullback p (spMap (j.comp f)))) :
    ConnectedSpace ↥(pullback p (spMap f)) := by
  rw [spMap_comp] at h
  let e := pullbackLeftPullbackSndIso p (spMap f) (spMap j)
  let g : pullback p (spMap j ≫ spMap f) ⟶ pullback p (spMap f) :=
    e.inv ≫ pullback.fst (pullback.snd p (spMap f)) (spMap j)
  refine Function.Surjective.connectedSpace (f := ⇑g) ?_ g.continuous
  intro z
  obtain ⟨y'⟩ := nonempty_sp K'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p (spMap f)) (g := spMap j) z y' (eq_of_sp_complex_pts _ _)
  refine ⟨e.hom w, ?_⟩
  have h2 : e.hom ≫ g = pullback.fst (pullback.snd p (spMap f)) (spMap j) := by
    simp [g, e]
  rw [← hw, ← h2]
  rfl

private theorem connectedSpace_of_iso {A B : Scheme.{0}} (e : A ≅ B) [ConnectedSpace A] :
    ConnectedSpace B := by
  refine Function.Surjective.connectedSpace (f := ⇑e.hom) (fun b => ⟨e.inv b, ?_⟩) e.hom.continuous
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

theorem geometricallyConnected_pullback_snd_iff {X S T : Scheme.{0}} (p : X ⟶ S) (g : T ⟶ S) :
    GeometricallyConnected (pullback.snd p g) ↔
      ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace ↥(pullback p (y ≫ g)) := by
  rw [geometricallyConnected_iff]
  constructor
  · intro H K _ y
    haveI : ConnectedSpace ↥(pullback (pullback.snd p g) y) :=
      H y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    exact connectedSpace_of_iso (pullbackLeftPullbackSndIso p g y)
  · intro H K _ y Z fst snd hpb
    haveI := H K y
    exact connectedSpace_of_iso (hpb.isoPullback ≪≫ pullbackLeftPullbackSndIso p g y).symm

theorem geometricallyConnected_pullback_snd_spMap_iff {k R : Type} [CommRing k] [CommRing R]
    {X : Scheme.{0}} (p : X ⟶ Sp k) (a : k →+* R) :
    GeometricallyConnected (pullback.snd p (spMap a)) ↔
      ∀ (K : Type) [Field K] (φ : R →+* K), ConnectedSpace ↥(pullback p (spMap (φ.comp a))) := by
  rw [geometricallyConnected_pullback_snd_iff]
  constructor
  · intro H K _ φ
    have := H K (spMap φ)
    rwa [← spMap_comp] at this
  · intro H K _ y
    obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, spMap φ = y :=
      ⟨(Spec.preimage (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))).hom, Spec.map_preimage _⟩
    rw [← spMap_comp]
    exact H K φ

theorem exists_field_amalgam {F K₁ K₂ : Type} [Field F] [Field K₁] [Field K₂]
    (a : F →+* K₁) (b : F →+* K₂) :
    ∃ (L : Type) (_ : Field L) (i : K₁ →+* L) (j : K₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  haveI : Nontrivial (K₁ ⊗[F] K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[F] K₂)
  letI := Ideal.Quotient.field m
  refine ⟨K₁ ⊗[F] K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  congr 1
  exact (Algebra.TensorProduct.algebraMap_apply x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)

theorem exists_residueField_lift {k K : Type} [CommRing k] [Field K] (f : k →+* K)
    (x : PrimeSpectrum k) (hx : x.asIdeal = RingHom.ker f) :
    ∃ ψ : x.asIdeal.ResidueField →+* K, ψ.comp (algebraMap k x.asIdeal.ResidueField) = f := by
  have h2 : x.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) := by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => Ideal.mem_primeCompl_iff.mp hr ?_
    rw [hx]
    exact RingHom.mem_ker.mpr h0
  refine ⟨Ideal.ResidueField.lift x.asIdeal f hx.le h2, ?_⟩
  ext r
  exact Ideal.ResidueField.lift_algebraMap x.asIdeal f hx.le h2 r

theorem geometricallyConnected_pullback_snd_spMap_iff_residueField :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k),
      GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔
        ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)),
          GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  intro k V _ _ _ X p
  rw [geometricallyConnected_pullback_snd_spMap_iff]
  constructor
  · rintro H x ⟨q, rfl⟩
    rw [geometricallyConnected_pullback_snd_spMap_iff]
    intro K _ ψ
    have hker : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker ((algebraMap V q.asIdeal.ResidueField).comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      rfl
    obtain ⟨ψ', hψ'⟩ := exists_residueField_lift _ _ hker
    obtain ⟨L, hL, i, j', hij⟩ := exists_field_amalgam ψ ψ'
    apply connectedSpace_pullback_of_fieldHom p _ i
    have e : i.comp (ψ.comp (algebraMap k (PrimeSpectrum.comap (algebraMap k V) q).asIdeal.ResidueField)) =
        (j'.comp (algebraMap V q.asIdeal.ResidueField)).comp (algebraMap k V) := by
      rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    rw [e]
    exact H L _
  · intro H K _ φ
    haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    let q : PrimeSpectrum V := ⟨RingHom.ker φ, inferInstance⟩
    have hx : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker (φ.comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker]
      rfl
    obtain ⟨ψ, hψ⟩ := exists_residueField_lift _ _ hx
    have := (geometricallyConnected_pullback_snd_spMap_iff p _).mp (H _ ⟨q, rfl⟩) K ψ
    rwa [hψ] at this

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralOfClosedFibre
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_comp_residue_eq (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (K : Type) [Field K] (φ : A →+* K) :
    ∃ ψ : IsLocalRing.ResidueField A →+* K, ψ.comp (IsLocalRing.residue A) = φ := by
  have hm : (RingHom.ker φ).IsMaximal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    exact IsArtinianRing.isMaximal_of_isPrime _
  have he : RingHom.ker φ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  have H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := fun a ha => by
    rw [← he] at ha
    exact (RingHom.mem_ker).1 ha
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H,
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩

theorem geometricallyIntegral_of_closedFibre (A : Type) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A)
    (h : GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A)))) :
    GeometricallyIntegral p := by
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ψ, hψ⟩ := exists_comp_residue_eq A K (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]
    exact Spec.map_preimage y
  have hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A) := by
    rw [Category.assoc, hy]
    exact hpb.w
  have hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫
      pullback.fst p (spMap (IsLocalRing.residue A))) snd p
      (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A)) := by
    rw [pullback.lift_fst, hy]
    exact hpb
  have hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd
      (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ)) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq

theorem isIso_appTop_of_artinian : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (X : Scheme.{0}) (p : X ⟶ Sp A), Flat p → IsProper p →
    GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) → IsIso p.appTop := by
  intro A _ _ _ X p hflat hprop hgi
  haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  haveI := hflat
  haveI := hprop
  haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi
  exact GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GroupPointsEquivCommonCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MarkFibre

theorem exists_fibre_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  intro E _ _ _ H S₁ S₂ V t₁ t₂ tV f₁ f₂ m₁ m₂ x y₁ y₂ h₁ h₂
  subst h₁ h₂
  have hw₁ : m₁.cm.F ≫ t₁.G.hom = tV.G.hom ≫ f₁ := m₁.cart.1.w
  have hw₂ : m₂.cm.F ≫ t₂.G.hom = tV.G.hom ≫ f₂ := m₂.cart.1.w
  obtain ⟨e₁, he₁, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₁ 0 x (x ≫ f₁) rfl
  obtain ⟨e₂, he₂, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₂ 0 x (x ≫ f₂) rfl
  have mul₁ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₁ (a * b) = Out.toBase hw₁ a * Out.toBase hw₁ b :=
    fun T a b => Over.OverMorphism.ext (m₁.cart.2 T a b (Out.toBase hw₁ a) (Out.toBase hw₁ b) rfl rfl).symm
  have mul₂ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₂ (a * b) = Out.toBase hw₂ a * Out.toBase hw₂ b :=
    fun T a b => Over.OverMorphism.ext (m₂.cart.2 T a b (Out.toBase hw₂ a) (Out.toBase hw₂ b) rfl rfl).symm
  have b₁ : ∀ p, Out.toBase hw₁ (e₁ p) = p := fun p => Over.OverMorphism.ext (he₁ p)
  have b₂ : ∀ p, Out.toBase hw₂ (e₂ p) = p := fun p => Over.OverMorphism.ext (he₂ p)
  have key : ∀ q, e₁ ((e₂.trans e₁.symm) q) = e₂ q := fun q => e₁.apply_symm_apply _
  refine ⟨(e₂.trans e₁.symm).toEquiv, fun q q' => map_mul (e₂.trans e₁.symm) q q', fun q =>
    ⟨(e₂ q).left, Over.w (e₂ q), he₂ q, ?_⟩, fun N q q' ζ h => ?_⟩
  · have := he₁ ((e₂.trans e₁.symm) q)
    rw [key] at this
    exact this
  · have ha : e₂ q ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.1).trans (map_one e₁)
    have ha' : e₂ q' ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.2.1).trans (map_one e₁)
    obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil tV.cub ha ha'
    have c₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₁ _ _ m₁.cm hw₁ mul₁ _ _ t₁.cub tV.cub m₁.lin N _ _ _ ζ' hζ'
    have c₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₂ _ _ m₂.cm hw₂ mul₂ _ _ t₂.cub tV.cub m₂.lin N _ _ _ ζ' hζ'
    rw [b₂, b₂] at c₂
    rw [← key q, ← key q', b₁, b₁] at c₁
    obtain rfl : ζ' = ζ := c₁.unique h
    exact c₂

end GlobalTheory.CompanionTheory.Ar.MarkFibre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLabelFrame
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem not_inFibre_centre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z)
    (r : ℕ) (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hu : IsUnit ((r : X.presheaf.stalk (centre z))) := by
    have h1 : IsUnit ((Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z))) := by
      have e : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
      exact e ▸ hr0.isUnit
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ h1
  obtain ⟨u, hu⟩ := hu
  have hg : genMap ξ ⟨centre z, h⟩ (u : X.presheaf.stalk (centre z)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine not_not.2 ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem frame_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z lab r s h hs i
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeChar0.lattices_of_char_zero E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hinj
    ⟨centre z, h⟩ (fun r hr => not_inFibre_centre 𝔐.ξ z h r hr)
  have hmem : s i ∈ 𝔐.V lab ⟨centre z, h⟩ := by
    rw [hs.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h1 lab] at hmem
  have hlat : s i ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
    rw [h3]
    exact (le_iSup (fun s' => 𝔐.dR s' ⟨centre z, h⟩) lab) hmem
  exact (𝔐.M.exists_valAt_iff z (s i)).2 ⟨h, hlat⟩

end GlobalTheory.CompanionTheory.Ar.HodgeVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.ActFam

theorem comp_mul_hom {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    (u ≫ a) * (u ≫ b) = u ≫ (a * b) := by
  rw [Hom.mul_def, Hom.mul_def, comp_lift_assoc]

theorem exists_action_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  intro E _ _ _ H R _ t g n M ρ ψ e hρ
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ
  have hlift := fun c : 𝓞 E => exists_linear_lift_of_additive_family R t.G g n M (Metric.ball 0 ρ) ψ e g
    (Metric.ball 0 ρ) (fun b z => e.ex b z ≫ t.act.act c) Metric.isOpen_ball subset_rfl
    (fun b hb z w => by
      haveI := t.act.hom c
      simp only [e.add b hb z w]
      exact (IsMonHom.monoidHom (t.act.act c) _).map_mul _ _)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp e.hol (t.act.act c).left)
  choose h hd hs using hlift
  have hex : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ z, e.ex b (h c b z) = e.ex b z ≫ t.act.act c :=
    fun c b hb z => (hs c b hb).1 z
  have huq : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z, e.ex b (l z) = e.ex b z ≫ t.act.act c) → l = h c b :=
    fun c b hb l hl => (hs c b hb).2.1 l hl
  have hring : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ), ∀ c, f c = h c b := by
    intro b hb
    refine ⟨RingHom.mk' ⟨⟨fun c => h c b, ?_⟩, ?_⟩ ?_, fun c => rfl⟩
    · refine (huq 1 b hb LinearMap.id fun z => ?_).symm
      rw [t.act.one]
      exact (Category.comp_id _).symm
    · intro c c'
      refine (huq (c * c') b hb (h c b * h c' b) fun z => ?_).symm
      rw [Module.End.mul_apply, hex c b hb, hex c' b hb, mul_comm c c', t.act.mul, Category.assoc]
    · intro c c'
      refine (huq (c + c') b hb (h c b + h c' b) fun z => ?_).symm
      rw [LinearMap.add_apply, e.add b hb, hex c b hb, hex c' b hb, t.act.add, comp_mul_hom]
  have hall : ∀ b, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ),
      b ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ c, f c = h c b := by
    intro b
    by_cases hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ
    · obtain ⟨f, hf⟩ := hring b hb
      exact ⟨f, fun _ => hf⟩
    · obtain ⟨f, -⟩ := hring 0 h0
      exact ⟨f, fun hb' => absurd hb' hb⟩
  choose B hB using hall
  refine ⟨B, fun c x => ?_, fun b hb c x => ?_⟩
  · refine (hd c x).congr fun b hb => ?_
    simp only [hB b hb c]
  · rw [hB b hb c]
    exact hex c b hb x

end GlobalTheory.CompanionTheory.Ar.Flat.ActFam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_ringEquiv_of_genPt_eq {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (ξ' : Sp Ω' ⟶ X) (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom)
    (h' : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom) (he : genPt ξ = genPt ξ') :
    ∃ e : Ω ≃+* Ω', spMap e.toRingHom ≫ ξ = ξ' := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso (Scheme.stalkClosedPointTo ξ') := (ConcreteCategory.isIso_iff_bijective _).2 h'
  have hi : Inseparable (ξ (IsLocalRing.closedPoint Ω)) (ξ' (IsLocalRing.closedPoint Ω')) := .of_eq he
  let i : CommRingCat.of Ω ≅ CommRingCat.of Ω' :=
    (asIso (Scheme.stalkClosedPointTo ξ)).symm ≪≫ X.presheaf.stalkCongr hi ≪≫
      asIso (Scheme.stalkClosedPointTo ξ')
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  have e1 : Scheme.stalkClosedPointTo ξ ≫ i.hom =
      (X.presheaf.stalkCongr hi).hom ≫ Scheme.stalkClosedPointTo ξ' := by simp [i]
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have h3 : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk _ = X.fromSpecStalk _ :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.symm.specializes
  show Spec.map i.hom ≫ ξ = ξ'
  conv_lhs => rw [← h1]
  conv_rhs => rw [← h2]
  rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, h3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem bijective_stalk_of_cptOver {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (hβ : FracBase β) : Function.Bijective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hβ.1 hβ.2.2
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω))
  have hg := Z.gen.bij
  rw [Scheme.stalkClosedPointTo_comp] at hg
  exact (Function.Bijective.of_comp_iff _ hb).1 hg

theorem genPt_eq_of_cptOver {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Y : Model Xo c β} {Y' : Model Xo c β'} {U : Set (Xo.XF c)} (Z : CptOver Y U) (Z' : CptOver Y' U) :
    genPt Z.ξ₀ = genPt Z'.ξ₀ :=
  (((Z.closure _).1 Z'.genPt_mem).antisymm ((Z'.closure _).1 Z.genPt_mem)).eq

theorem cptOver_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c U hU
  refine ⟨Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) ⟨U, hU⟩,
    fun O _ β Y hβ => nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y U hU, ?_⟩
  intro O _ β Y O' _ β' Y' Z Z' hβ hβ' hg
  obtain ⟨e, he⟩ := exists_ringEquiv_of_genPt_eq Z.ξ₀ Z'.ξ₀ (bijective_stalk_of_cptOver Z hβ)
    (bijective_stalk_of_cptOver Z' hβ') (genPt_eq_of_cptOver Z Z')
  have h2 : spMap e.toRingHom ≫ spMap Z.inc = spMap Z'.inc := by
    rw [← Z.over_inc, ← Z'.over_inc, ← he, Category.assoc]
  have h4 : CommRingCat.ofHom Z.inc ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom Z'.inc :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  have h3 : e.toRingHom.comp Z.inc = Z'.inc := congrArg CommRingCat.Hom.hom h4
  rintro x ⟨f, hf, hx⟩
  have h5 : f.eval₂ Z.inc (e.symm x) = 0 := by
    apply e.injective
    have := Polynomial.hom_eval₂ f Z.inc e.toRingHom (e.symm x)
    rw [h3] at this
    simpa [hx] using this
  obtain ⟨a, ha⟩ := hg (e.symm x) ⟨f, hf, h5⟩
  refine ⟨a, ?_⟩
  rw [← h3]
  simp [ha]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

