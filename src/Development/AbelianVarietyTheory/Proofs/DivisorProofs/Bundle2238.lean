module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverLiftThroughNormal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCoverFin

theorem isDominant_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : IsDominant V.j := by
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  refine ⟨?_⟩
  obtain ⟨x⟩ : Nonempty V.G := inferInstance
  have h0 : genericPoint V.X ∈ Set.range V.j :=
    (Flat.generalizingMap V.j).stableUnderGeneralization_range (genericPoint_specializes (V.j x)) ⟨x, rfl⟩
  have h2 : closure ({genericPoint V.X} : Set V.X) ⊆ closure (Set.range V.j) :=
    closure_mono (Set.singleton_subset_iff.2 h0)
  rw [show closure ({genericPoint V.X} : Set V.X) = Set.univ from genericPoint_spec V.X] at h2
  exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)

theorem exists_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V V₂ : Mean4O.Cover Y) (G : Scheme.{0})
    [IsIntegral G] [GlobalTheory.IsNormalScheme G] (g : G ⟶ V.G) [IsFinite g] [IsDominant g] (k : G ⟶ V₂.G),
    k ≫ V₂.π = g ≫ V.π →
    ∃ (W : Mean4O.Cover Y) (a : W.X ⟶ V.X) (k' : W.G ⟶ V₂.G), a ≫ V.p = W.p ∧ Lies W V a ∧ k' ≫ V₂.π = W.π := by
  intro F _ _ Y V V₂ G _ _ g _ _ k hk
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : IsAffineHom V.j := MorphismProperty.of_isPullback V.pb.flip (isAffineHom_of_isAffine _)
  have : IsDominant V.j := isDominant_j V
  let h : G ⟶ V.X := g ≫ V.j
  have hh : h = g ≫ 𝟙 _ ≫ V.j := by simp [h]
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) V.pb g (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have w : h ≫ V.p = (g ≫ V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [h, Category.assoc, V.pb.w]
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h V.p F (g ≫ V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : IsDominant h.fromNormalization := by
    have : IsDominant (h.toNormalization ≫ h.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp h.toNormalization h.fromNormalization
  have hs : Surjective h.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ h.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    rw [← V.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos h.fromNormalization
      (apply_genericPoint_of_isDominant h.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap h.fromNormalization.isClosedMap hs.surj)
    let := (h.fromNormalization.residueFieldMap (genericPoint h.normalization)).hom.toAlgebra
    have : Module.Finite (V.X.residueField (h.fromNormalization (genericPoint h.normalization)))
        (h.normalization.residueField (genericPoint h.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite h.fromNormalization _
    exact Module.finrank_pos
  have hfl : Flat (h.fromNormalization ≫ V.p) :=
    GlobalTheory.flat_fromNormalization_comp h F V.p (g ≫ V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : Surjective g := surjective_of_isDominant_of_isClosed_range _ g.isClosedMap.isClosed_range
  have hη : (g ≫ V.π) (genericPoint G) ⤳ genericPoint Y.X :=
    specializes_of_eq (apply_genericPoint_of_isDominant (g ≫ V.π))
  let W : Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin V.ar.isProjOver,
        inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := G
      j := h.toNormalization
      π := g ≫ V.π
      pb := by simpa [Category.assoc] using hpb.paste_vert V.pb
      φ := SmallSec.fnMap (g ≫ V.π) hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ (g ≫ V.π).stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨W, h.fromNormalization, k, rfl, ⟨g, by simp [W, h], rfl⟩, hk⟩

end GlobalTheory.Mean4O.NormCoverFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNaturaStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.crystallineCocycleCotangentValue_baseChange_natural
    (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R')
    (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ)
    (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D']
    (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D')
    (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (ha : ∀ r : D, (a.φ r : D') = s r) :
    cotVal (m.coef.pullbackOneCocycle f) y' =
      (SemiBialgHom.cot s) (cotVal f y) + dUnit (R := R') (A := D') (ev f a) :=
  cotVal_pull R R' σ X X' φ m D D' s y y' a f ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.PtExt.fv_linear (R : Type) [CommRing R] (X : Over (Sp R)) :
    (∀ (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (f + f') = (fv f).add (fv f')) ∧
    (∀ (r : R) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
      (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
      (φ : D →ₐ[R] D') (x : Pt X D),
      fv (r • f) D D' φ x = algebraMap R D' r * fv f D D' φ x) ∧
    (∀ g : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)),
      ∃ k : Fn0 X, IsCob (whole X) (fv ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩) k) := by
  refine ⟨fun f f' ↦ rfl, ?_, fun g ↦ ⟨fun D _ _ x ↦ g (trivAt x), ?_⟩⟩
  · intro r f D _ _ D' _ _ φ x
    exact Algebra.smul_def r (ev f (trivMap φ x))
  · intro D _ _ D' _ _ φ x _
    rfl

alias GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear := GlobalTheory.PtExt.fv_linear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullback
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem ev_triv_congr {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 (O (dp0 R) s))
    {D D' : Type} [CommRing D] [CommRing D'] (i j : Algebra R D) (i' j' : Algebra R D') (hi : i = j) (hi' : i' = j')
    (x : Sp D ⟶ X) (x₁ x₂ : Sp D' ⟶ X) (hx₁ : x₁ = x₂)
    (hx : x ≫ s = spMap (@algebraMap R D _ _ i)) (hxj : x ≫ s = spMap (@algebraMap R D _ _ j))
    (hx' : x₁ ≫ s = spMap (@algebraMap R D' _ _ i')) (hxj' : x₂ ≫ s = spMap (@algebraMap R D' _ _ j'))
    (a : @Thick.triv R _ X s D _ i x hx ⟶ @Thick.triv R _ X s D' _ i' x₁ hx')
    (b : @Thick.triv R _ X s D _ j x hxj ⟶ @Thick.triv R _ X s D' _ j' x₂ hxj')
    (h : ∀ r, a.φ r = b.φ r) : ev f a = ev f b := by
  subst hi hi' hx₁
  have : a = b := Thick.Hom.ext' (AlgHom.ext h)
  subst this
  rfl

theorem ev_functor_map_trivMap {R : Type} [CommRing R] {X Y : Over (Sp R)} (q : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [j : Algebra R D] (D' : Type) [CommRing D']
    [j' : Algebra R D'] (φ : D →ₐ[R] D') (y : Pt Y D) :
    ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q)) := by
  let y' : Pt Y D' := spOver φ ≫ y
  have h : (y' ≫ q).left = (spOver φ ≫ y ≫ q).left :=
    congrArg (fun p : Pt X D' ↦ p.left) (Category.assoc (spOver φ) y q)
  exact ev_triv_congr f (((algebraMap R D).comp (RingHom.id R)).toAlgebra) j
    (((algebraMap R D').comp (RingHom.id R)).toAlgebra) j' (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) (y ≫ q).left (y' ≫ q).left
    (spOver φ ≫ y ≫ q).left h (m.obj (trivAt y)).w (Pt.w (y ≫ q))
    (m.obj (trivAt y')).w (Pt.w (spOver φ ≫ y ≫ q))
    (m.functor.map (trivMap φ y)) (trivMap φ (y ≫ q)) fun _ ↦ rfl

theorem fv_pullbackOneCocycle_eq_pull : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  intro R _ X Y q m f
  funext D _ _ D' _ _ φ y
  change ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q))
  exact ev_functor_map_trivMap q m f D D' φ y

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackCh
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem fv_pullbackOneCocycle_eq_bcPull_of_changeOfBase : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ q) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = bcPull w (fv f) := by
  intro R R' _ _ σ X X' q w m f
  unfold fv bcPull
  rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairs
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm.AffPair

section

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def smAff : ObjectProperty (IsSm κ t i).FullSubcategory := fun S ↦ IsAffineOpen S.obj.U

theorem smAff_up (S S' : (IsSm κ t i).FullSubcategory) (f : S ⟶ S') (h : smAff κ t i S) :
    smAff κ t i S' := by
  rcases S'.obj.hU with h' | h'
  · exact h'
  · have e : S'.obj.U = S.obj.U := le_antisymm f.hom.2 (h' ▸ le_top)
    change IsAffineOpen S'.obj.U
    rw [e]
    exact h

abbrev coefSm : (IsSm κ t i).FullSubcategory ⥤ CommAlgCat.{0} R := (IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t

def toIter : EE κ t i ⥤ (smAff κ t i).FullSubcategory where
  obj a := ⟨⟨a.obj, ⟨⟨a.obj.U, a.property⟩, a.obj.mem⟩⟩, a.property⟩
  map f := ⟨⟨f.hom⟩⟩

def ofIter : (smAff κ t i).FullSubcategory ⥤ EE κ t i where
  obj a := ⟨a.obj.obj, a.property⟩
  map f := ⟨f.hom.hom⟩

def mapTo : CoefMap (RingHom.id R) ((smAff κ t i).ι ⋙ coefSm κ t i) (pE κ t i ⋙ O κ t) where
  G := toIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def mapOf : CoefMap (RingHom.id R) (pE κ t i ⋙ O κ t) ((smAff κ t i).ι ⋙ coefSm κ t i) where
  G := ofIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem mapTo_pull1 : Function.Bijective (mapTo κ t i).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl

theorem mapTo_pull2 : Function.Bijective (mapTo κ t i).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl

end

end GlobalTheory.PDForm.AffPair

namespace GlobalTheory.PDForm


open AffPair in
theorem crystallineCohomology_computed_on_affinePairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i hY
  have ha := _root_.GlobalTheory.PDForm.pull_isSm_bijective R I κ X t Y i
  have hc := _root_.GlobalTheory.PDForm.isSm_acyclic_two.1 R I κ X t Y i hY
  have hc2 := _root_.GlobalTheory.PDForm.isSm_acyclic_two.2 R I κ X t Y i hY
  have h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 :=
    Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2
  have h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 :=
    ⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2,
    Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩
  refine _root_.GlobalTheory.CxCoh.single_algebra_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_
  · have h := (mapTo_pull1 κ t i).comp (h1.comp ha.1)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 := by
      funext c
      obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [e]
    exact h
  · have h := (mapTo_pull2 κ t i).comp (h2.comp ha.2)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
      funext c
      obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
    rw [e]
    exact h

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeBundleOfTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.LamTransl
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem foldr_eq {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (l : List (Fin n)) :
    l.foldr (fun k acc => padd G (x k) acc) (pzero G T) = (l.map x).prod := by
  induction l with
  | nil => simp [pzero, Hom.one_def]
  | cons k l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, padd, Hom.mul_def]

def split3 (I : Finset (Fin 3)) : Finset (Fin 2) ⊕ Finset (Fin 2) :=
  if (2 : Fin 3) ∈ I then Sum.inl (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)
  else Sum.inr (Finset.univ.filter fun i : Fin 2 => Fin.castSucc i ∈ I)

theorem split3_bij : Function.Bijective split3 := by decide

def splitEquiv : thK ≃ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) :=
  Equiv.ulift.trans ((Equiv.ofBijective _ split3_bij).trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

theorem mem8 : ∀ I : Finset (Fin 3),
    I ∈ ({∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, {0,1,2}} : Finset (Finset (Fin 3))) := by decide

variable (a : 𝟙_ (Over S) ⟶ G)

def tr : G ⟶ G := (toUnit G ≫ a) * 𝟙 G

def pt3 : G2 G ⟶ G3 G := lift (fst G G) (lift (snd G G) (toUnit (G2 G) ≫ a))
def φA : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down ≫ tr G a).left
def φB : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left
def ε2 : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem splitEquiv_apply (I : Finset (Fin 3)) : splitEquiv ⟨I⟩ = Sum.map ULift.up ULift.up (split3 I) := by
  rfl

theorem split_eq (k : thK) : Sum.elim (φA G a) (φB G) (splitEquiv k) = (pt3 G a).left ≫ thφ G (x3 G) k ∧
    Sum.elim ε2 (fun k => -ε2 k) (splitEquiv k) = thε k := by
  rcases k with ⟨I⟩
  rw [splitEquiv_apply]
  have h := mem8 I
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (config := {decide := true}) only [split3, if_true, if_false, Finset.mem_insert, Finset.mem_singleton,
      Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  all_goals
    refine ⟨?_, trivial⟩
    simp only [φA, φB, thφ]
    rw [← Over.comp_left]
    congr 1
    rw [psum, foldr_eq, psum, foldr_eq]
    simp [List.finRange_succ, x2, x3, pt3, tr, MonObj.comp_mul]
  all_goals ac_rfl

theorem sameSum : LB.SameSum (fun k => (pt3 G a).left ≫ thφ G (x3 G) k) thε (Sum.elim (φA G a) (φB G))
    (Sum.elim ε2 fun k => -ε2 k) := by
  classical
  intro ψ
  rw [← Equiv.sum_comp splitEquiv]
  exact Finset.sum_congr rfl fun k _ => by rw [(split_eq G a k).1, (split_eq G a k).2]

end GlobalTheory.Mum.LamTransl

namespace GlobalTheory.Mum


open LamTransl in
theorem lam_transl_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), CubicalStr G L →
    ∀ (a : 𝟙_ (Over S) ⟶ G) (N : LB G.left), N.IsLB → LBIso N (L.L.pull ((toUnit G ≫ a) * 𝟙 G).left) →
      LBIso (abelian₂ G N) (abelian₂ G L.L) := by
  intro S G _ _ L c a N hN hNL
  have hT : (L.L.pull (tr G a).left).IsLB := pull_isLB L.isLB _
  have hA : (LB.LinComb L.L (φA G a) ε2).IsLB := DVR.linComb_isLB _ L.isLB _ _
  have hLam := GlobalTheory.SabBaseChange.cube_isLB (x2 G) L.isLB
  have h1 : LBIso (abelian₂ G N) (abelian₂ G (L.L.pull (tr G a).left)) := GlobalTheory.SabBaseChange.lbIso_cube (x2 G) hNL
  have h2 : LBIso (abelian₂ G (L.L.pull (tr G a).left)) (LB.LinComb L.L (φA G a) ε2) :=
    LBIso.chartPull (chartPullLinComb L.L (tr G a).left _ (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (chartPullSame L.L (φA G a) (φA G a) ε2 (𝟙 _) fun k => (Category.id_comp _).symm)
      (GlobalTheory.PolBaseChange.lbIso_refl hA)
  have h3 : LBIso (abelian₂ G L.L) (LB.LinComb L.L (φA G a) ε2) := by
    refine (GlobalTheory.TripleCompare.lbIso_iff_gen (L := L.L) (φB G) ε2 (φA G a) ε2).2 ?_
    obtain ⟨t', ht', -⟩ := DVR.gen_transport L.isLB (sameSum G a)
      _ (DVR.pullGen_isGen L.L _ _ c.t c.isGen (pt3 G a).left)
    exact ⟨t', ht'⟩
  exact LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hN) (GlobalTheory.SabBaseChange.cube_isLB _ hT) hLam h1
    (LBIso.trans (GlobalTheory.SabBaseChange.cube_isLB _ hT) hA hLam h2 (LBIso.symm h3))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpsilonPartDeformationFormClassEqCoboundaryOfLifStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K)))) (ω : Form (A.hom ≫ 𝟙 (Sp K))) (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))), (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') = (constMor A).isMor.pull1 (Form.cl _ ω) + (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b) → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (P Q : GPt A) (φ : P.Hom Q) (y : Sp (DualNumber P.B) ⟶ A'.left) (y' : Sp (DualNumber Q.B) ⟶ A'.left) (hy : IsLift i P y) (hy' : IsLift i Q y'), spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ y = y' → ev b φ.triv = ((liftVal h ω'.1 hy').snd + G Q) - φ.ρ ((liftVal h ω'.1 hy).snd + G P) := by
  first | exact @GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | exact GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary | (intros; apply GlobalTheory.CechKS.LiftTriv.eps_part_eq_coboundary <;> assumption)
end

