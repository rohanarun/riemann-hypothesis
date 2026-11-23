module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0200
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem complex_uniformisation_holds : N1c := GlobalTheory.closing_of_abelianSchemeLaws

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqSingleOfIsUnitCoeff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusMono

open AddMonoidAlgebra (single)
open GlobalTheory.TorusUnit GlobalTheory.BiextTriv

theorem eq_single_of_isUnit_coeff {A X : Type} [CommRing A] [IsReduced A] [AddCommGroup X]
    [TwoUniqueSums X] {u : AddMonoidAlgebra A X} (hu : IsUnit u) {χ : X}
    (hχ : IsUnit (u.coeff χ)) : u = single χ (u.coeff χ) := by
  classical
  have key : ∀ z, z ≠ χ → u.coeff z = 0 := by
    intro z hz
    have hn : u.coeff z ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Ideal.mem_sInf.2 fun {p} hp => ?_
      have : p.IsPrime := hp
      obtain ⟨a, c, -, e⟩ := Semi.Rosenlicht.isUnit_eq_single
        (hu.map (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk p)))
      have ec : ∀ w, Ideal.Quotient.mk p (u.coeff w) = (single a c : AddMonoidAlgebra (A ⧸ p) X).coeff w := by
        intro w
        rw [← e, AddMonoidAlgebra.coeff_mapRingHom]
      have ha : a = χ := by
        by_contra hne
        have h1 := ec χ
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne] at h1
        exact (hχ.map (Ideal.Quotient.mk p)).ne_zero h1
      have h2 := ec z
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (ha.trans_ne hz.symm)] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    rw [nilradical_eq_zero] at hn
    exact hn
  ext z
  by_cases h : z = χ
  · subst h; simp
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, key z h, Ne.symm h]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def IsMonoNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ ∃ c : R, IsUnit c ∧ (expand y).hom ρ = single χ c

theorem IsMonoNear.residueField {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) : ∃ c : Y.left.residueField p, c ≠ 0 ∧
      (expand (Y.left.fromSpecResidueField p)).hom ρ = single χ c := by
  obtain ⟨R, y, hy, hp, c, hc, he⟩ := h
  have H : Set.range (Y.left.fromSpecResidueField p) ⊆ Set.range y := by
    rw [Scheme.range_fromSpecResidueField]; simpa using hp
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f ≫ y = Y.left.fromSpecResidueField p :=
    ⟨Spec.preimage (IsOpenImmersion.lift y _ H), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  refine ⟨f.hom c, (hc.map _).ne_zero, ?_⟩
  rw [← hf, expand_map, he]
  simp

theorem IsMonoNear.unique {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) (h' : IsMonoNear ρ χ' p) : χ = χ' := by
  classical
  obtain ⟨c, hc, e⟩ := h.residueField
  obtain ⟨c', -, e'⟩ := h'.residueField
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f χ) (e.symm.trans e')
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  exact hc this

theorem exists_isMonoNear [Module.Free ℤ X] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) (p : Y.left) : ∃ χ, IsMonoNear ρ.val χ p := by
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (ρ.isUnit.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ.val).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  have hopen : IsOpenImmersion (Spec.map g ≫ y) := inferInstance
  have hred : IsReduced (Spec (CommRingCat.of (Localization.Away a))) :=
    isReduced_of_isOpenImmersion (Spec.map g ≫ y)
  have hred' : _root_.IsReduced (Localization.Away a) :=
    (affine_isReduced_iff (CommRingCat.of (Localization.Away a))).1 hred
  have hcoeff : ((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ = algebraMap R (Localization.Away a) a := by
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hunit : IsUnit (((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ) := by
    rw [hcoeff]
    exact IsLocalization.Away.algebraMap_isUnit a
  refine ⟨χ, _, Spec.map g ≫ y, hopen, ?_, _, hunit,
    eq_single_of_isUnit_coeff (ρ.isUnit.map (expand _).hom) hunit⟩
  have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
    rw [this]; exact hχ
  refine ⟨r, ?_⟩
  rw [← hq, ← hr]
  exact Scheme.Hom.comp_apply _ _ _

theorem snd_expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    (snd (splitTorus S X) Y).left.appTop ≫ expand y =
      y.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ const X R := by
  rw [expand, value, ← Scheme.Hom.comp_appTop_assoc, prodPoint_snd, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]

theorem eq_char_mul [Module.Free ℤ X] [ConnectedSpace Y.left] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) :
    ∃ χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val *
      (snd (splitTorus S X) Y).left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) := by
  choose c hc using exists_isMonoNear (X := X) (Y := Y) ρ
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_⟩
  obtain ⟨R, y, hy, hp, d, -, he⟩ := hc p
  refine ⟨R, y, hy, hp, ?_⟩
  have e1 := congrArg (fun f => f.hom ρ.val) (expand_aug (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  rw [he, aug_single] at e1
  have e2 := congrArg (fun f => f.hom ((unitSec X Y).appTop.hom ρ.val)) (snd_expand (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [map_mul, e2, ← e1, expand_char, he, hlc.apply_eq_of_preconnectedSpace p p₀]
  simp [const, AddMonoidAlgebra.single_mul_single]

end GlobalTheory.CompanionTheory.TorusMono


open GlobalTheory.CompanionTheory.TorusMono GlobalTheory.BiextTriv in
theorem GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S) [ConnectedSpace Y.left] [IsReduced Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ), ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift t y).left.appTop.hom ρ.val = (chV t χ).val * (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
  intro S X _ _ Y _ _ ρ
  obtain ⟨χ, hχ⟩ := eq_char_mul ρ
  refine ⟨χ, fun Z t y => ?_⟩
  have c1 : ∀ v, (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom v) =
      t.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (fst (splitTorus S X) Y).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c2 : ∀ v, (lift t y).left.appTop.hom ((snd (splitTorus S X) Y).left.appTop.hom v) =
      y.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (snd (splitTorus S X) Y).left = y.left := by
      rw [← Over.comp_left, lift_snd]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c3 : y.left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) =
      (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
    rw [← comp_unitSec, Scheme.Hom.comp_appTop]
    rfl
  conv_lhs => rw [hχ]
  rw [map_mul, c1, c2, c3, chV_val]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeft
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter _root_.Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_fibreSlice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (B ×ˢ Set.univ) y)
    {b : V} (hb : b ∈ B) : IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨hb, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem tangent_of_isGrpPullback {tB : SAB H (Sp ℂ)} (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left)
    (hφ : IsGrpPullback A tB.G (𝟙 _) φ) (hP : IsPrincipal tB) {g : ℕ} (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hu : u.IsAH Hm χ) :
    IsAbelianScheme A ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := by
    have := hAb.comm
    have hc : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hφ.2 T x y (pushPt hφ.1.w x) (pushPt hφ.1.w y) rfl rfl,
        ← hφ.2 T y x (pushPt hφ.1.w y) (pushPt hφ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hφ.1 hAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hφ.1 hAb.geomConnected⟩
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hφ ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hφ fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hφ.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hφ tB.PP.isLB hL' hw hP.2.2 }
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hu
  exact ⟨hA, h₁, h₂⟩

theorem exists_isAbLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ hb hφ hu hP
  obtain ⟨hA, h₁, h₂⟩ := tangent_of_isGrpPullback A φ hφ hP u Hm χ hu
  obtain ⟨p, hp⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv P.m.cart (𝟙_ _) (s := spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨c, hc⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv hφ (𝟙_ _) (s := 𝟙 _) (Category.comp_id _).symm
  letI := P.τ.grpB
  haveI : IsMonHom P.τ.q := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let r : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) := fun y => p.symm (e.ex b y) ≫ P.τ.q ≫ P.e.hom
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun y => c.symm (r y)
  have hr : ∀ z w, r (z + w) = r z * r w := fun z w => by
    simp only [r, e.add b hb, map_mul, MonObj.mul_comp]
  have hG : ∀ z w, G (z + w) = G z * G w := fun z w => by
    simp only [G, hr, map_mul]
  have hGr : ∀ y, (G y).left ≫ φ = (r y).left := fun y => by
    rw [← hc, c.apply_symm_apply]
  have hs : IsHolTo Set.univ (fun y => (p.symm (e.ex b y)).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback P.m.cart.1 ?_ ?_
    · have h := isHolTo_fibreSlice e.hol hb
      have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.m.cm.F) = fun y => (e.ex b y).left :=
        funext fun y => by rw [← hp, p.apply_symm_apply]
      rw [e₁]
      exact h
    · have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.tK.G.hom) = fun _ => 𝟙 (Sp ℂ) :=
        funext fun y => Over.w (p.symm (e.ex b y))
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (G z).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback hφ.1 ?_ ?_
    · have h := GlobalTheory.CMSpreadCompare.isHolTo_postcomp hs (P.τ.q ≫ P.e.hom).left
      have e₁ : (fun y => (G y).left ≫ φ) = fun y => (p.symm (e.ex b y)).left ≫ (P.τ.q ≫ P.e.hom).left :=
        funext fun y => by rw [hGr]; rfl
      rw [e₁]
      exact h
    · have e₁ : (fun y => (G y).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun y => Over.w (G y)
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ g' g u h₁ h₂ G hG hol
  refine ⟨F, fun y s hs' => ?_⟩
  have es : s = p.symm (e.ex b y) := by
    rw [eq_comm, MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext ((hp s).trans hs').symm
  rw [hF, hGr, es]

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {g m : ℕ} {Y : Scheme.{0}}

theorem isDerivAt0_comp_linMap {e : (Fin m → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolTo Set.univ e)
    (D : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e (D w) v) : IsDerivAt0 (fun z => e (D z)) w v := by
  obtain ⟨h1, h2⟩ := hv
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact h1, fun U h f => ?_⟩
  rw [h2 U h f]
  obtain ⟨hopen, hdiff⟩ := hol U f
  have h0mem : (0 : Fin m → ℂ) ∈ {b | b ∈ Set.univ ∧ ⊤ ≤ (TopologicalSpace.Opens.map (e b).base).obj U} := by
    refine ⟨Set.mem_univ _, ?_⟩
    have hv' : (TopologicalSpace.Opens.map v.base).obj U = ⊤ := top_le_iff.1 h
    rw [← h1]
    simp [hv']
  have hφ : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact (hdiff 0 h0mem).differentiableAt (hopen.mem_nhds h0mem)
  have hDd : DifferentiableAt ℂ (⇑(LinearMap.toContinuousLinearMap D)) 0 :=
    (LinearMap.toContinuousLinearMap D).differentiableAt
  have hc := fderiv_comp (0 : Fin g → ℂ) hφ hDd
  have hDf : fderiv ℂ (⇑D) 0 = LinearMap.toContinuousLinearMap D :=
    (LinearMap.toContinuousLinearMap D).fderiv
  rw [show (fun z => valAt' (e (D z)) U f) = (fun z => valAt' (e z) U f) ∘ ⇑D from rfl, hc, hDf]
  simp

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem ex_zero_left (u : HolUnif A L g) : (u.ex 0).left = η[A].left := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  have h1 : u.ex 0 = 1 := by simpa using h
  rw [h1, Hom.one_def]
  simp

theorem isHolTo_ex (u : HolUnif A L g) : IsHolTo Set.univ (fun z => (u.ex z).left) := by
  intro U f
  simpa using u.hol U f

theorem isDerivAt0_of_isDiff (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (ht : IsTangent v)
    (hd : u.IsDiff w v) : IsDerivAt0 (fun z => (u.ex z).left) w v.left := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff at hd
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent at ht
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  exact ⟨ht.trans (ex_zero_left u).symm, hd⟩

theorem isDerivAt0_of_fibre {Q : Out.PolAV (Sp ℂ)} {X : Scheme.{0}} (ψ : Q.A.left ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (u : HolUnif Q.A Q.L Q.g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hF : ∀ z, (u.ex (F z)).left ≫ ψ = e z)
    {w : Fin g → ℂ} {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u.IsDiff (F w) t) :
    IsDerivAt0 e w (t.left ≫ ψ) := by
  have h4 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u ht hd)
  have he : e = fun z => (u.ex (F z)).left ≫ ψ := funext fun z => (hF z).symm
  subst he
  obtain ⟨h41, h42⟩ := h4
  have hval : ∀ (y : Sp ℂ ⟶ Q.A.left) (U : X.Opens) (f : ↑(X.presheaf.obj (Opposite.op U))),
      valAt' (y ≫ ψ) U f = valAt' y (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
    intro y U f
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    by_cases hy : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj (ψ ⁻¹ᵁ U)
    · rw [dite_eq_left hy, dite_eq_left (show ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
      simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    · rw [dite_eq_right hy, dite_eq_right (show ¬ ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by rw [← Category.assoc, h41], fun U h f => ?_⟩
  have h' : ⊤ ≤ (TopologicalSpace.Opens.map t.left.base).obj (ψ ⁻¹ᵁ U) := h
  simp only [hval]
  rw [← h42 (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom f)]
  simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem isDiff_map {Q : Out.PolAV (Sp ℂ)} (u u' : HolUnif Q.A Q.L Q.g) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hG : ∀ z, u.ex (G z) = u'.ex z) {w : Fin Q.g → ℂ}
    {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u'.IsDiff w t) : u.IsDiff (G w) t := by
  have h4 := isDerivAt0_of_isDiff u' ht hd
  simp_rw [← hG] at h4
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_ex u) (G w)
  have h1 := isDerivAt0_comp_linMap (isHolTo_ex u) G hv₀
  have heq := GlobalTheory.VerticalDeriv.isDerivAt0_unique h1 h4
  rw [heq] at hv₀
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff
  exact hv₀.2

end GlobalTheory.CompanionTheory.Ar.Flat.PerGram

namespace GlobalTheory.CompanionTheory.Ar.Flat


open PerGram in
theorem hodgeGram_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = (FU.Di i).EF x y) → ∀ (y : Sp ℂ ⟶ Xo.X), y = FU.u i P → ∀ (m : ℕ) (v : Fin m → (epsAt y ⟶ Xo.univ.t.G)) (W : Fin m → Fin g → ℂ) (Γ : Matrix (Fin m) (Fin m) ℂ), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (W a) (v a).left) → (IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L y v Γ ↔ ∀ a b, Γ a b = Real.pi * hermForm Hm (W a) (W b)) := by
  intro E _ _ _ H D l Xo σ g ty FU i P Hm hP _ hIm y hy m v W Γ hd
  subst hy
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback Q.A Xo.univ.t.G (FU.u i P) ψ → LBIso Q.L (Xo.univ.t.PP.L.pull ψ) →
      ∃ (u : HolUnif Q.A Q.L Q.g) (H₂ : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ)
        (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)), u.IsAH H₂ χ ∧ (∀ t, IsTangent t → ∃! w, u.IsDiff w t) ∧
        (∀ w, ∃! t, IsTangent t ∧ u.IsDiff w t) ∧ (∀ z w, hermForm H₂ (F z) (F w) = hermForm Hm z w) ∧
        ∀ a, ∃ t : epsR ℂ ⟶ Q.A, IsTangent t ∧ u.IsDiff (F (W a)) t ∧ t.left ≫ ψ = (v a).left := by
    intro Q ψ hQ hQL
    obtain ⟨u, H₂, χ, F, hAH, d₁, d₂, -, hF, -, hE⟩ :=
      GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
        Q ψ hQ hQL
    refine ⟨u, H₂, χ, F, hAH, d₁, d₂, fun z w => ?_, fun a => ?_⟩
    · refine GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap Hm LinearMap.id hP.2.2.2.1 ?_ z w
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hE a b).trans (hIm a b).symm
    · obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (W a))
      exact ⟨t, h₁, h₂, GlobalTheory.VerticalDeriv.isDerivAt0_unique
        (isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) (hd a)⟩
  unfold IsHodgeGram
  constructor
  · rintro ⟨Q, ψ, v', u', Hm', χ', W', hQ, hQL, hAH, hv, hΓ⟩ a b
    obtain ⟨u, H₂, χ, F, hAH₂, d₁, d₂, hH, ht⟩ := key Q ψ hQ hQL.symm
    obtain ⟨G, hG, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo Q.A Q.isAb Q.L Q.g Q.g u d₁ d₂ u'.ex u'.ex_add
      (isHolTo_ex u')
    have hW : ∀ c, G (W' c) = F (W c) := fun c => by
      obtain ⟨t, h₁, h₂, h₃⟩ := ht c
      have e : v' c = t := Over.OverMorphism.ext
        (hQ.1.hom_ext ((hv c).1.trans h₃.symm) (by rw [Over.w, Over.w]))
      have h₄ : u'.IsDiff (W' c) t := e ▸ (hv c).2
      exact (d₁ t h₁).unique (isDiff_map u u' d₂ G hG h₁ h₄) h₂
    rw [hΓ, ← GlobalTheory.UnifCompare.hermForm_eq Q.isLB u' u hAH hAH₂ G hG, hW, hW, hH]
  · intro hΓ
    obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
      Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
    obtain ⟨u, H₂, χ, F, hAH₂, -, -, hH, ht⟩ := key Q ψ hQ hQL
    choose t h₁ h₂ h₃ using ht
    exact ⟨Q, ψ, t, u, H₂, χ, fun a => F (W a), hQ, hQL.symm, hAH₂, fun a => ⟨h₃ a, h₂ a⟩,
      fun a b => by rw [hΓ, hH]⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointHTOfFarguesHodgeTateStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointHT_of_fargues_hodge_tate : FarguesHodgeTate → PointHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | exact GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.Fargues.pointHT <;> assumption)
end

