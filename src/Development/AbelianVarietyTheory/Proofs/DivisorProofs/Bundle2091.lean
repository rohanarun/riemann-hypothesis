module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

variable (p : ℕ) [Fact p.Prime]

abbrev frobR (R : Type) [CommRing R] (hR : (p : R) = 0) : R →+* R :=
  GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR

theorem frobR_apply (R : Type) [CommRing R] (hR : (p : R) = 0) (x : R) : frobR p R hR x = x ^ p :=
  congrArg (x ^ ·) (pow_one p)

theorem frob_sp (R : Type) [CommRing R] (hR : (p : R) = 0) (h : (p : Γ(Sp R, ⊤)) = 0) :
    GlobalTheory.VB.frob (Sp R) p h = spMap (frobR p R hR) :=
  GlobalTheory.SS.FrobField.absFrob_spec R p 1 Fact.out h _ fun _ ↦ rfl

theorem frob_comp_hom (R : Type) [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}} (f : X ⟶ Sp R)
    (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ f = f ≫ spMap (frobR p R hR) := by
  have h0 : (p : Γ(Sp R, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp R hR
  have hn : GlobalTheory.VB.frob X p h ≫ f = f ≫ GlobalTheory.VB.frob (Sp R) p h0 :=
    GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out h h0
  rw [hn, frob_sp p R hR h0]

theorem cast_left (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) :
    (p : Γ(A.left, ⊤)) = 0 :=
  GlobalTheory.SS.FrobField.cast_zero_of_hom A.hom (GlobalTheory.SS.FrobField.cast_zero_sp R hR)

theorem frobMor (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (h : (p : Γ(A.left, ⊤)) = 0) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p h) := by
  refine { dp := isDPMorphism_of_eq_bot _ rfl _ _, base := ?_,
           w := frob_comp_hom p R hR A.hom h, mul := ?_ }
  · simp
  · intro T x y x₀ y₀ hx hy
    have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
    have hn (f : T.left ⟶ A.left) :
        GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p h :=
      GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT h
    let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
      Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
    have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
      simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
    have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
      simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
    subst ex ey
    rw [← MonObj.comp_mul]
    simp only [Over.comp_left, Over.homMk_left, j]
    exact hn (x * y).left

def frobDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    primDR A →ₛₗ[frobR p R hR] primDR A :=
  (frobMor p R hR A (cast_left p R hR A)).pull

def conjDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    Submodule R (primDR A) :=
  Submodule.span R (Set.range (frobDR p R hR A))

end GlobalTheory.ConjSeq

namespace GlobalTheory.DeRhamSheaf

open _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

end GlobalTheory.DeRhamSheaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem mul_eq_zero_of_mem_map_sq {R : Type} [CommRing R] {I : Ideal R} (hI : I ^ 2 = 0) {B' : Type} [CommRing B']
    [Algebra R B'] {x y : B'} (hx : x ∈ I.map (algebraMap R B')) (hy : y ∈ I.map (algebraMap R B')) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← sq, map_sq hI B', Ideal.zero_eq_bot, Ideal.mem_bot] at h
  exact h

theorem isTheta_mul_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {B B₀ B' : Type}
    [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] [CommRing B'] [Algebra R B'] {p : B →+* B₀}
    {a b : B →ₐ[R] B'} {θ : Ω[B₀⁄R₀] →+ B'} (h : IsTheta I p a b θ) (x : B) {t : B'}
    (ht : t ∈ I.map (algebraMap R B')) : a x * t = b x * t := by
  have hd : (a x - b x) * t = 0 := by
    rw [← h.der x]; exact mul_eq_zero_of_mem_map_sq hI (h.mem _) ht
  rw [sub_mul, sub_eq_zero] at hd
  exact hd

theorem isTheta_add : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' : Type) [CommRing B'] [Algebra R B'] (a b c : B →ₐ[R] B') (θ θ' : Ω[B₀⁄R₀] →+ B'), IsTheta I p a b θ → (IsTheta I p b a (-θ) ∧ (IsTheta I p b c θ' → IsTheta I p a c (θ + θ')) ∧ (IsTheta I p a b θ' → θ = θ') ∧ (θ = 0 → a = b)) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' _ _ a b c θ θ' h
  refine ⟨⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h' ↦ ?_,
    fun h0 ↦ ?_⟩
  · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, h.smul, mul_neg, isTheta_mul_eq hI h x (h.mem w)]
  · rw [AddMonoidHom.neg_apply, h.der, neg_sub]
  · exact (Ideal.neg_mem_iff _).2 (h.mem w)
  · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, h.smul, h'.smul, mul_add,
      isTheta_mul_eq hI h x (h'.mem w)]
  · rw [AddMonoidHom.add_apply, h.der, h'.der]; ring
  · exact Ideal.add_mem _ (h.mem w) (h'.mem w)
  · ext w
    have hw : w ∈ Submodule.span B₀ (Set.range (KaehlerDifferential.D R₀ B₀)) := by
      rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, rfl⟩ := hy
      obtain ⟨x, rfl⟩ := hp y
      rw [h.der, h'.der]
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
    | smul r u _ hu =>
      obtain ⟨x, rfl⟩ := hp r
      rw [h.smul, h'.smul, hu]
  · ext x
    have := h.der x
    rw [h0, AddMonoidHom.zero_apply] at this
    exact (sub_eq_zero.1 this.symm)

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsComp
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Obs.isTheta_comp : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (E E' : Type) [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E'] (a b : B →ₐ[R] E) (θ : Ω[B₀⁄R₀] →+ E), IsTheta I p a b θ → (∀ g : E →ₐ[R] E', IsTheta I p (g.comp a) (g.comp b) ((g : E →+* E').toAddMonoidHom.comp θ)) ∧ ∀ (h : B' →ₐ[R] B) (h₀ : B₀' →ₐ[R₀] B₀), (∀ x, p (h x) = h₀ (p' x)) → IsTheta I p' (a.comp h) (b.comp h) (θ.comp (SemiHom.of_algHom h₀).m1.toAddMonoidHom) := by
  intro R R₀ _ _ I hI π hπ hk B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' E E' _ _ _ _ a b θ hθ
  refine ⟨fun g ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩, fun h h₀ hh ↦ ⟨fun x w ↦ ?_, fun x ↦ ?_, fun w ↦ ?_⟩⟩
  · change g (θ (p x • w)) = g (a x) * g (θ w)
    rw [hθ.smul, map_mul]
  · change g (θ (KaehlerDifferential.D R₀ B₀ (p x))) = g (a x) - g (b x)
    rw [hθ.der, map_sub]
  · have h1 := Ideal.mem_map_of_mem (g : E →+* E') (hθ.mem w)
    rw [Ideal.map_map, g.comp_algebraMap] at h1
    simpa using h1
  · change θ ((SemiHom.of_algHom h₀).m1 (p' x • w)) = a (h x) * θ ((SemiHom.of_algHom h₀).m1 w)
    rw [SemiHom.oneFormMap_smul_semilinear]
    change θ (h₀ (p' x) • _) = _
    rw [← hh, hθ.smul]
  · change θ ((SemiHom.of_algHom h₀).m1 (KaehlerDifferential.D R₀ B₀' (p' x))) = a (h x) - b (h x)
    rw [SemiHom.m1_D]
    change θ (KaehlerDifferential.D R₀ B₀ (h₀ (p' x))) = _
    rw [← hh, hθ.der]
  · exact hθ.mem _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainSectionsQuotMaximalIdealSmoothConnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem abLawCst_eq_smallExtLiftCst {X : Scheme} {R : Type} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    GlobalTheory.AbLaw.cst f U = GlobalTheory.SmallExtLift.cst f U := by
  ext r
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.SmallExtLift.cst, GlobalTheory.AbLaw.rs, Scheme.Hom.appLE,
    CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop]
  rfl

theorem isDomain_quot_maximalIdeal_of_smooth :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)), Smooth G.hom →
      GeometricallyConnected G.hom → ∀ (U : G.left.Opens), IsAffineOpen U → ∀ y ∈ U,
        G.hom y = closedPoint R →
          IsDomain (Γ(G.left, U) ⧸ (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U)) := by
  intro R _ _ G hsm hgc U hU y hyU hy
  haveI := hsm
  haveI := hgc
  let f : G.left ⟶ Spec (CommRingCat.of R) := G.hom
  let g : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (residue R))
  haveI hI : IsIntegral (pullback f g) := GlobalTheory.isIntegral_specialFibre_of_smooth f
  let q := pullback.fst f g
  have H : IsPullback q (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hsurj : Function.Surjective (q.app U).hom :=
    GlobalTheory.SmallExtLift.app_surj (residue_surjective) H hU
  have hker : RingHom.ker (q.app U).hom = (maximalIdeal R).map (GlobalTheory.AbLaw.cst G.hom U) := by
    rw [abLawCst_eq_smallExtLiftCst]
    apply le_antisymm
    · intro a ha
      have := GlobalTheory.SmallExtLift.mem_of_app_eq_zero (residue_surjective) H hU a ha
      rwa [ker_residue] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, GlobalTheory.SmallExtLift.app_cst H.w,
        (residue_eq_zero_iff r).2 hr, map_zero]
  have hne : Nonempty (q ⁻¹ᵁ U) := by
    have hpt : f y = g (closedPoint (ResidueField R)) := by
      rw [show f y = G.hom y from rfl, hy]
      exact (IsLocalRing.comap_closedPoint (residue R)).symm
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hpt
    exact ⟨⟨z, show q z ∈ U from hz ▸ hyU⟩⟩
  haveI : IsDomain Γ(pullback f g, q ⁻¹ᵁ U) := inferInstance
  rw [← hker]
  exact (RingHom.quotientKerEquivOfSurjective hsurj).toMulEquiv.isDomain

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectDual

theorem mono_of_isPerfect {S : Scheme.{0}} {A B B' : Over S} [GrpObj A] [GrpObj B] [GrpObj B']
    {P : LB (A ⊗ B).left} {P' : LB (A ⊗ B').left} (h : IsDual A B' P') (hP : IsPerfect A B P) (x : B ⟶ B')
    [IsMonHom x] (hx : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : Mono x := by
  have h' : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB h.isLB _
  have hc : cls P hP.isLB = cls _ h' := (cls_eq_iff hP.isLB h').2 hx
  have key : ∀ {Y : Over S} (a : Y ⟶ A) (t : Y ⟶ B), evc hP.isLB a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    show CechPic.pull (lift a t).left (cls P hP.isLB) = _
    rw [hc, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  refine ⟨fun {T} u v huv ↦ ?_⟩
  have hw : (u * v⁻¹) ≫ x = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
  have t := hP.ker_right T (u * v⁻¹) ((triv_ev_iff hP.isLB _ _).2 (by
    rw [key, Category.assoc, hw, MonObj.comp_one, evc_one_right h.isLB h.zero]))
  rwa [mul_inv_eq_one] at t

theorem isIso_of_isEmpty {S : Scheme.{0}} (hS : IsEmpty S) {X Y : Over S} (f : X ⟶ Y) : IsIso f := by
  haveI : IsEmpty X.left := ⟨fun p ↦ hS.false (X.hom p)⟩
  haveI : IsEmpty Y.left := ⟨fun p ↦ hS.false (Y.hom p)⟩
  haveI : IsIso f.left := ⟨⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩⟩
  haveI : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)

theorem isDual_of_isPerfect_of_additive (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) (haddA : IsAdditive P) (haddB : IsAdditive (swap P)) :
    IsDual A B P := by
  obtain ⟨B', _, P', hB', hd', h1, h2⟩ := hD S A hA
  obtain ⟨A'', _, Q, hA'', hdQ, k1, k2⟩ := hD S B hB
  obtain ⟨x, hx, -⟩ := h1.univ B P hP.isLB haddA
  have hs : (swap P).IsLB := pull_isLB hP.isLB _
  obtain ⟨y, hy, -⟩ := k1.univ A (swap P) hs haddB
  have hmx : IsMonHom x := GlobalTheory.AbDual.isMonHom_of_classifying S A B B' P P' h1 h2.additive hP.isLB haddB x hx
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  have haddSS : IsAdditive (swap (swap P)) := (isAdditive_iff hss).2 fun Y a a' t ↦ by
    rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP.isLB hs, evc_swap hP.isLB hs,
      evc_swap hP.isLB hs]
    exact (isAdditive_iff hP.isLB).1 haddA Y a a' t
  have hmy : IsMonHom y := GlobalTheory.AbDual.isMonHom_of_classifying S B A A'' (swap P) Q k1 k2.additive hs haddSS y hy
  have mx : Mono x := mono_of_isPerfect h1 hP x hx
  have my : Mono y := mono_of_isPerfect k1 hP.swap y hy
  have ix : IsIso x := by
    rcases le_or_gt g g' with hle | hlt
    · exact GlobalTheory.AbMonoIso.isIso_of_mono S B B' hB hB' g' g hg' (hd' g hg) hle x hmx mx
    · by_cases hS : Nonempty S
      · exfalso
        have iy := GlobalTheory.AbMonoIso.isIso_of_mono S A A'' hA hA'' g g' hg (hdQ g' hg') hlt.le y hmy my
        exact absurd (GlobalTheory.relDim_unique_of_iso_grp S hS A A'' y iy g g' hg (hdQ g' hg')) hlt.ne'
      · exact isIso_of_isEmpty (not_nonempty_iff.1 hS) x
  exact GlobalTheory.AbDual.transport S A B B' P P' h1 hP.isLB x ix hmx hx

theorem isDual_of_isPerfect (hD : GlobalTheory.Published.DualAbelianScheme) {S : Scheme.{0}} [IsLocallyNoetherian S]
    (A B : Over S) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hg' : SmoothOfRelativeDimension g' B.hom)
    {P : LB (A ⊗ B).left} (hP : IsPerfect A B P) : IsDual A B P :=
  isDual_of_isPerfect_of_additive hD A B hA hB hg hg' hP
    (CubeNoeth.isAdditive_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)
    (CubeNoeth.isAdditive_swap_of_triv_axes hA hB hP.isLB hP.zero_left hP.zero_right)

end GlobalTheory.PerfectDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_smoothOfRelativeDimension {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (p : Y ⟶ Z) (g : ℕ) (hp : SmoothOfRelativeDimension g p)
    (hq : SmoothOfRelativeDimension g (f ≫ p)) [FormallyUnramified f] : Etale f := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      fun R S _ _ _ r _ => RingHom.etale_algebraMap.mpr (.of_isLocalizationAway r)).left).mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hxV, e, H⟩ := hp.exists_isStandardSmoothOfRelativeDimension (f x)
  obtain ⟨W, hW, hxW, e'⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ V from hxV)
  have e'' : W ≤ (f ≫ p) ⁻¹ᵁ U := e'.trans (f.preimage_mono e)
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (f ≫ p) hq ⟨U, hU⟩ ⟨W, hW⟩ e''
  rw [RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso]
    at h1
  obtain ⟨s, hs, hfs⟩ := h1
  have hs' := iSup_basicOpen_of_span_eq_top _ _ hs
  have hx : x ∈ (⨆ i ∈ (s : Set Γ(X, W)), X.basicOpen i) := by rw [hs']; exact hxW
  have hx' : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := hx'
  have hloc : IsLocalization.Away r Γ(X, X.basicOpen r) := hW.isLocalization_basicOpen r
  have er : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans e'
  have h2 : ((f ≫ p).appLE U (X.basicOpen r)
      ((X.basicOpen_le r).trans e'')).hom.IsStandardSmoothOfRelativeDimension g := by
    rw [← (f ≫ p).appLE_map e'' (homOfLE (X.basicOpen_le r)).op]
    exact hfs r hr _
  have h3 : (f.appLE V (X.basicOpen r) er).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance ⟨V, hV⟩
      ⟨X.basicOpen r, hW.basicOpen r⟩ er
  refine ⟨⟨V, hV⟩, ⟨X.basicOpen r, hW.basicOpen r⟩, hxr, er, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE f p U V _ e er, CommRingCat.hom_comp] at h2
  letI := (p.appLE U V e).hom.toAlgebra
  letI := (f.appLE V (X.basicOpen r) er).hom.toAlgebra
  letI := ((f.appLE V (X.basicOpen r) er).hom.comp (p.appLE U V e).hom).toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact _root_.GlobalTheory.etale_of_formallyUnramified_of_relDim Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) g H h2 h3

theorem isOpenImmersion_of_mono_of_smoothOfRelativeDimension :
    ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p →
      SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  intro X Y Z f p g hp hq hf
  have : Etale f := etale_of_formallyUnramified_of_smoothOfRelativeDimension f p g hp hq
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjective
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.FiniteOverProj

theorem isProjOver_of_isFinite_over :
    ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  intro A o _ _ κ M Z z π s hz hπ _ hs
  have h : IsProjOver (π ≫ z) := GlobalTheory.isProjOver_comp_of_isFinite π hz
  rw [← hs] at h
  exact GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap κ h

end GlobalTheory.FiniteOverProj

end
end

