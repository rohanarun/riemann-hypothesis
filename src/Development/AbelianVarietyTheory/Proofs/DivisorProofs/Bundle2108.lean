module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectra
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch.Aff

theorem pinched_of_iso (g : ℕ) {S S' Z B' C Y B₂ C₂ Y₂ : Scheme.{0}} {s' : S' ⟶ S} {z : Z ⟶ S}
    {b' : B' ⟶ S'} {e : C ⟶ Z} {i : Y ⟶ B'} {q : Y ⟶ C}
    {b₂ : B₂ ⟶ S'} {e₂ : C₂ ⟶ Z} {i₂ : Y₂ ⟶ B₂} {q₂ : Y₂ ⟶ C₂}
    (eB : B' ≅ B₂) (eC : C ≅ C₂) (eY : Y ≅ Y₂)
    (hb : b' = eB.hom ≫ b₂) (he : e = eC.hom ≫ e₂) (hi : i ≫ eB.hom = eY.hom ≫ i₂)
    (hq : q ≫ eC.hom = eY.hom ≫ q₂) (x : B') (h : Pinched g s' z b₂ e₂ i₂ q₂ (eB.hom x)) :
    Pinched g s' z b' e i q x := by
  obtain ⟨U, U', V, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := h
  refine ⟨U, U', V, u, p, j ≫ eB.inv, n, k ≫ eC.inv, hu, ?_, inferInstance, ?_, ?_, ?_⟩
  · simpa [hb] using hp
  · obtain ⟨t, ht⟩ := hx
    refine ⟨t, ?_⟩
    simp [ht]
  · simpa [he] using hn
  · intro T a a' h
    obtain ⟨y, hy1, hy2⟩ := hl T a a' h
    refine ⟨y ≫ eY.inv, ?_, ?_⟩
    · have : eY.inv ≫ i = i₂ ≫ eB.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hi]; simp
      rw [Category.assoc, this, ← Category.assoc, hy1, Category.assoc]
    · have : eY.inv ≫ q = q₂ ≫ eC.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hq]; simp
      rw [Category.assoc, this, ← Category.assoc, hy2, Category.assoc]

theorem isPushout_of_isPullback_Spec {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPullback (Spec.map h) (Spec.map k) (Spec.map f) (Spec.map g)) :
    IsPushout f g h k := by
  have w : k.op ≫ g.op = h.op ≫ f.op := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact H.w.symm
  exact (IsPullback.of_map Scheme.Spec w H.flip).unop

end GlobalTheory.Pinch.Aff

namespace GlobalTheory.Pinch.Aff

theorem pinched_affine_of_spec : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  intro H R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hB hC hsm hss h1 h2 y
  haveI : IsAffine Y := IsAffine.of_isPullback h1
  haveI := hsm
  set φc : CommRingCat.of R' ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ b') with hφc
  set δc : CommRingCat.of (R ⧸ c) ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ e) with hδc
  set πc : Γ(B', ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom) with hπc
  set ψc : Γ(C, ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom) with hψc
  have eφ : spMap φc.hom = B'.isoSpec.inv ≫ b' := by simp [spMap, φc]
  have eδ : spMap δc.hom = C.isoSpec.inv ≫ e := by simp [spMap, δc]
  have eπ : spMap πc.hom = Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom := by simp [spMap, πc]
  have eψ : spMap ψc.hom = Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom := by simp [spMap, ψc]
  have hφs : φc.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφc, Spec.map_preimage]
    infer_instance
  have hδ : δc = (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).inv ≫ e.appTop := by
    apply Spec.map_injective
    rw [hδc, Spec.map_preimage, Spec.map_comp, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hδs : δc.hom.IsStandardSmoothOfRelativeDimension g := by
    rw [hδ, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).mpr hss
  have hp1 : IsPushout (CommRingCat.ofHom (φc.hom.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c))
      (CommRingCat.ofHom πc.hom) (CommRingCat.ofHom (ψc.hom.comp δc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap πc.hom) (spMap ψc.hom ≫ spMap δc.hom) (spMap φc.hom ≫ spMap (algebraMap R R'))
      (spMap (Ideal.Quotient.mk c))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h1 Y.isoSpec B'.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hp2 : IsPushout (CommRingCat.ofHom (δc.hom.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom ψc.hom) (CommRingCat.ofHom (πc.hom.comp φc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap ψc.hom) (spMap πc.hom ≫ spMap φc.hom) (spMap δc.hom ≫ spMap (Ideal.Quotient.mk c))
      (spMap (algebraMap R R'))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h2 Y.isoSpec C.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hP := H R R' hinj c hc g Γ(B', ⊤) Γ(C, ⊤) Γ(Y, ⊤) φc.hom δc.hom πc.hom ψc.hom hφs hδs hp1 hp2
    (Y.isoSpec.hom y)
  have hpt : spMap πc.hom (Y.isoSpec.hom y) = B'.isoSpec.hom (i y) := by
    rw [eπ]; simp
  rw [hpt] at hP
  refine pinched_of_iso g B'.isoSpec C.isoSpec Y.isoSpec ?_ ?_ ?_ ?_ (i y) hP
  · rw [eφ]; simp
  · rw [eδ]; simp
  · rw [eπ]; simp
  · rw [eψ]; simp

end GlobalTheory.Pinch.Aff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PinchLift.FlatBC

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S}
    {iY : Y ⟶ T} (H : IsPullback g iY iX f) {US : S.Opens} {UT : T.Opens} {UX : X.Opens} {UY : Y.Opens}
    (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT) (hUX : IsAffineOpen UX)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (h₁ : UY ≤ g ⁻¹ᵁ UX) (h₂ : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (iX.appLE US UX hUSX) (f.appLE US UT hUST) (g.appLE UX UY h₁) (iY.appLE UT UY h₂) :=
  (isIso_pushoutSection_iff H hUST hUSX hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY hUS hUT hUX)

theorem appLE_congr_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) (U : B.Opens) (V : A.Opens)
    (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

end GlobalTheory.PinchLift.FlatBC

namespace GlobalTheory.PinchLift.FlatBC

theorem glues_affine_of_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  intro S E X X' Z Z' p i i' p' hE hc hpb hp hi hglue V W hV hW hWV a b hab
  have hcl : i'.left ≫ p.left = p'.left ≫ i.left := by
    rw [← Over.comp_left, ← Over.comp_left, hc]
  have hcE : (E ◁ i').left ≫ (E ◁ p).left = (E ◁ p').left ≫ (E ◁ i).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, hc]
  have nat : ∀ {Y Y' : Over S} (j : Y' ⟶ Y),
      (E ◁ j).left ≫ (snd E Y).left = (snd E Y').left ≫ j.left := by
    intro Y Y' j
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  haveI : IsAffineHom i.left := inferInstance
  haveI : IsClosedImmersion i'.left := MorphismProperty.of_isPullback hpb.flip ‹_›
  haveI : IsAffineHom p'.left := MorphismProperty.of_isPullback hpb ‹_›
  haveI : Flat (snd E X).left := by
    change Flat (pullback.snd E.hom X.hom); infer_instance
  have eV : p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcl]
  have eW : (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) = (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hcE]
  have hDV : i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V) = (i'.left ≫ p.left) ⁻¹ᵁ V := by
    rw [eV, inf_idem]; rfl
  have hDW : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W := by
    rw [eW, inf_idem]; rfl
  have hDVa : IsAffineOpen (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDV]; exact hV.preimage _
  have H1 := isPullback_whiskerLeft_snd_left E p
  have H2 := isPullback_whiskerLeft_snd_left E i
  have H3 : IsPullback ((E ◁ i').left ≫ (E ◁ p).left) (snd E Z').left (snd E X).left
      (i'.left ≫ p.left) := by
    have := isPullback_whiskerLeft_snd_left E (i' ≫ p)
    rwa [MonoidalCategory.whiskerLeft_comp, Over.comp_left, Over.comp_left] at this
  have hU1 : (E ◁ p).left ⁻¹ᵁ W = (E ◁ p).left ⁻¹ᵁ W ⊓ (snd E X').left ⁻¹ᵁ (p.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat p, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have hU2 : (E ◁ i).left ⁻¹ᵁ W = (E ◁ i).left ⁻¹ᵁ W ⊓ (snd E Z).left ⁻¹ᵁ (i.left ⁻¹ᵁ V) := by
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, ← nat i, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hWV
  have nat3 : ((E ◁ i').left ≫ (E ◁ p).left) ≫ (snd E X).left =
      (snd E Z').left ≫ (i'.left ≫ p.left) := by
    rw [Category.assoc, nat p, ← Category.assoc, nat i', Category.assoc]
  have hU3 : (E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W) =
      ((E ◁ i').left ≫ (E ◁ p).left) ⁻¹ᵁ W ⊓
        (snd E Z').left ⁻¹ᵁ (i'.left ⁻¹ᵁ (p.left ⁻¹ᵁ V) ⊓ p'.left ⁻¹ᵁ (i.left ⁻¹ᵁ V)) := by
    rw [hDW, hDV]
    refine (inf_eq_left.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage (snd E Z').left (i'.left ≫ p.left) V, ← nat3,
      Scheme.Hom.comp_preimage _ (snd E X).left V]
    exact Scheme.Hom.preimage_mono _ hWV
  have P1 := isPushout_appLE_of_isPullback H1 hV (hV.preimage p.left) hW le_rfl hWV hU1 le_rfl
    (hU1.le.trans inf_le_right)
  have P2 := isPushout_appLE_of_isPullback H2 hV (hV.preimage i.left) hW le_rfl hWV hU2 le_rfl
    (hU2.le.trans inf_le_right)
  have P3 := isPushout_appLE_of_isPullback H3 hV hDVa hW hDV.le hWV hU3 (hU3.le.trans inf_le_left)
    (hU3.le.trans inf_le_right)
  have key := _root_.GlobalTheory.FlatFibreProduct.exists_unique_of_flat_of_isPushout (p.left.appLE V (p.left ⁻¹ᵁ V) le_rfl) (i.left.appLE V (i.left ⁻¹ᵁ V) le_rfl)
    (i'.left.appLE (p.left ⁻¹ᵁ V) _ inf_le_left) (p'.left.appLE (i.left ⁻¹ᵁ V) _ inf_le_right)
    ((snd E X).left.appLE V W hWV)
    ((snd E X').left.appLE (p.left ⁻¹ᵁ V) ((E ◁ p).left ⁻¹ᵁ W) (hU1.le.trans inf_le_right))
    ((snd E Z).left.appLE (i.left ⁻¹ᵁ V) ((E ◁ i).left ⁻¹ᵁ W) (hU2.le.trans inf_le_right))
    ((snd E Z').left.appLE _ _ (hU3.le.trans inf_le_right))
    ((E ◁ p).left.appLE W _ le_rfl) ((E ◁ i).left.appLE W _ le_rfl)
    ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) _ inf_le_left)
    ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) _ inf_le_right)
    ((snd E X).left.flat_appLE hV hW hWV) P1 P2
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; exact P3)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat i') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq (nat p') _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcE _ _ _ _)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
        exact appLE_congr_of_eq hcl _ _ _ _)
    (fun b c h => by
      have := hglue V b c h
      rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE] at this) a b hab
  rwa [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]

end GlobalTheory.PinchLift.FlatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TorsGeomPow

theorem pow_eq_one_of_geometric_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  intro S A _ hA n hn T x hx d hpt
  obtain ⟨-, -, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  set P : Over S := pullback (mulN A n) (η : 𝟙_ (Over S) ⟶ A) with hP
  have hPe : Etale P.hom := hZe
  have hxd : (x ^ d) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, ← pow_mul, mul_comm, pow_mul, hx, one_pow, CategoryTheory.Hom.one_def]
  have h1 : (1 : T ⟶ A) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, one_pow, CategoryTheory.Hom.one_def]
  let y₁ : T ⟶ P := pullback.lift (x ^ d) (toUnit T) hxd
  let u₁ : T ⟶ P := pullback.lift 1 (toUnit T) h1
  have hy : y₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = x ^ d := pullback.lift_fst _ _ _
  have hu : u₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = 1 := pullback.lift_fst _ _ _
  have key : ∀ {W : Over S} (f : W ⟶ T), (f ≫ x) ^ d = 1 → f ≫ y₁ = f ≫ u₁ := by
    intro W f hf
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy, hu, MonObj.comp_pow, hf, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hyu : y₁ = u₁ := by
    haveI := hPe
    have hw : y₁.left ≫ P.hom = u₁.left ≫ P.hom := by rw [Over.w, Over.w]
    let l : T.left ⟶ pullback P.hom P.hom := pullback.lift _ _ hw
    have hl1 : l ≫ pullback.fst _ _ = y₁.left := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = u₁.left := pullback.lift_snd _ _ _
    have hs : Function.Surjective (pullback.snd (pullback.diagonal P.hom) l) := by
      intro s
      let k := AlgebraicClosure (T.left.residueField s)
      let ξ : Sp k ⟶ T.left :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField s) k)) ≫ T.left.fromSpecResidueField s
      have hξ : ξ ≫ y₁.left = ξ ≫ u₁.left :=
        congrArg CommaMorphism.left (key (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) (hpt k ξ))
      have hq : (ξ ≫ y₁.left) ≫ pullback.diagonal P.hom = ξ ≫ l := by
        apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [pullback.diagonal_fst, Category.comp_id, hl1]
        · simp only [Category.assoc]
          rw [pullback.diagonal_snd, Category.comp_id, hl2, hξ]
      refine ⟨pullback.lift _ _ hq (IsLocalRing.closedPoint k), ?_⟩
      have e : (pullback.lift _ _ hq ≫ pullback.snd (pullback.diagonal P.hom) l) (IsLocalRing.closedPoint k) =
          ξ (IsLocalRing.closedPoint k) := by rw [Limits.pullback.lift_snd]
      refine (Eq.trans ?_ e).trans ?_
      · rfl
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply s _)
    have : Epi (pullback.snd (pullback.diagonal P.hom) l).base :=
      (TopCat.epi_iff_surjective _).2 hs
    have : IsIso (pullback.snd (pullback.diagonal P.hom) l) := IsOpenImmersion.isIso _
    have hl : l = inv (pullback.snd (pullback.diagonal P.hom) l) ≫ pullback.fst _ _ ≫
        pullback.diagonal P.hom := by
      rw [pullback.condition, IsIso.inv_hom_id_assoc]
    apply Over.OverMorphism.ext
    rw [← hl1, ← hl2, hl]
    simp
  rw [← hy, hyu, hu]

end GlobalTheory.TorsGeomPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime]

structure SimSys (D : Datum p) (N K : ℕ) where
  g : ℕ → D.La →+ D.La
  u : ℕ → ℕ
  lin : ∀ n, 0 < n → n.Coprime p → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  u_cop : ∀ n, 0 < n → n.Coprime p → (u n).Coprime n
  u_tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n]
  surj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w
  sim : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - u n * D.EF x y
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z
  one : ∀ x, ∃ z, g K x = x + N • z

variable {D : Datum p} {N K : ℕ}

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem TateIsoO.ev_nsmul_self (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (z : D.La) :
    I.ev n (n • z) = 1 :=
  (I.ker n hn hc _).2 ⟨z, rfl⟩

theorem TateIsoO.ev_add_nsmul (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (x z : D.La) :
    I.ev n (x + n • z) = I.ev n x := by
  rw [I.add, I.ev_nsmul_self hn hc, _root_.mul_one]

end Tate

variable {R : Type} [CommRing R]


variable (D K) in
def multSub : AddSubgroup D.La where
  carrier := {x | ∃ z, x = K • z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    exact ⟨a + c, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (smul_neg _ _).symm⟩


variable (D K) in
abbrev LQ := D.La ⧸ multSub D K


end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

variable {Y X : Scheme.{0}} [IsIntegral Y] [IsIntegral X]

theorem theta_stalk {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    (a : X.presheaf.stalk (π y)) :
    θ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a) := by
  obtain ⟨l, h₁, h₂⟩ := h
  rw [Category.comp_id] at h₁
  subst h₁
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes y)
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
  have e₁ : Spec.map sY ≫ Y.fromSpecStalk y = gp Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : π.stalkMap y ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (π y)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  exact (congrArg (fun f => CommRingCat.Hom.hom f a) e₂).symm

theorem theta_fnOf {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ)
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hU s) = fnOf (π ⁻¹ᵁ U) hU' (π.app U s) := by
  have hU'' : π (genericPoint Y) ∈ U := hU'
  rw [← algebraMap_germ (x := π (genericPoint Y)) hU'' s, theta_stalk h,
    Scheme.Hom.germ_stalkMap_apply]
  exact algebraMap_germ hU' _

theorem regAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨_, (theta_stalk h y a).symm⟩

theorem unitAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : UnitAt (π y) u) : UnitAt y (θ u) := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨_, ha.map _, (theta_stalk h y a).symm⟩

theorem preimage_regSet {π : Y ⟶ X} [Flat π] {θ : X.functionField →+* Y.functionField}
    (h : PFF (𝟙 _) π θ) (y : Y) : θ ⁻¹' (regSet y) = regSet (π y) := by
  ext u
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hu => regAt_theta h y hu⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y)) u
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  letI := (π.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π y))
    (B := Y.presheaf.stalk y)
  have e : π.stalkMap y a = c * π.stalkMap y b := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hc, ← theta_stalk h, ← theta_stalk h, ← map_mul, div_mul_cancel₀ _ hb0]
  have hm : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {b}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, e.symm⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨d, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩

theorem spMap_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : spMap (GlobalTheory.Desc.cst p) = gp X ≫ p := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  conv_rhs => rw [h, gp, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem comp_cst {V : Scheme.{0}} {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {p : X ⟶ Sp R}
    {q : Y ⟶ Sp R₁} {i : V ⟶ Y} {φ : V ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap ((GlobalTheory.Desc.cst q).comp ρ) := by
    have e1 : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap θ ≫ spMap (GlobalTheory.Desc.cst p) := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((GlobalTheory.Desc.cst q).comp ρ) = spMap (GlobalTheory.Desc.cst q) ≫ spMap ρ := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, spMap_cst, spMap_cst, ← Category.assoc, ← h₂, ← h₁]
    simp only [Category.assoc, w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem regAt_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem unitAt_cst_iff {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    UnitAt x (GlobalTheory.Desc.cst p r) ↔ r ∉ (p x).asIdeal := by
  refine (unitAt_fnOf_iff (U := ⊤) trivial trivial _).trans ?_
  change x ∈ X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

end GlobalTheory.Desc.GaussPt
end

