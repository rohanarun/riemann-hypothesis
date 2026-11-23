module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivityDefectGeneratorInvariantSameImage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

namespace GlobalTheory.CharKer

private theorem coe_gm_eq_stalkMap_germ {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U)
    (a : Γ(X, U)ˣ) :
    ((gm f y U a : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      f.stalkMap y (X.presheaf.germ U (f y) h (a : Γ(X, U))) := by
  unfold gm
  rw [dite_eq_left h]
  simp only [pullU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact (Scheme.Hom.germ_stalkMap_apply f U y h _).symm

private theorem gm_res_pullU_lemma_2 {X Y Z : Scheme.{0}} (φ : Y ⟶ X) (ψ : Z ⟶ Y) (z : Z) (U : X.Opens)
    {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (hz : ψ z ∈ V) (a : Γ(X, U)ˣ) :
    gm ψ z V (res hle (pullU φ U a)) = gm (ψ ≫ φ) z U a := by
  have h1 : φ (ψ z) ∈ U := hle hz
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ ψ z V hz, coe_gm_eq_stalkMap_germ (ψ ≫ φ) z U h1]
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [Scheme.Hom.stalkMap_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  exact congrArg (Scheme.Hom.stalkMap ψ z) (Scheme.Hom.germ_stalkMap_apply φ U (ψ z) h1 _).symm

private theorem gm_pullTop_inv {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)ˣ) :
    gm f z ⊤ (pullTop g a) = gm (f ≫ g) z ⊤ a := by
  apply Units.ext
  rw [coe_gm_eq_stalkMap_germ f z ⊤ trivial, coe_gm_eq_stalkMap_germ (f ≫ g) z ⊤ trivial]
  rw [Scheme.Hom.stalkMap_comp]
  exact congrArg (Scheme.Hom.stalkMap f z) (Scheme.Hom.germ_stalkMap_apply g ⊤ (f z) trivial _).symm

theorem gm_character_mul {S : Scheme.{0}} {N T Z : Over S} [GrpObj N] {χ : Γ((N ⊗ T).left, ⊤)ˣ}
    (hχ : IsCharacter χ) (ν₁ ν₂ : Z ⟶ N) (t : Z ⟶ T) (z : Z.left) :
    gm (lift (ν₁ * ν₂) t).left z ⊤ χ = gm (lift ν₁ t).left z ⊤ χ * gm (lift ν₂ t).left z ⊤ χ := by
  have hy1 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) =
      lift (ν₁ * ν₂) t := by
    simp [comp_lift, MonObj.comp_mul]
  have hy2 : lift ν₁ (lift ν₂ t) ≫ lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) = lift ν₁ t := by
    simp [comp_lift]
  have hy3 : lift ν₁ (lift ν₂ t) ≫ snd N (N ⊗ T) = lift ν₂ t := by simp
  have hc : IsCharacter χ := hχ
  unfold IsCharacter at hc
  rw [← hy1, Over.comp_left, ← gm_pullTop_inv, hc, map_mul, gm_pullTop_inv, gm_pullTop_inv,
    ← Over.comp_left, ← Over.comp_left, hy2, hy3]

theorem gm_equivGen {S : Scheme.{0}} {A A' N T Z : Over S} [GrpObj A] {i : N ⟶ A} {q : A ⟶ A'}
    {χ : Γ((N ⊗ T).left, ⊤)ˣ} {M : LB (A' ⊗ T).left} {e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ}
    (he : IsEquivGen i q χ M e) (a b : Z ⟶ A) (ν : Z ⟶ N) (t : Z ⟶ T) (hb : b = a * (ν ≫ i)) (z : Z.left)
    (k : M.ι) (h₁ : (lift b t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k)
    (h₂ : (lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U k) :
    gm (lift b t).left z _ (e k) = gm (lift ν t).left z ⊤ χ * gm (lift a t).left z _ (e k) := by
  set y : Z ⟶ A ⊗ (N ⊗ T) := lift a (lift ν t) with hy
  have e1 : y.left ≫ (actMap i T).left = (lift b t).left := by
    rw [← Over.comp_left, hb, hy]
    unfold actMap
    simp [comp_lift, MonObj.comp_mul]
  have e2 : y.left ≫ (prMap A N T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold prMap
    simp [comp_lift]
  have e3 : y.left ≫ (snd A (N ⊗ T)).left = (lift ν t).left := by
    rw [← Over.comp_left, hy]
    simp
  have w1 : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e1] at h₁
    exact h₁
  have w2 : y.left z ∈ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := by
    rw [← e2] at h₂
    exact h₂
  have key := congrArg (gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
    (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))) (he.2 k _ inf_le_left inf_le_right)
  have hw : y.left z ∈ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) := ⟨w1, w2⟩
  rw [map_mul, gm_res_pullU_lemma_2 _ _ _ _ _ hw, gm_res_pullU_lemma_2 _ _ _ _ _ hw, e1, e2] at key
  have hχ' : gm y.left z ((actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k) ⊓
      (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)) (res le_top (pullTop (snd A (N ⊗ T)).left χ)) =
      gm (lift ν t).left z ⊤ χ := by
    have := gm_res_pullU_lemma_2 (snd A (N ⊗ T)).left y.left z ⊤ (V := _) le_top hw χ
    rw [e3] at this
    exact this
  rw [hχ'] at key
  exact key

theorem gm_addGen {S : Scheme.{0}} {A A' T Z : Over S} [GrpObj A] [GrpObj A'] (q : A ⟶ A') [IsMonHom q]
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (a a' : Z ⟶ A) (t : Z ⟶ T)
    (z : Z.left) (k : (addBundle M).ι)
    (h : (lift a (lift a' t)).left z ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k) :
    ((lift a t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit) ∧
      (lift a' t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit) ∧
      (lift (a * a') t).left z ∈ (pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) ∧
    gm (lift a (lift a' t)).left z _ (addGen q M e k) =
      gm (lift a t).left z _ (e (k.1.1 PUnit.unit)) * gm (lift a' t).left z _ (e (k.1.2 PUnit.unit)) *
        (gm (lift (a * a') t).left z _ (e (k.2 PUnit.unit)))⁻¹ := by
  set y : Z ⟶ A ⊗ (A ⊗ T) := lift a (lift a' t) with hy
  have eF : y.left ≫ (ptFst A T).left = (lift a t).left := by
    rw [← Over.comp_left, hy]
    unfold ptFst
    simp [comp_lift]
  have eS : y.left ≫ (ptSnd A T).left = (lift a' t).left := by
    rw [← Over.comp_left, hy]
    unfold ptSnd
    simp [comp_lift]
  have eM : y.left ≫ (ptMul A T).left = (lift (a * a') t).left := by
    rw [← Over.comp_left, hy]
    unfold ptMul
    simp [comp_lift, MonObj.comp_mul]
  have m1 := addGen_le₁ q M k h
  have m2 := addGen_le₂ q M k h
  have m3 := addGen_le₃ q M k h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← eF]
    exact m1
  · rw [← eS]
    exact m2
  · rw [← eM]
    exact m3
  · unfold addGen
    rw [map_mul, map_mul, map_inv, gm_res_pullU_lemma_2 _ _ _ _ _ h, gm_res_pullU_lemma_2 _ _ _ _ _ h,
      gm_res_pullU_lemma_2 _ _ _ _ _ h, eF, eS, eM]

private theorem germ_eq_gm_coe {Z : Scheme.{0}} (W : Z.Opens) (w : Z) (hw : w ∈ W) (x : Γ(Z, W)ˣ) :
    Z.presheaf.germ W w hw (x : Γ(Z, W)) = ((gm (𝟙 Z) w W x : (Z.presheaf.stalk w)ˣ) : Z.presheaf.stalk w) := by
  rw [coe_gm_eq_stalkMap_germ (𝟙 Z) w W hw]
  erw [Scheme.Hom.stalkMap_id]
  rfl

private theorem mul_mul_mul_inv_cancel_left_factors {G : Type*} [CommGroup G] (c₁ c₂ E₁ E₂ E₃ : G) :
    c₁ * E₁ * (c₂ * E₂) * (c₁ * c₂ * E₃)⁻¹ = E₁ * E₂ * E₃⁻¹ := by
  rw [mul_inv (c₁ * c₂) E₃, _root_.mul_mul_mul_comm c₁ E₁ c₂ E₂, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]

theorem addGen_invariant : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') [IsMonHom q] (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsMonHom i → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → IsEquivGen i q χ M e → ∀ (Z : Scheme.{0}) (y₁ y₂ : Z ⟶ (A ⊗ (A ⊗ T)).left), y₁ ≫ (pmap2 q T).left = y₂ ≫ (pmap2 q T).left → ∀ (k : (addBundle M).ι) (W : Z.Opens) (h₁ : W ≤ y₁ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)) (h₂ : W ≤ y₂ ⁻¹ᵁ ((pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)), res h₁ (pullU y₁ _ (addGen q M e k)) = res h₂ (pullU y₂ _ (addGen q M e k)) := by
  intro S A A' N T _i1 _i2 _i3 _i4 i q _i5 χ M e hi hpb hχ he Z y₁ y₂ hy k W h₁ h₂
  haveI := hi
  apply Units.ext
  apply TopCat.Presheaf.section_ext Z.sheaf W
  intro w hw
  erw [germ_eq_gm_coe W w hw, germ_eq_gm_coe W w hw]
  rw [gm_res_pullU_lemma_2 y₁ (𝟙 Z) w _ h₁ hw, gm_res_pullU_lemma_2 y₂ (𝟙 Z) w _ h₂ hw, Category.id_comp,
    Category.id_comp]
  have m₁ : y₁ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₁ hw
  have m₂ : y₂ w ∈ (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k := h₂ hw
  have hyS : y₂ ≫ (A ⊗ (A ⊗ T)).hom = y₁ ≫ (A ⊗ (A ⊗ T)).hom := by
    have h := congrArg (· ≫ (A' ⊗ (A' ⊗ T)).hom) hy
    simp only [Category.assoc, Over.w] at h
    exact h.symm
  let Z' : Over S := Over.mk (y₁ ≫ (A ⊗ (A ⊗ T)).hom)
  let Y₁ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₁ rfl
  let Y₂ : Z' ⟶ A ⊗ (A ⊗ T) := Over.homMk y₂ hyS
  have hY : Y₁ ≫ pmap2 q T = Y₂ ≫ pmap2 q T := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    exact hy
  have h_a : Y₁ ≫ fst A (A ⊗ T) ≫ q = Y₂ ≫ fst A (A ⊗ T) ≫ q := by
    have h := congrArg (· ≫ fst A' (A' ⊗ T)) hY
    simpa [pmap2] using h
  have h_b : Y₁ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q = Y₂ ≫ snd A (A ⊗ T) ≫ fst A T ≫ q := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ fst A' T) hY
    simpa [pmap2, pmap] using h
  have h_t : Y₁ ≫ snd A (A ⊗ T) ≫ snd A T = Y₂ ≫ snd A (A ⊗ T) ≫ snd A T := by
    have h := congrArg (· ≫ snd A' (A' ⊗ T) ≫ snd A' T) hY
    simpa [pmap2, pmap] using h
  have eY₁ : lift (Y₁ ≫ fst A (A ⊗ T)) (lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have eY₂ : lift (Y₂ ≫ fst A (A ⊗ T)) (lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T)) = Y₂ := by
    rw [h_t]
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have hP := pmap_isPullback_actMap S A A' N T i q hi inferInstance hpb
  have wa : lift (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_a]
  have wb : lift (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T =
      lift (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) ≫ pmap q T := by
    simp [pmap, comp_lift, h_b]
  have key : ∀ (a₁ a₂ : Z' ⟶ A) (t : Z' ⟶ T), lift a₁ t ≫ pmap q T = lift a₂ t ≫ pmap q T →
      ∃ ν : Z' ⟶ N, a₂ = a₁ * (ν ≫ i) := by
    intro a₁ a₂ t hw'
    have e1 := congrArg (· ≫ fst A T) (hP.lift_snd (lift a₁ t) (lift a₂ t) hw')
    have e2 := congrArg (· ≫ fst A T) (hP.lift_fst (lift a₁ t) (lift a₂ t) hw')
    generalize hP.lift (lift a₁ t) (lift a₂ t) hw' = u at e1 e2
    refine ⟨u ≫ snd A (N ⊗ T) ≫ fst N T, ?_⟩
    simp only [actMap, prMap, Category.assoc, lift_fst, MonObj.comp_mul] at e1 e2
    rw [← e1, e2]
    simp [Category.assoc]
  obtain ⟨ν, hν⟩ := key _ _ _ wa
  obtain ⟨ν', hν'⟩ := key _ _ _ wb
  have hνν : Y₂ ≫ fst A (A ⊗ T) * (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T) =
      Y₁ ≫ fst A (A ⊗ T) * (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T) * ((ν * ν') ≫ i) := by
    rw [hν, hν', MonObj.mul_comp, _root_.mul_mul_mul_comm]
  have M₁ := (gm_addGen q M e (Y₁ ≫ fst A (A ⊗ T)) (Y₁ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₁]; exact m₁))
  have M₂ := (gm_addGen q M e (Y₂ ≫ fst A (A ⊗ T)) (Y₂ ≫ snd A (A ⊗ T) ≫ fst A T)
    (Y₁ ≫ snd A (A ⊗ T) ≫ snd A T) w k (by rw [eY₂]; exact m₂))
  have G₁ := M₁.2
  have G₂ := M₂.2
  rw [eY₁] at G₁
  rw [eY₂] at G₂
  refine congrArg Units.val ?_
  change gm Y₁.left w _ (addGen q M e k) = gm Y₂.left w _ (addGen q M e k) at ⊢
  rw [G₁, G₂, gm_equivGen he _ _ ν _ hν w _ M₂.1.1 M₁.1.1, gm_equivGen he _ _ ν' _ hν' w _ M₂.1.2.1 M₁.1.2.1,
    gm_equivGen he _ _ (ν * ν') _ hνν w _ M₂.1.2.2 M₁.1.2.2, gm_character_mul hχ ν ν', mul_mul_mul_inv_cancel_left_factors]

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairLiftsGlueToMorphismOfLifts
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.GluePair

open Opposite _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits GlobalTheory.LiftSys.Glue

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ Z₀ : Scheme.{0}} {t₀ : Z₀ ⟶ Sp R₀}

abbrev fh {f₀ : Z₀ ⟶ X₀} {T₁ T₂ : Pair f₀} (a : T₁ ⟶ T₂) : (op T₂.1.1 : AffOp Z₀) ⟶ op T₁.1.1 :=
  (homOfLE (Pair.le_fst (leOfHom a))).op

abbrev cov {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z) : Z.OpenCover where
  I₀ := Pair f₀
  X T := Sp (S'.F.obj (op T.1.1))
  f T := P'.y (op T.1.1)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨T, z, hz⟩ := hc x; exact ⟨T, z, hz⟩, fun T ↦ P'.isOpen _⟩

def dir {S' : Sys I π t₀} {Z : Scheme.{0}} {t : Z ⟶ Sp R} {k : Z₀ ⟶ Z} (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀)
    (hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z)
    (hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a) :
    (cov P' f₀ hc).LocallyDirected where
  trans {T₁ T₂} a := spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1))
  trans_id T := by
    haveI := P'.isOpen (op T.1.1)
    rw [← cancel_mono (P'.y (op T.1.1))]
    exact (P'.nat _).trans (Category.id_comp _).symm
  trans_comp {T₁ T₂ T₃} a b := by
    haveI := P'.isOpen (op T₃.1.1)
    rw [← cancel_mono (P'.y (op T₃.1.1))]
    rw [Category.assoc]
    exact (P'.nat _).trans ((congrArg (_ ≫ ·) (P'.nat _)).trans (P'.nat _)).symm
  w {T₁ T₂} a := P'.nat _
  directed {T₁ T₂} x := by
    haveI := P'.isOpen (op T₁.1.1)
    haveI := P'.isOpen (op T₂.1.1)
    obtain ⟨T₃, h₁, h₂, c, hcT⟩ := hd T₁ T₂ (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (pullback.snd (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨T₃, homOfLE h₁, homOfLE h₂, c, ?_⟩
    apply (pullback.fst (P'.y (op T₁.1.1)) (P'.y (op T₂.1.1)) ≫ P'.y (op T₁.1.1)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ P'.y (op T₁.1.1)) c = _
    rw [P'.nat, hcT, Scheme.Hom.comp_apply]
  property_trans {T₁ T₂} a := by
    haveI := P'.isOpen (op T₂.1.1)
    haveI : IsOpenImmersion (spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
        P'.y (op T₂.1.1)) := by
      rw [P'.nat]; exact P'.isOpen _
    exact IsOpenImmersion.of_comp _ (P'.y (op T₂.1.1))

end GlobalTheory.Obs.GluePair

namespace GlobalTheory.Obs

open Opposite _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits GlobalTheory.LiftSys.Glue GlobalTheory.Obs.GluePair

theorem pairs_glue : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l → ∃ f : Z ⟶ X, f ≫ s = t ∧ k ≫ f = f₀ ≫ i := by
  intro R R₀ _ _ I hI π hπ hk X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h l hL hN
  have hsurU : ∀ W, Function.Surjective (spMap (S'.p W)) := fun W ↦
    spMap_surjective _ (S'.surj W) fun b hb ↦ by
      have hb' := (S'.ker W b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj W))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hkc : IsClosedImmersion k := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hkk.flip inferInstance
  have hinj : Function.Injective k := k.isClosedEmbedding.injective
  have hksurj : Function.Surjective k :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hkk.flip ⟨hπs⟩).surj

  have hrng : ∀ (W : Z₀.affineOpens) (w : Sp (S'.F.obj (op W))), ∃ z₀ ∈ W.1, P'.y (op W) w = k z₀ := by
    intro W w
    obtain ⟨v, rfl⟩ := hsurU (op W) w
    refine ⟨affPt t₀ W v, W.2.range_fromSpec.le ⟨v, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, P'.red (op W), Scheme.Hom.comp_apply]
  have hcov : ∀ (W : Z₀.affineOpens) (z₀ : Z₀), z₀ ∈ W.1 → ∃ w : Sp (S'.F.obj (op W)), P'.y (op W) w = k z₀ := by
    intro W z₀ hz
    obtain ⟨v, hv⟩ : z₀ ∈ Set.range (affPt t₀ W) := W.2.range_fromSpec.ge hz
    refine ⟨spMap (S'.p (op W)) v, ?_⟩
    change (spMap (S'.p (op W)) ≫ P'.y (op W)) v = k z₀
    rw [P'.red (op W), Scheme.Hom.comp_apply]
    exact congrArg k hv

  have hpair : ∀ (z₀ : Z₀) (U : X₀.affineOpens), f₀ z₀ ∈ U.1 → ∀ V : Z₀.Opens, z₀ ∈ V →
      ∃ T : Pair f₀, z₀ ∈ T.1.1.1 ∧ T.1.2 = U ∧ T.1.1.1 ≤ V := by
    intro z₀ U hU V hV
    obtain ⟨W, hW, hWle⟩ := exists_affine (show z₀ ∈ V ⊓ f₀ ⁻¹ᵁ U.1 from ⟨hV, hU⟩)
    exact ⟨⟨(W, U), hWle.trans inf_le_right⟩, hW, rfl, hWle.trans inf_le_left⟩
  have hpt : ∀ z₀ : Z₀, ∃ T : Pair f₀, z₀ ∈ T.1.1.1 := by
    intro z₀
    obtain ⟨U, hU, -⟩ := exists_affine (show f₀ z₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨T, hT, -, -⟩ := hpair z₀ U hU ⊤ trivial
    exact ⟨T, hT⟩
  have hc : ∀ z : Z, ∃ (T : Pair f₀) (w : Sp (S'.F.obj (op T.1.1))), P'.y (op T.1.1) w = z := by
    intro z
    obtain ⟨z₀, rfl⟩ := hksurj z
    obtain ⟨T, hT⟩ := hpt z₀
    obtain ⟨w, hw⟩ := hcov T.1.1 z₀ hT
    exact ⟨T, w, hw⟩
  have hd : ∀ (T₁ T₂ : Pair f₀) (a : Sp (S'.F.obj (op T₁.1.1))) (b : Sp (S'.F.obj (op T₂.1.1))),
      P'.y (op T₁.1.1) a = P'.y (op T₂.1.1) b → ∃ (T₃ : Pair f₀) (_ : T₃ ≤ T₁) (_ : T₃ ≤ T₂)
        (c : Sp (S'.F.obj (op T₃.1.1))), P'.y (op T₃.1.1) c = P'.y (op T₁.1.1) a := by
    intro T₁ T₂ a b hab
    obtain ⟨z₀, h₁, ha⟩ := hrng T₁.1.1 a
    obtain ⟨z₁, h₂, hb⟩ := hrng T₂.1.1 b
    have e : z₀ = z₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    have hU₁ : f₀ z₀ ∈ T₁.1.2.1 := T₁.2 h₁
    have hU₂ : f₀ z₀ ∈ T₂.1.2.1 := T₂.2 h₂
    obtain ⟨U₃, hU₃, hU₃le⟩ := exists_affine (show f₀ z₀ ∈ T₁.1.2.1 ⊓ T₂.1.2.1 from ⟨hU₁, hU₂⟩)
    obtain ⟨T₃, hT₃, e₃, hT₃le⟩ := hpair z₀ U₃ hU₃ (T₁.1.1.1 ⊓ T₂.1.1.1) ⟨h₁, h₂⟩
    subst e₃
    obtain ⟨c, hc'⟩ := hcov T₃.1.1 z₀ hT₃
    refine ⟨T₃, ?_, ?_, c, hc'.trans ha.symm⟩
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).1, (le_inf_iff.1 hU₃le).1⟩)
    · exact Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(le_inf_iff.1 hT₃le).2, (le_inf_iff.1 hU₃le).2⟩)
  letI := dir P' f₀ hc hd
  let 𝒰 := cov P' f₀ hc
  let lr : ∀ T : Pair f₀, S.F.obj (op T.1.2) →+* S'.F.obj (op T.1.1) := fun T ↦ (l (op T)).toRingHom
  let g : ∀ T : 𝒰.I₀, 𝒰.X T ⟶ X := fun T ↦ spMap (lr T) ≫ P.y (op T.1.2)
  have hg : ∀ {T₁ T₂ : 𝒰.I₀} (a : T₁ ⟶ T₂), 𝒰.trans a ≫ g T₂ = g T₁ := by
    intro T₁ T₂ a
    change spMap (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)) ≫
      spMap (lr T₂) ≫ P.y (op T₂.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F (fh a) : S'.F.obj (op T₂.1.1) →+* S'.F.obj (op T₁.1.1)).comp (lr T₂) =
        (lr T₁).comp (mp S.F (homOfLE (Pair.le_snd (leOfHom a))).op : S.F.obj (op T₂.1.2) →+* S.F.obj (op T₁.1.2)) :=
      RingHom.ext fun b ↦ hN a.op b
    rw [e, spMap_comp₂, Category.assoc, P.nat]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun T ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg T]
    change (spMap (lr T) ≫ P.y (op T.1.2)) ≫ s = P'.y (op T.1.1) ≫ t
    rw [Category.assoc, P.base, P'.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (l (op T)).commutes r)
  · let 𝒱 : Z₀.OpenCover := Scheme.Cover.mkOfCovers (Pair f₀) (fun T ↦ Sp (GlobalTheory.CechDR.Sec t₀ T.1.1.1))
      (fun T ↦ affPt t₀ T.1.1)
      (fun z ↦ by
        obtain ⟨T, hT⟩ := hpt z
        obtain ⟨w, hw⟩ : z ∈ Set.range (affPt t₀ T.1.1) := T.1.1.2.range_fromSpec.ge hT
        exact ⟨T, w, hw⟩)
      (fun T ↦ IsAffineOpen.isOpenImmersion_fromSpec T.1.1.2)
    refine 𝒱.hom_ext _ _ fun T ↦ ?_
    change affPt t₀ T.1.1 ≫ k ≫ _ = affPt t₀ T.1.1 ≫ f₀ ≫ i
    rw [← Category.assoc, show affPt t₀ T.1.1 ≫ k = _ from (P'.red (op T.1.1)).symm, Category.assoc]
    change spMap (S'.p (op T.1.1)) ≫ 𝒰.f T ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg T]
    change spMap (S'.p (op T.1.1)) ≫ spMap (lr T) ≫ P.y (op T.1.2) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (S'.p (op T.1.1)).comp (lr T) = (GlobalTheory.CechDR.secPull s₀ t₀ T).comp (S.p (op T.1.2)) :=
      RingHom.ext fun b ↦ hL (op T) b
    rw [e, spMap_comp₂, Category.assoc, show spMap (S.p (op T.1.2)) ≫ P.y (op T.1.2) = affPt s₀ T.1.2 ≫ i from P.red _,
      ← Category.assoc, GlobalTheory.CechDR.secPull_affPt (φ := f₀) s₀ t₀ T, Category.assoc]

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePairPreimageBaseChangeFstIsBasis
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs.BC

theorem exists_affineOpen_nhds_le {X : Scheme.{0}} (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hx) W.isOpen
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

theorem pairBC_fst_basis : ∀ (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (e : f₁ ≫ pr = pr' ≫ f₀), (∀ U : Y₁.Opens, ∃ V : Y₀.Opens, pr' ⁻¹ᵁ V = U) → (∀ (x : Y₁) (U : Y₁.Opens), x ∈ U → ∃ t, x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t).unop.1 ≤ U) ∧ (∀ t₁ t₂ (x : Y₁) (U : Y₁.Opens), x ∈ U → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₁).unop.1 → x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₂).unop.1 → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ∧ ((GlobalTheory.Obs.BC.pairBC pr pr' e ⋙ pairFst f₁).obj t₃).unop.1 ≤ U) := by
  intro X₀ X₁ Y₀ Y₁ pr pr' _ _ f₀ f₁ e hsurj
  constructor
  · intro x U hx
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    obtain ⟨V, hfV, -⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) ⊤ trivial
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x) (W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨hy, hfV⟩
    refine ⟨Opposite.op (⟨(U', V), hU'le.trans inf_le_right⟩ : Pair f₀), ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans inf_le_left)
  · intro t₁ t₂ x U hx h₁ h₂
    obtain ⟨W₀, rfl⟩ := hsurj U
    have hy : pr' x ∈ W₀ := hx
    have hy₁ : pr' x ∈ t₁.unop.1.1.1 := h₁
    have hy₂ : pr' x ∈ t₂.unop.1.1.1 := h₂
    have hf₁ : f₀ (pr' x) ∈ t₁.unop.1.2.1 := t₁.unop.2 hy₁
    have hf₂ : f₀ (pr' x) ∈ t₂.unop.1.2.1 := t₂.unop.2 hy₂
    obtain ⟨V, hfV, hVle⟩ := exists_affineOpen_nhds_le (f₀ (pr' x)) (t₁.unop.1.2.1 ⊓ t₂.unop.1.2.1) ⟨hf₁, hf₂⟩
    obtain ⟨U', hU', hU'le⟩ := exists_affineOpen_nhds_le (pr' x)
      (t₁.unop.1.1.1 ⊓ t₂.unop.1.1.1 ⊓ W₀ ⊓ f₀ ⁻¹ᵁ V.1) ⟨⟨⟨hy₁, hy₂⟩, hy⟩, hfV⟩
    let p : Pair f₀ := ⟨(U', V), hU'le.trans inf_le_right⟩
    have hp₁ : p ≤ t₁.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)), hVle.trans inf_le_left⟩)
    have hp₂ : p ≤ t₂.unop := Subtype.coe_le_coe.1 (Prod.mk_le_mk.2
      ⟨hU'le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)), hVle.trans inf_le_right⟩)
    refine ⟨Opposite.op p, ⟨(homOfLE hp₁).op⟩, ⟨(homOfLE hp₂).op⟩, ?_, ?_⟩
    · show pr' x ∈ U'.1
      exact hU'
    · show pr' ⁻¹ᵁ U'.1 ≤ pr' ⁻¹ᵁ W₀
      exact pr'.preimage_mono (hU'le.trans (inf_le_left.trans inf_le_right))

end GlobalTheory.Obs.BC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem app_bijective_of_flat_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R)
    (p : Z ⟶ Y) (q : Z ⟶ S), QuasiCompact π → QuasiSeparated π → Function.Bijective π.appTop.hom → Flat y →
    IsPullback p q y π → ∀ V : Y.Opens, Function.Bijective (p.app V).hom := by
  intro R _ S Y Z π y p q hqc hqs hbij hy H V
  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hV : IsIso (p.app V) := GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens p (fun W ↦
    have : IsAffine W.1 := W.2
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
      ((isPullback_morphismRestrict p W.1).flip.paste_horiz H.flip)) V
  exact (ConcreteCategory.isIso_iff_bijective _).mp hV

end GlobalTheory.Mum
end

