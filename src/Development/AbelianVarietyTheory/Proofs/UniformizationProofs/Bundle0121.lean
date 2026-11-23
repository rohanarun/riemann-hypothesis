module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAlgebraizationGroupOperationsCdvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GrpAlg

theorem inv_one_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (∀ (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G), x₀.left = x.left ≫ φ →
      (x₀⁻¹).left = (x⁻¹).left ≫ φ) ∧
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) := MonoidHom.mk' F fun x y =>
    Over.OverMorphism.ext (h.2 T x y (F x) (F y) rfl rfl).symm
  refine ⟨fun x x₀ hx => ?_, congrArg (·.left) (map_one Φ).symm⟩
  obtain rfl : x₀ = Φ x := Over.OverMorphism.ext hx
  exact congrArg (·.left) (map_inv Φ x).symm

theorem exists_operation_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ r e)
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (W : Over S) (Z : ∀ e, Over (R e)) (w : ∀ e, (Z e).left ⟶ W.left)
    (hw : ∀ e, IsPullback (w e) (Z e).hom W.hom (s e)) (ζ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left)
    (hζ : ∀ e, ζ e ≫ (Z (e + 1)).hom = (Z e).hom ≫ r e) (hζw : ∀ e, ζ e ≫ w (e + 1) = w e)
    (ext : ∀ f : ∀ e, (Z e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w e ≫ W.hom) →
      (∀ e, ζ e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w e ≫ g.left = f e)
    (J : Type) (p : J → (W ⟶ B)) (op : ∀ e (T : Over (R e)), (J → (T ⟶ Y e)) → (T ⟶ Y e))
    (nat : ∀ e T T' (t : T' ⟶ T) (x : J → (T ⟶ Y e)), t ≫ op e T x = op e T' fun i => t ≫ x i)
    (cmp : ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (x₀ : J → (Over.mk (T.hom ≫ r e) ⟶ Y (e + 1))),
      (∀ i, (x₀ i).left = (x i).left ≫ β e) → (op (e + 1) _ x₀).left = (op e T x).left ≫ β e) :
    ∃ g : W ⟶ B, ∀ e (T : Over (R e)) (x : J → (T ⟶ Y e)) (t : Over.mk (T.hom ≫ s e) ⟶ W),
      (∀ i, (t ≫ p i).left = (x i).left ≫ b e) → (t ≫ g).left = (op e T x).left ≫ b e := by
  have hp : ∀ e i, (w e ≫ (p i).left) ≫ B.hom = (Z e).hom ≫ s e :=
    fun e i => by rw [Category.assoc, Over.w (p i), (hw e).w]
  obtain ⟨X, hX⟩ : ∃ X : ∀ e, J → (Z e ⟶ Y e), ∀ e i, (X e i).left ≫ b e = w e ≫ (p i).left :=
    ⟨fun e i => Over.homMk ((hb e).lift _ _ (hp e i)) ((hb e).lift_snd _ _ _),
      fun e i => (hb e).lift_fst _ _ (hp e i)⟩
  obtain ⟨g, hg⟩ := ext (fun e => (op e _ (X e)).left ≫ b e)
    (fun e => by rw [Category.assoc, (hb e).w, ← Category.assoc, Over.w (op e _ (X e)), (hw e).w])
    (fun e => by
      obtain ⟨tr, h₁⟩ : ∃ tr : Over.mk ((Z e).hom ≫ r e) ⟶ Z (e + 1), tr.left = ζ e :=
        ⟨Over.homMk (ζ e) (hζ e), rfl⟩
      have h₂ := cmp e _ (X e) (fun i => tr ≫ X (e + 1) i) fun i => by
        apply (hb (e + 1)).hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, hX, hβb, hX, ← Category.assoc, h₁]
          exact congrArg (· ≫ (p i).left) (hζw e)
        · rw [Over.w, Category.assoc, hβ, ← Category.assoc, Over.w (X e i)]
          rfl
      rw [← nat, Over.comp_left, h₁] at h₂
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ b (e + 1)) h₂).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (hβb e)))))
  refine ⟨g, fun e T x t ht => ?_⟩
  obtain ⟨t', h₁⟩ : ∃ t' : T ⟶ Z e, t'.left ≫ w e = t.left :=
    ⟨Over.homMk ((hw e).lift t.left T.hom (Over.w t)) ((hw e).lift_snd _ _ _),
      (hw e).lift_fst _ _ (Over.w t)⟩
  have h₂ : x = fun i => t' ≫ X e i := funext fun i => Over.OverMorphism.ext <| by
    apply (hb e).hom_ext
    · rw [← ht, Over.comp_left, Over.comp_left, Category.assoc, hX, ← Category.assoc, h₁]
    · rw [Over.w, Over.w]
  rw [h₂, ← nat, Over.comp_left, Over.comp_left, Category.assoc, ← hg e, ← Category.assoc, h₁]

theorem exists_group_operations_of_extend {S : Scheme.{0}} {R : ℕ → Scheme.{0}} (s : ∀ e, R e ⟶ S)
    (r : ∀ e, R e ⟶ R (e + 1)) (Y : ∀ e, Over (R e)) [∀ e, GrpObj (Y e)]
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsGrpPullback (Y e) (Y (e + 1)) (r e) (β e))
    (B : Over S) (b : ∀ e, (Y e).left ⟶ B.left) (hb : ∀ e, IsPullback (b e) (Y e).hom B.hom (s e))
    (hβb : ∀ e, β e ≫ b (e + 1) = b e)
    (Z : Over S → ∀ e, Over (R e)) (w : ∀ W e, (Z W e).left ⟶ W.left)
    (hw : ∀ W e, IsPullback (w W e) (Z W e).hom W.hom (s e))
    (ζ : ∀ W e, (Z W e).left ⟶ (Z W (e + 1)).left)
    (hζ : ∀ W e, ζ W e ≫ (Z W (e + 1)).hom = (Z W e).hom ≫ r e)
    (hζw : ∀ W e, ζ W e ≫ w W (e + 1) = w W e) (P : Over S → Prop)
    (ext : ∀ W, P W → ∀ f : ∀ e, (Z W e).left ⟶ B.left, (∀ e, f e ≫ B.hom = w W e ≫ W.hom) →
      (∀ e, ζ W e ≫ f (e + 1) = f e) → ∃ g : W ⟶ B, ∀ e, w W e ≫ g.left = f e)
    (h₂ : P (B ⊗ B)) (h₁ : P B) (h₀ : P (𝟙_ _)) :
    ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (R e)) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ s e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ s e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  have key := fun W hW => exists_operation_of_extend s r Y β (fun e => (hβ e).1.w) B b hb hβb W (Z W) (w W)
    (hw W) (ζ W) (hζ W) (hζw W) (ext W hW)
  obtain ⟨mu, hmu⟩ := key _ h₂ Bool (fun i => cond i (fst B B) (snd B B))
    (fun _ _ x => x true * x false) (fun _ _ _ t x => comp_mul _ _ _)
    (fun e T x x₀ h => (hβ e).2 T _ _ _ _ (h true) (h false))
  obtain ⟨io, hio⟩ := key _ h₁ Unit (fun _ => 𝟙 B) (fun _ _ x => (x ())⁻¹)
    (fun _ _ _ t x => GrpObj.comp_inv _ _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).1 _ _ (h ()))
  obtain ⟨un, hun⟩ := key _ h₀ Empty Empty.elim (fun _ _ _ => 1) (fun _ _ _ t x => comp_one _)
    (fun e T x x₀ h => (inv_one_of_isGrpPullback (hβ e) T).2)
  refine ⟨mu, io, un, fun e T x y x₀ y₀ hx hy => ⟨?_, ?_, ?_⟩⟩
  · refine hmu e T (fun i => cond i x y) _ fun i => ?_
    cases i
    · exact (congrArg (·.left) (lift_snd x₀ y₀)).trans hy
    · exact (congrArg (·.left) (lift_fst x₀ y₀)).trans hx
  · exact hio e T (fun _ => x) _ fun _ => (congrArg (·.left) (Category.comp_id x₀)).trans hx
  · exact hun e T Empty.elim _ fun i => i.elim

theorem isPullback_fstG {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    IsPullback (P := (thickObj R I e W).left) (fstG I e W).left (thickObj R I e W).hom W.hom (thick R I e) :=
  IsPullback.of_hasPullback W.hom (thick R I e)

theorem thickMap_hom {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (thickObj R I (e + 1) W).hom = (thickObj R I e W).hom ≫ thickTrans R I e :=
  pullback.lift_snd _ _ _

theorem thickMap_proj {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (W : Over (Spec (CommRingCat.of R))) :
    thickMap R I e W ≫ (fstG I (e + 1) W).left = (fstG I e W).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end GlobalTheory.GrpAlg

theorem GlobalTheory.GrpAlg.exists_group_operations : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsGrpPullback (Y e) (Y (e + 1)) (thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∃ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) := by
  intro V _ _ _ _ Y _ β hβ B b hB hfl hb hβb
  have hfl₂ : Flat (B ⊗ B).hom := by
    change Flat (pullback.fst B.hom B.hom ≫ B.hom)
    infer_instance
  exact GlobalTheory.GrpAlg.exists_group_operations_of_extend (S := Spec (CommRingCat.of V))
    (R := fun e => Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))
    (thick V (IsLocalRing.maximalIdeal V)) (thickTrans V (IsLocalRing.maximalIdeal V)) Y β hβ B b hb hβb
    (fun W e => thickObj V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => (fstG (IsLocalRing.maximalIdeal V) e W).left)
    (fun W e => GlobalTheory.GrpAlg.isPullback_fstG _ e W) (fun W e => thickMap V (IsLocalRing.maximalIdeal V) e W)
    (fun W e => GlobalTheory.GrpAlg.thickMap_hom _ e W) (fun W e => GlobalTheory.GrpAlg.thickMap_proj _ e W)
    (fun W => IsProjBy W.hom ∧ Flat W.hom) (fun W hW => GlobalTheory.MorAlg.exists_hom_of_thickenings V W B hW.1 hB hW.2)
    ⟨isProjBy_tensor V B B hB hB, hfl₂⟩ ⟨hB, hfl⟩
    ⟨isProjBy_id V, inferInstanceAs (Flat (𝟙 (Spec (CommRingCat.of V))))⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleGeneratingSectionsAllThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_generatingSections_all_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  first | exact @GlobalTheory.SecTower.exists_tower | exact GlobalTheory.SecTower.exists_tower | (intros; apply GlobalTheory.SecTower.exists_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlg

variable {X Y Z : Scheme.{0}}

theorem gm_tw (A H : LB X) (t : ℤ) (r : Z ⟶ X) (z : Z) (p q : A.ι × H.ι)
    (hm : r z ∈ A.U p.1 ⊓ H.U p.2 ⊓ (A.U q.1 ⊓ H.U q.2)) :
    gm r z ((tw A H t).U p ⊓ (tw A H t).U q) ((tw A H t).g p q) =
      gm r z _ (A.g p.1 q.1) * gm r z _ (H.g p.2 q.2) ^ t := by
  refine (gm_div (AbLaw.pw H (-t)) A r z p q hm).trans ?_
  refine congrArg _ ((congrArg (·⁻¹) (map_zpow _ _ _)).trans ?_)
  rw [zpow_neg, inv_inv]
  rfl

theorem lbIso_of_germs {A B : LB X} (s : ∀ p : B.ι × A.ι, Γ(X, B.U p.1 ⊓ A.U p.2)ˣ)
    (h : ∀ (x : X) (p q : B.ι × A.ι), x ∈ B.U p.1 → x ∈ A.U p.2 → x ∈ B.U q.1 → x ∈ A.U q.2 →
      gm (𝟙 X) x _ (s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (s q)) :
    LBIso A B := by
  refine ⟨⟨s⟩, fun p q => unit_ext fun x hx => ?_⟩
  exact (gm_res _ x _ hx _).trans ((h x p q hx.1.1 hx.1.2 hx.2.1 hx.2.2).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))).symm)

theorem germs_of_isGen {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (h₁ : x ∈ B.U p.1) (h₂ : x ∈ A.U p.2) (h₃ : x ∈ B.U q.1) (h₄ : x ∈ A.U q.2) :
    gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2) (w.s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ *
      gm (𝟙 X) x (B.U q.1 ⊓ A.U q.2) (w.s q) := by
  have hx : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  exact (gm_res _ x _ hx _).symm.trans ((congrArg (gm (𝟙 X) x _) (hw p q)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))))

theorem lbIso_self {A : LB X} (hA : A.IsLB) : LBIso A A := by
  refine lbIso_of_germs (fun p => A.g p.1 p.2) fun x p q h₁ h₂ h₃ h₄ => ?_
  rw [← gm_cocycle hA (𝟙 X) x h₁ h₂ h₃, ← gm_cocycle hA (𝟙 X) x h₂ h₃ h₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def chartPullTw {A' H' : LB Y} {A H : LB X} {h : Y ⟶ X} (a : ChartPull A' A h) (b : ChartPull H' H h) (t : ℤ) :
    ChartPull (tw A' H' t) (tw A H t) h where
  idx p := (a.idx p.1, b.idx p.2)
  le p y hy := ⟨a.le _ hy.1, b.le _ hy.2⟩
  g y p q hp hq := by
    refine (gm_tw A' H' t (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_ (gm_tw A H t h y (a.idx p.1, b.idx p.2)
      (a.idx q.1, b.idx q.2) ⟨⟨a.le _ hp.1, b.le _ hp.2⟩, a.le _ hq.1, b.le _ hq.2⟩).symm)
    rw [a.g y _ _ hp.1 hq.1, b.g y _ _ hp.2 hq.2]

theorem lbIso_tw_congr {A B H : LB X} (hH : H.IsLB) (t : ℤ) (h : LBIso A B) : LBIso (tw A H t) (tw B H t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ B.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ H.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (B.ι × H.ι) × (A.ι × H.ι)), x ∈ (tw B H t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t) =
        gm (𝟙 X) x (B.U p.1.1 ⊓ A.U p.2.1) (w.s (p.1.1, p.2.1)) * gm (𝟙 X) x _ (H.g p.1.2 p.2.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (gm_tw B H t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [germs_of_isGen hw x (p.1.1, p.2.1) (q.1.1, q.2.1) h₁.1 h₂.1 h₃.1 h₄.1,
    ← gm_cocycle hH (𝟙 X) x h₁.2 h₂.2 h₃.2, ← gm_cocycle hH (𝟙 X) x h₂.2 h₃.2 h₄.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem lbIso_tw_tw {A H : LB X} (hA : A.IsLB) (hH : H.IsLB) (t : ℤ) : LBIso A (tw (tw A H t) H (-t)) := by
  have l₁ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ A.U p.1.1.1 ⊓ A.U p.2 :=
    fun p x hx => ⟨hx.1.1.1, hx.2⟩
  have l₂ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ H.U p.1.1.2 ⊓ H.U p.1.2 :=
    fun p x hx => ⟨hx.1.1.2, hx.1.2⟩
  have v : ∀ (x : X) (p : ((A.ι × H.ι) × H.ι) × A.ι), x ∈ (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1.1 p.2) * gm (𝟙 X) x _ (H.g p.1.1.2 p.1.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (· * _)
    ((gm_tw (tw A H t) H (-t) (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩).trans (congrArg (· * _)
      (gm_tw A H t (𝟙 X) x p.1.1 q.1.1 ⟨h₁.1, h₃.1⟩)))) (v x q ⟨h₃, h₄⟩)).symm)
  rw [← gm_cocycle hA (𝟙 X) x h₁.1.1 h₂ h₃.1.1, ← gm_cocycle hA (𝟙 X) x h₂ h₃.1.1 h₄,
    ← gm_cocycle hH (𝟙 X) x h₁.1.2 h₁.2 h₃.1.2, ← gm_cocycle hH (𝟙 X) x h₁.2 h₃.1.2 h₃.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem surjective_thickTrans (V : Type) [CommRing V] (I : Ideal V) (e : ℕ) : Surjective (thickTrans V I e) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := (GlobalTheory.SecLifts.mk_mem_ker_factor _ a).1 ha
    have h2 : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have := Ideal.pow_mem_pow ha' 2
      rw [← pow_mul] at this
      exact Ideal.pow_le_pow_right (by omega) this
    exact x.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  exact h


open GlobalTheory.MorAlg in
theorem exists_lineBundle_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro V _ _ _ _ Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull (b 0) hH σ
  have hva : VeryAmpleBy (Y 0).hom (H.pull (b 0)) σ₀ := by
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V B.left B.hom H m σ hH hσ _
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (b 0) (hb 0).w ?_ _ w₀ _ (hL 0) hw₀ c₀
    have e : pullback.lift (b 0) (Y 0).hom (hb 0).w = (hb 0).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    rw [e]
    infer_instance
  obtain ⟨t₁, ht₁⟩ := _root_.GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hflY
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) (ht₁ t h₁) (u j)
  have hcov : ∀ e, ⨆ j, nonzeroLocus (s j e) = ⊤ := by
    intro e
    induction e with
    | zero => simpa only [hs0] using hu
    | succ e ih =>
      have hsurj : Surjective (β e) :=
        MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans V _ e)
      refine top_le_iff.1 fun y _ => ?_
      obtain ⟨x, rfl⟩ := hsurj.surj y
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ j, nonzeroLocus (s j e) by rw [ih]; trivial)
      rw [(GlobalTheory.SecPullIso.section_pull _ _ (β e) _ _ (v' e) (hT (e + 1)) (hT e) (hv' e) (s j (e + 1))).2 _
        (hs j e)] at hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨P, p, O, x, hO, hx, heq⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n ⊥ (by
    intro F hF d
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose φ w hφ hw cw using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V P p O n x hO hx (Y e).left
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) _ (fun j => s j e) (hT e) (hcov e) (by
      intro d F hF h0 k
      obtain ⟨i, hi⟩ := (heq d F hF).1 h0 0
      rw [Ideal.mem_bot, mul_eq_zero] at hi
      rw [hi.resolve_left (pow_ne_zero _ (MvPolynomial.X_ne_zero _)), map_zero])
  have hφc : ∀ e, β e ≫ φ (e + 1) = φ e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp (s := x) (s' := fun j => s j (e + 1)) (s'' := fun j => s j e)
      hO (hT (e + 1)) (hT e) ⟨w (e + 1), hw (e + 1), cw (e + 1)⟩ ⟨v' e, hv' e, fun j => hs j e⟩
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P p O n x hO hx _ _ (fun j => s j e) _ _ w₁ (w e) (hT e) ?_
      hw₁ (hw e) c₁ (cw e)
    rw [Category.assoc, hφ, hφ, ← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hi : ∀ e, (hb e).isoPullback.inv ≫ β e =
      thickMap V (IsLocalRing.maximalIdeal V) e B ≫ (hb (e + 1)).isoPullback.inv := fun e => by
    apply (hb (e + 1)).hom_ext
    · rw [Category.assoc, Category.assoc, hc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_inv_fst]
      exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
    · rw [Category.assoc, Category.assoc, (hβ e).w, IsPullback.isoPullback_inv_snd_assoc,
        IsPullback.isoPullback_inv_snd]
      exact (pullback.lift_snd _ _ _).symm
  obtain ⟨g, hg⟩ := exists_hom_of_thickenings V B (Over.mk p) hB ⟨O, hO, n, x, hx⟩ hfl
    (fun e => (hb e).isoPullback.inv ≫ φ e) (fun e => by
      refine (Category.assoc _ _ _).trans ((congrArg _ (hφ e)).trans ?_)
      rw [IsPullback.isoPullback_inv_snd_assoc]
      exact pullback.condition.symm) (fun e => by
      rw [← hφc e]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ (e + 1)) (hi e).symm).trans
        (Category.assoc _ _ _)))
  let g' : B.left ⟶ P := g.left
  have hbg : ∀ e, φ e = b e ≫ g' := fun e => by
    have h : pullback.fst B.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g' = (hb e).isoPullback.inv ≫ φ e := hg e
    rw [← (hb e).isoPullback_hom_fst, Category.assoc, h, Iso.hom_inv_id_assoc]
  have hM : (tw (O.pull g') H (-t)).IsLB := isLB_tw (pull_isLB hO _) hH _
  refine ⟨tw (O.pull g') H (-t), hM, fun e => ?_⟩
  have hO' : (tw (O.pull (φ e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hO _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) ⟨w e, hw e⟩))
    (LBIso.chartPull (chartPullTw (chartPullSame O _ _ _ (b e) fun _ => hbg e) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM))

end GlobalTheory.LBAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMorphismToProjectiveOfRankOneSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RankMap

theorem exists_hom_of_rank_one : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (f : Z ⟶ Spec (CommRingCat.of R)) (H : LB Z) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X : Scheme.{0}) (f' : X ⟶ Spec (CommRingCat.of R)) (N : LB X) (m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → (∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ k, MvPolynomial.eval₂Hom (cst f (H.U k)) (fun i => (s i).f k) F = 0) → ∀ j k, MvPolynomial.eval₂Hom (cst f' (N.U k)) (fun i => (w i j).f k) F = 0) → ∃ φ : X ⟶ Z, φ ≫ f = f' ∧ ∀ (T : Scheme.{0}) (r : T ⟶ X) (ψ : T ⟶ Z), ψ ≫ f = r ≫ f' → (∀ z k k' i i' j, ψ z ∈ H.U k → r z ∈ N.U k' → gs ψ z (H.U k) ((s i).f k) * gs r z (N.U k') ((w i' j).f k') = gs ψ z (H.U k) ((s i').f k) * gs r z (N.U k') ((w i j).f k')) → r ≫ φ = ψ := by
  intro R _ Z f H n s hH hs X f' N m w hN hw hr he
  obtain ⟨H', s', hH', hs', hv⟩ := GlobalTheory.RankBundle.exists_rank_one_bundle X N n m w hN hw hr
  obtain ⟨φ, u, hφ, -, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R Z f H n s hH hs X f' H' s' hH' hs'
    fun t F hF h0 c => by
      refine fn_ext fun x hx => ?_
      obtain ⟨j, hj⟩ := hv x c hx
      obtain ⟨k, hk⟩ := exists_chart hN x
      obtain ⟨v, hvi⟩ := hj k hk
      have e := congrArg (gs (𝟙 X) x _) (he t F hF h0 j k)
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hk, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero] at e
      simp only [hvi] at e
      rw [MorAlg.eval₂_scale _ _ _ hF] at e
      rw [MorAlg.gs_eval f' (𝟙 X) x _ hx, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]
      exact ((Units.isUnit _).pow t).mul_right_eq_zero.1 e
  refine ⟨φ, hφ, fun T r ψ hψ hp => ?_⟩
  refine GlobalTheory.ProjUniq.hom_eq_of_proportional R Z f H n s hH hs T _ _
    (by rw [Category.assoc, hφ, hψ]) fun z k k' i i' hk hk' => ?_
  obtain ⟨c, hc⟩ := exists_chart hH' (r z)
  obtain ⟨d, hd⟩ := exists_chart hN (r z)
  obtain ⟨j, hj⟩ := hv (r z) c hc
  obtain ⟨v, hvi⟩ := hj d hd
  have hu : IsUnit ((r.stalkMap z).hom v.val) := v.isUnit.map _
  have e : ∀ l, gs r z (N.U d) ((w l j).f d) =
      (r.stalkMap z).hom v.val * gs r z (H'.U c) ((s' l).f c) := fun l => by
    have e := congrArg (r.stalkMap z).hom (hvi l)
    rwa [map_mul, MorAlg.gs_stalk r (𝟙 X) z _ hd, MorAlg.gs_stalk r (𝟙 X) z _ hc, Category.comp_id] at e
  have q := hp z k' d i i' j hk' hd
  rw [e, e] at q
  rw [MorAlg.Carries.at (w := u) cu r i z k c hk hc, MorAlg.Carries.at (w := u) cu r i' z k c hk hc]
  refine hu.mul_left_cancel ?_
  linear_combination (-(Geo.Tor.gw u r z k c).val) * q

end GlobalTheory.RankMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pullback_section_endomorphism : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  first | exact @GlobalTheory.UT.PullExp.main | exact GlobalTheory.UT.PullExp.main | (intros; apply GlobalTheory.UT.PullExp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtDvrAndLaws
section
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory

theorem homExtDvr_and_laws : Out.HomExtDvrSt ∧ Out.Laws7 := by
  have h : Out.HomExtDvrSt := fun T _ _ _ G G' _ _ hG hG' φ hφ =>
    GlobalTheory.existsUnique_hom_extension_semiAbelian T (FractionRing T) G G' hG hG' φ hφ
  exact ⟨h, ⟨h⟩⟩

end GlobalTheory
end

