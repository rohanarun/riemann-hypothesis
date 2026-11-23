module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvForm

variable {R : Type} [CommRing R]

section Val

variable {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]

abbrev redHom (φ : B →ₐ[R] DualNumber D) : B →+* D :=
  (TrivSqZeroExt.fstHom R D D).toRingHom.comp φ.toRingHom

theorem redHom_algebraMap (φ : B →ₐ[R] DualNumber D) (r : R) :
    redHom φ (algebraMap R B r) = algebraMap R D r := by
  simp [redHom, TrivSqZeroExt.algebraMap_eq_inl']

def dVal (φ : B →ₐ[R] DualNumber D) : Ω[B⁄R] →ₗ[R] D :=
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  let d : Derivation R B D :=
    { toFun := fun b ↦ (φ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        rw [map_smul, TrivSqZeroExt.snd_smul]
        rfl
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (φ (a * b)).snd = (φ a).fst * (φ b).snd + (φ b).fst * (φ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  d.liftKaehlerDifferential.restrictScalars R

theorem dVal_D (φ : B →ₐ[R] DualNumber D) (b : B) : dVal φ (KaehlerDifferential.D R B b) = (φ b).snd := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact Derivation.liftKaehlerDifferential_comp_D _ b

end Val

variable (A : Over (Sp R)) [GrpObj A]

def IsInv (w : GlobForm A.hom) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (U V : A.left.affineOpens)
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) (ψ : Sec A.hom V.1 →ₐ[R] DualNumber D)
    (p q : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ A) (q₀ : Sp D ⟶ A.left),
    p.left = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U →
    q.left = spMap (algebraMap D (DualNumber D)) ≫ q₀ →
    (p * q).left = spMap (ψ : Sec A.hom V.1 →+* DualNumber D) ≫ affPt A.hom V →
    dVal φ (w.1 (op U)) = dVal ψ (w.1 (op V))

def InvForm : Submodule R (GlobForm A.hom) where
  carrier := {w | IsInv A w}
  add_mem' {w w'} hw hw' D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (w.1 (op U) + w'.1 (op U)) = dVal ψ (w.1 (op V) + w'.1 (op V))
    rw [map_add (f := _), map_add (f := _), hw D U V φ ψ p q q₀ hp hq hpq, hw' D U V φ ψ p q q₀ hp hq hpq]
  zero_mem' D _ _ U V φ ψ p q q₀ _ _ _ := by
    change dVal φ 0 = dVal ψ 0
    rw [map_zero, map_zero]
  smul_mem' r w hw D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (r • w.1 (op U)) = dVal ψ (r • w.1 (op V))
    rw [map_smul, map_smul, hw D U V φ ψ p q q₀ hp hq hpq]

end GlobalTheory.InvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem rescale_tau_val {R' : Type} [CommRing R'] [IsDomain R'] (D : DegPre R') (g : D.X → (FractionRing R')ˣ)
    (a b : D.X) {z : (TK R').left} {J : ((TK R').left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val ((rescale D g).tau a b) (𝟙 _) z J =
      gm (𝟙 (TK R').left) z ⊤ (unitOn (g (a + b))) * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g a)))⁻¹ *
        (gm (𝟙 (TK R').left) z ⊤ (unitOn (g b)))⁻¹ * val (D.tau a b) (𝟙 _) z J := by
  have hJ' : Good (rescale D g).P.L z J := hJ
  unfold DegPre.tau
  simp only [val_mul hJ', val_mul hJ, val_inv]
  erw [val_inv, val_inv, val_inv]
  have e1 : ∀ χ, val ((rescale D g).psi χ) (𝟙 _) z J = gm (𝟙 (TK R').left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 _) z J :=
    fun χ => GlobalTheory.UU.val_scaleGen _ _ _ hJ
  have e2 : val (rescale D g).rigK (𝟙 _) z J = val D.rigK (𝟙 _) z J := rfl
  erw [e1 (a + b), e1 a, e1 b, e2]
  simp only [mul_inv]
  ac_rfl

theorem half_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  intro R _ _ R' _ _ Q ρ D e f f' g h hf
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have H := h₆ κ hκ a b z J J' hJ hJ'
  have E := rescale_tau_val D g a b hJ'
  have key : ∀ x y : D.X, gm (𝟙 (TK R').left) z ⊤ (unitOn (f x y)) = gm (𝟙 (TK R').left) z ⊤ (unitOn (g (x + y))) *
      (gm (𝟙 (TK R').left) z ⊤ (unitOn (g x)))⁻¹ * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g y)))⁻¹ *
        gm (𝟙 (TK R').left) z ⊤ (unitOn (f' x y)) := fun x y => by
    rw [hf x y]; simp only [unitOn, map_mul, map_inv]
  erw [E]
  refine Eq.trans ?_ H
  erw [key a b]
  ac_rfl

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.StalkMap

variable {X : Scheme.{0}}

theorem top_le_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem appLE_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (top_le_fromSpecStalk x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (top_le_fromSpecStalk x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

def val {R : Type} [CommRing R] (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem val_congr {R : Type} [CommRing R] {g g' : Sp R ⟶ X} (e : g = g') (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(X, V)) : val g V h u = val g' V h' u := by
  subst e; rfl

theorem val_gp [IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) (h : ⊤ ≤ gp X ⁻¹ᵁ V) (u : Γ(X, V)) :
    val (gp X) V h u = GlobalTheory.Cartier.fnOf V hV u := by
  have : (gp X).appLE V ⊤ h = X.presheaf.germ V _ hV ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv :=
    appLE_fromSpecStalk (genericPoint X) V hV
  unfold val
  rw [RingHom.comp_apply, this]
  exact (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv_hom_id_apply _

end GlobalTheory.Desc.StalkMap

namespace GlobalTheory.Desc.StalkMap

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem val_appLE (g : Sp R ⟶ X) (φ : X ⟶ X') (V : X'.Opens) (W : X.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(X', V)) :
    val g W h ((φ.appLE V W e).hom u) = val (g ≫ φ) V h' u :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u))
    (Scheme.Hom.appLE_comp_appLE g φ V W ⊤ e h)

theorem val_top (g : Sp R ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(X, ⊤)) :
    val g ⊤ h u = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  have : g.appLE ⊤ ⊤ h = g.appTop := Scheme.Hom.appLE_eq_app g
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u)) this

theorem val_spMap (σ : R →+* R') (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ (spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(X, V)) : val (spMap σ ≫ g) V h' u = σ (val g V h u) := by
  refine (val_appLE (spMap σ) g V ⊤ h le_top h' u).symm.trans ((val_top (spMap σ) le_top _).trans ?_)
  exact congrArg (fun q => CommRingCat.Hom.hom q ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem fnOf_app_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField) (hm : gp Y ≫ m = spMap φ ≫ gp P) {W : P.Opens}
    (hY : genericPoint Y ∈ m ⁻¹ᵁ W) (hP : genericPoint P ∈ W) (s : Γ(P, W)) :
    GlobalTheory.Cartier.fnOf (m ⁻¹ᵁ W) hY ((m.app W).hom s) = φ (GlobalTheory.Cartier.fnOf W hP s) := by
  have h1 : ⊤ ≤ gp Y ⁻¹ᵁ (m ⁻¹ᵁ W) := top_le_fromSpecStalk _ _ hY
  have h2 : ⊤ ≤ gp P ⁻¹ᵁ W := top_le_fromSpecStalk _ _ hP
  have h3 : ⊤ ≤ (gp Y ≫ m) ⁻¹ᵁ W := h1
  have h4 : ⊤ ≤ (spMap φ ≫ gp P) ⁻¹ᵁ W := hm ▸ h3
  rw [← val_gp _ hY h1, ← val_gp _ hP h2, ← val_spMap φ (gp P) W h2 h4,
    ← val_congr hm W h3 h4, ← val_appLE (gp Y) m W (m ⁻¹ᵁ W) le_rfl h1 h3, Scheme.Hom.app_eq_appLE]

end GlobalTheory.Desc.StalkMap


open GlobalTheory.Desc.StalkMap in
theorem GlobalTheory.Desc.regAt_map_of_gp : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField),
    RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  intro Y P _ _ m φ hm y v hv
  obtain ⟨W, hW, s, rfl⟩ := hv.exists_fnOf
  have hy : y ∈ m ⁻¹ᵁ W := hW
  have hY : genericPoint Y ∈ m ⁻¹ᵁ W := gen_mem hy
  rw [← fnOf_app_eq m φ hm hY (gen_mem hW) s]
  refine ⟨regAt_fnOf hy hY _, ?_⟩
  rw [unitAt_fnOf_iff hy hY, unitAt_fnOf_iff hW (gen_mem hW), ← Scheme.preimage_basicOpen]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.RegPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem germ_gp (V : Y.Opens) (hY : genericPoint Y ∈ V) (h : gp Y (closedPoint _) ∈ V) :
    Y.presheaf.germ V (gp Y (closedPoint _)) h ≫ Scheme.stalkClosedPointTo (gp Y) =
      Y.presheaf.germ V (genericPoint Y) hY := by
  have hC : ∀ G : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ Y,
      G = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) → ∀ h,
      Y.presheaf.germ V (G (closedPoint _)) h ≫ Scheme.stalkClosedPointTo G =
        Y.presheaf.germ V (genericPoint Y) hY ≫ 𝟙 _ := by
    rintro G rfl h
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 _) V h
  have e : gp Y = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [Spec.map_id, Category.id_comp]; rfl
  exact (hC (gp Y) e h).trans (Category.comp_id _)

theorem fnOf_map (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField)
    (e : gp Y ≫ π = spMap θ ≫ gp X) (U : X.Opens) (hX : genericPoint X ∈ U)
    (hY : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hX s) = fnOf (π ⁻¹ᵁ U) hY (π.app U s) := by
  have hA : ∀ F : Sp Y.functionField ⟶ X, F = spMap θ ≫ gp X → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        X.presheaf.germ U (genericPoint X) hX ≫ CommRingCat.ofHom θ := by
    rintro F rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU
  have hg : gp Y (closedPoint _) = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hV : gp Y (closedPoint _) ∈ π ⁻¹ᵁ U := by rw [hg]; exact hY
  have hB : ∀ F : Sp Y.functionField ⟶ X, F = gp Y ≫ π → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hY := by
    rintro F rfl hU
    rw [Scheme.stalkClosedPointTo_comp]
    refine (Scheme.Hom.germ_stalkMap_assoc π U (gp Y (closedPoint _)) hV _).trans ?_
    exact congrArg (π.app U ≫ ·) (germ_gp (π ⁻¹ᵁ U) hY hV)
  have := (hA _ e hV).symm.trans (hB _ rfl hV)
  exact congrArg (fun g => g.hom s) this

theorem regAt_map (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (θ : X.functionField →+* Y.functionField) (hθ : PFF (𝟙 _) π θ) (y : Y) (u : X.functionField)
    (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨l, hl, e⟩ := hθ
  rw [Category.comp_id] at hl
  subst hl
  obtain ⟨U, hx, s, rfl⟩ := hu.exists_fnOf
  have hy : y ∈ π ⁻¹ᵁ U := hx
  rw [fnOf_map π θ e U _ (gen_mem hy) s]
  exact regAt_fnOf hy _ _

end GlobalTheory.Desc.RegPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem rescale_psiEven : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ),
    EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  intro R _ _ D h eta hD hadd hsq
  have h0 : eta 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have key : ∀ χ : D.X, eta (-χ) * h χ = eta χ := fun χ => by
    rw [← hsq, pow_two, ← _root_.mul_assoc, ← hadd, neg_add_cancel, h0, _root_.one_mul]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul _ a b
  refine fun (χ : D.X) => corr_of_val D.P.isLB fun y J hJ => ?_
  show val (LB.mulGen D.P.L _ _ _ _ (GlobalTheory.UU.scaleGen (unitOn (eta (-χ))) (D.psi (-χ)))
      (LB.pullGen D.P.L _ _ D.sym (D.xK χ))) (𝟙 _) y J = val (GlobalTheory.UU.scaleGen (unitOn (eta χ)) (D.psi χ)) (𝟙 _) y J
  refine (val_mul hJ _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen _ _ _ hJ)
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val D.sym r y J) (Category.id_comp _)))).trans ?_
  refine (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) (hD χ y J hJ)).trans ?_)
  refine (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) ((map_mul _ _ _).symm.trans
    (congrArg (gm _ y ⊤) ((hu _ _).symm.trans (congrArg unitOn (key χ)))))).trans (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{0}}

def RosatiFor (D : Datum p) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left) : Prop :=
  ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

def EtaOK (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (eta : D.La → (𝟙_ (Over S) ⟶ A)) :
    Prop :=
  (∀ x y, eta (x + y) = eta x * eta y) ∧ (∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c) ∧ ∀ x, eta (N • x) = 1

def GeomAt (D : Datum p) (N : ℕ) {A : Over S} [GrpObj A] (act : OActN D.O A) (P : LB (G2 A).left)
    (eta : D.La → (𝟙_ (Over S) ⟶ A)) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
      (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ eta y = I.ev N y

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {s : S ⟶ Sp R}

theorem Obj.rosatiFor (o : Obj b N s) : RosatiFor D o.act o.P := o.rosati

theorem Obj.etaOK (o : Obj b N s) : EtaOK D N o.act o.eta := ⟨o.eta_add, o.eta_lin, o.eta_ker⟩

theorem Obj.geomAt (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k)
    (hx : x ≫ s = spMap β) : GeomAt D N o.act o.P o.eta k x := o.geom k x β hx

theorem Obj.lieHer (o : Obj b N s) (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S)
    (hx : x ≫ s = spMap β) : LieHer b o.act β x := by
  intro R'' _ g
  have e₁ : (spMap g ≫ x) ≫ s = spMap (g.comp β) := by
    rw [Category.assoc, hx]
    simp [spMap, ← Spec.map_comp]
    try rfl
  refine ⟨o.lie R'' (g.comp β) (spMap g ≫ x) e₁, fun k _ _ g' i => ?_⟩
  refine o.lieRank k (spMap g' ≫ spMap g ≫ x) (g'.comp (g.comp β)) ?_ i
  rw [Category.assoc, Category.assoc, hx]
  simp [spMap, ← Spec.map_comp]
  try rfl

theorem RosatiFor.of_iso {A : Over S} [GrpObj A] {act : OActN D.O A} {P P' : LB (G2 A).left} (hP : P.IsLB)
    (hP' : P'.IsLB) (H : LBIso P P') (h : RosatiFor D act P) : RosatiFor D act P' := fun c =>
  LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB hP' _)
    (GlobalTheory.RigidBundleGlue.LBIso.pull H _).symm
    (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB hP' _) (h c) (GlobalTheory.RigidBundleGlue.LBIso.pull H _))

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsFromGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem semiAbelian_hom_extend_generic : ∀ (E : Type) [CommRing E] [IsDomain E] [IsNoetherianRing E] [IsIntegrallyClosed E]
    (G H : Over (Sp E)) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H →
    ∀ f : (Over.pullback (jK E)).obj G ⟶ (Over.pullback (jK E)).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (jK E)).map F = f := by
  intro E _ _ _ _ G H _ _ hG hH f hf
  exact GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds E (FractionRing E) G H hG hH f

end GlobalTheory.Desc
end

