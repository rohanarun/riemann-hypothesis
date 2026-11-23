module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotien
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.IntGauge

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, norm_mul] at *
              exact mul_le_one₀ ha (norm_nonneg _) hb
            one_mem' := by simp
            add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
            zero_mem' := by simp
            neg_mem' := fun {a} ha => by simpa using ha
            mem_or_inv_mem' := fun x => by
              by_cases h : ‖x‖ ≤ 1
              · exact Or.inl h
              · right
                show ‖x⁻¹‖ ≤ 1
                rw [norm_inv]
                exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h)) }, fun x => Iff.rfl⟩

theorem exists_intN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  intro V _ _ _ _ _ D C _ _ _ _ _ _ hC
  obtain ⟨S, hS⟩ := exists_ball C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult
    C S (fun r => (hS _).2 (hC.1 r))
  exact ⟨N, ν, S, hS, hν⟩

end GlobalTheory.IntGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationOfVectorFieldLiftNearUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem scheme_constantSection_add {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a + b) = constFn p U a + constFn p U b := by
  simp [constFn, map_add (f := _)]

theorem constFn_mul_on_open {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a * b) = constFn p U a * constFn p U b := by
  simp [constFn, map_mul]

theorem gammaSpecIso_appLE_of_eq_id_apply {R : Type} [CommRing R] (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (e : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ ⊤) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = r := by
  subst hf
  simp only [Scheme.Hom.appLE]
  erw [show (homOfLE e) = 𝟙 _ from Subsingleton.elim _ _]
  simp

theorem gammaSpecIso_appLE_section_constantSection_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (e : Sp R ⟶ X) (he : e ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ e ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r)) = r := by
  have hc := Scheme.Hom.appLE_comp_appLE e p ⊤ U ⊤ (fun _ _ => trivial) h
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ e.appLE U ⊤ h).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
    _ = _ := by rw [hc]
    _ = r := gammaSpecIso_appLE_of_eq_id_apply _ he _ r

end GlobalTheory.Heat

namespace GlobalTheory.Heat

theorem liftDer_isDerivation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens)
    (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  intro R _ G _ D W d hL hW
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  let ev : Γ(G.left, W) →+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (((η[G]).left.appLE W ⊤ hW).hom)
  have hev : ∀ r, ev (constFn G.hom W r) = r := fun r => gammaSpecIso_appLE_section_constantSection_eq G.hom _ he W hW r
  have hc : ∀ r, d W (constFn G.hom W r) = constFn G.hom W (D r) := hL.2 W le_rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have := congrArg ev (hc (a + b))
    rw [scheme_constantSection_add, hL.1.1 W le_rfl, hc, hc, map_add (f := _), hev, hev, hev] at this
    exact this.symm
  have hmul : ∀ a b, D (a * b) = a * D b + b * D a := by
    intro a b
    have := congrArg ev (hc (a * b))
    rw [constFn_mul_on_open, hL.1.2.1 W le_rfl, hc, hc, map_add (f := _), map_mul, map_mul, hev, hev, hev, hev, hev] at this
    exact this.symm
  let L : R →ₗ[ℤ] R := (AddMonoidHom.mk' D hadd).toIntLinearMap
  exact ⟨Derivation.mk' L (fun a b => by simpa [L, smul_eq_mul] using hmul a b), fun r => rfl⟩

end GlobalTheory.Heat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentLinearisedLineBundleFiniteGroupQuot
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.QuotDescent

private theorem descent_algebraMap_stalkCongr_of_eq {X : Scheme.{0}} [IsIntegral X] {x y : X} (h : x = y)
    (a : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk y) X.functionField ((X.presheaf.stalkCongr (.of_eq h)).hom a) =
      algebraMap (X.presheaf.stalk x) X.functionField a := by
  subst h
  simp

private theorem descent_fromSpecResidueField_comp_eq_of_fixes (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ]
    (ρ : Γ →* Aut X) (γ : Γ) (x : X) (hx : (ρ γ).asIso.hom x = x)
    (h : ∀ u : X.functionFieldˣ, RegAt x u → ZeroAt x ((fnAct ρ γ u : X.functionField) - u)) :
    X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x := by
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  set φ := (ρ γ).asIso.hom with hφ
  have key : (X.residueFieldCongr hx.symm).hom ≫ φ.residueFieldMap x = 𝟙 _ := by
    rw [← cancel_epi (X.residue x), Category.comp_id, X.residue_residueFieldCongr_assoc,
      Scheme.residue_residueFieldMap]
    ext a
    change IsLocalRing.residue _ (φ.stalkMap x ((X.presheaf.stalkCongr (.of_eq hx.symm)).hom a)) =
      IsLocalRing.residue _ a
    set b := (X.presheaf.stalkCongr (.of_eq hx.symm)).hom a with hb
    change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    by_cases ha : a = 0
    · rw [hb, ha, map_zero, map_zero, sub_zero]
      exact zero_mem _
    · have hne : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
      obtain ⟨c, hc, e⟩ := h (Units.mk0 _ hne) ⟨a, rfl⟩
      have e2 : ((fnAct ρ γ (Units.mk0 _ hne) : X.functionFieldˣ) : X.functionField) =
          GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) := rfl
      have e4 : GlobalTheory.functionFieldMap φ (algebraMap (X.presheaf.stalk x) X.functionField a) =
          algebraMap (X.presheaf.stalk x) X.functionField (φ.stalkMap x b) := by
        rw [← descent_algebraMap_stalkCongr_of_eq hx.symm a, ← hb]
        exact GlobalTheory.functionFieldMap_algebraMap φ x b
      rw [e2, Units.val_mk0, e4, ← map_sub] at e
      rwa [← IsFractionRing.injective _ _ e]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← X.residueFieldCongr_fromSpecResidueField hx.symm, ← Category.assoc, ← Spec.map_comp, key,
    Spec.map_id, Category.id_comp]


theorem functionFieldMap_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    functionFieldMap (a ≫ b) = (functionFieldMap a).comp (functionFieldMap b) := by
  have e : Spec.map (CommRingCat.ofHom (functionFieldMap (a ≫ b))) ≫ genericFieldPoint Z =
      Spec.map (CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b))) ≫
        genericFieldPoint Z := by
    rw [specMap_functionFieldMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      specMap_functionFieldMap, ← Category.assoc, ← Category.assoc, specMap_functionFieldMap]
  haveI : Mono (genericFieldPoint Z) := inferInstanceAs (Mono (Z.fromSpecStalk _))
  have := Spec.map_injective ((cancel_mono _).mp e)
  exact congrArg CommRingCat.Hom.hom this

theorem fnAct_mul : ∀ (X : Scheme.{0}) [IsIntegral X] (Γ : Type) [Group Γ] (ρ : Γ →* Aut X) (γ δ : Γ)
    (u : X.functionFieldˣ), fnAct ρ (γ * δ) u = fnAct ρ δ (fnAct ρ γ u) := by
  intro X _ Γ _ ρ γ δ u
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  haveI : IsIso (ρ δ).asIso.hom := Iso.isIso_hom (ρ δ).asIso
  haveI : IsIso (ρ (γ * δ)).asIso.hom := Iso.isIso_hom (ρ (γ * δ)).asIso
  have hc : (ρ (γ * δ)).asIso.hom = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom := by
    rw [map_mul, Aut.mul_asIso]; rfl
  apply Units.ext
  change functionFieldMap (ρ (γ * δ)).asIso.hom (u : X.functionField) =
    functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField))
  have key : ∀ (f : X ⟶ X) (_ : IsDominant f), f = (ρ δ).asIso.hom ≫ (ρ γ).asIso.hom →
      functionFieldMap f (u : X.functionField) =
        functionFieldMap (ρ δ).asIso.hom (functionFieldMap (ρ γ).asIso.hom (u : X.functionField)) := by
    rintro f _ rfl
    rw [functionFieldMap_comp]
    rfl
  exact key _ inferInstance hc

theorem descent : ∀ (F : Type) [Field F] [NumberField F] (X W : Scheme.{0}) [IsIntegral X] (q : X ⟶ W) (sW : W ⟶ Sp F) (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB), IsProjOver (q ≫ sW) → IsAffineQuotient ρ q → RatLin ρ L hL → ∃ (N : LB W) (hN : N.IsLB), CechPic.pull q (cls N hN) = cls L hL := by
  intro F _ _ X W _ q sW Γ _ _ ρ L hL _ hq hR
  obtain ⟨D, c, hcls, hcoc, heq, hin⟩ := hR
  haveI : IsIntegral W := hq.isIntegral
  haveI : Surjective q := hq.surjective
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (toFunctionField (q ≫ sW)).injective
  let σ : Γ → X.functionField →+* X.functionField := fun γ =>
    haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso; functionFieldMap (ρ γ).asIso.hom
  have hσu : ∀ γ (u : X.functionFieldˣ), ((fnAct ρ γ u : X.functionFieldˣ) : X.functionField) = σ γ u :=
    fun _ _ => rfl
  have hσ : ∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a) := by
    intro γ δ a
    by_cases ha : a = 0
    · simp [ha]
    · have := congrArg Units.val (fnAct_mul X Γ ρ γ δ (Units.mk0 a ha))
      rwa [hσu, hσu, hσu] at this
  have hcoc' : ∀ γ δ, (c (γ * δ) : X.functionField) = σ δ (c γ) * c δ := fun γ δ => by
    rw [hcoc, Units.val_mul, hσu]
  have htriv : ∀ γ, (∀ a, σ γ a = a) → c γ = 1 := by
    intro γ hγ
    have hη : (ρ γ).asIso.hom (genericPoint X) = genericPoint X := by
      haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
      have h1 := (genericPoint_spec X).image (ρ γ).asIso.hom.continuous
      have hs : Function.Surjective (ρ γ).asIso.hom.base := (ρ γ).asIso.hom.surjective
      simp only [Set.top_eq_univ, Set.image_univ, hs.range_eq, closure_univ] at h1
      exact h1.eq (genericPoint_spec X)
    have hfix := descent_fromSpecResidueField_comp_eq_of_fixes X Γ ρ γ (genericPoint X) hη (fun u _ => by rw [hσu, hγ, sub_self]; exact zeroAt_zero _)
    have h0 := hin γ _ 1 hfix (D.isEqn_genericPoint 1)
    have h1 : ((fnAct ρ γ 1 * (c γ)⁻¹ * 1⁻¹ : X.functionFieldˣ) : X.functionField) - 1 = 0 := by
      by_contra hne
      exact (zeroAt_iff.1 h0).2 (unitAt_genericPoint hne)
    rw [map_one, one_mul, inv_one, mul_one, sub_eq_zero, ← Units.val_one, Units.val_inj, inv_eq_one] at h1
    exact h1
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.exists_unit_of_cocycle_rightAction_charZero _ Γ σ hσ c hcoc' htriv
  have hfu : ∀ γ, fnAct ρ γ f = c γ * f := fun γ => Units.ext (by rw [hσu, Units.val_mul]; exact hf γ)
  set D' := D - CartierDiv.principal f with hD'
  have hD : D' + CartierDiv.principal f = D := sub_add_cancel _ _
  have hinv' : ∀ γ x g, D'.IsEqn ((ρ γ).asIso.hom x) g → D'.IsEqn x (fnAct ρ γ g) := by
    intro γ x g h
    have h1 := heq γ x (g * f) (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f _))
    have h2 := h1.sub (CartierDiv.isEqn_principal f x)
    have e : fnAct ρ γ g = fnAct ρ γ (g * f) * (c γ)⁻¹ / f := by
      rw [map_mul, hfu]; simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h2
  have hin' : ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D'.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1) := by
    intro γ x g hx h
    have h1 := hin γ x (g * f) hx (by rw [← hD]; exact h.add (CartierDiv.isEqn_principal f x))
    have e : fnAct ρ γ g * g⁻¹ = fnAct ρ γ (g * f) * (c γ)⁻¹ * (g * f)⁻¹ := by
      rw [map_mul, hfu]; simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]
    rw [e]; exact h1
  have hloc := _root_.GlobalTheory.InvEqn.exists_invariant_isEqn F X W (q ≫ sW) Γ ρ q hq D' hinv' hin'
  have key : ∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y →
      D'.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
    intro y
    obtain ⟨x, rfl⟩ := q.surjective y
    obtain ⟨g, hg, hgx⟩ := hloc x
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant X W Γ ρ q hq g hg
    refine ⟨b, fun x' hx' => ?_⟩
    obtain ⟨γ, rfl⟩ := (hq.apply_eq_iff x x').1 hx'.symm
    rw [hb]
    have hp : (ρ γ⁻¹).asIso.hom ((ρ γ).asIso.hom x) = x := by
      rw [map_inv]
      exact Scheme.inv_hom_apply _ _
    have := hinv' γ⁻¹ ((ρ γ).asIso.hom x) g (by rw [hp]; exact hgx)
    rwa [hg] at this
  obtain ⟨E, hE⟩ := _root_.GlobalTheory.Cartier.Descent.exists_cartierDiv_descent X W Γ ρ q hq D' key
  refine ⟨toLB E, isLB_toLB E, ?_⟩
  rw [_root_.GlobalTheory.Cartier.PullPres.pull_cls_toLB X W q D' E hE]
  calc cls (toLB D') (isLB_toLB D') = toPic D' := (toPic_apply D').symm
    _ = toPic D := by rw [hD', map_sub, toPic_principal, sub_zero]
    _ = cls L hL := hcls

end GlobalTheory.QuotDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberTangentPointOfLogarithmicDerivat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.LogPole

theorem spMap_comp_spMap' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_ext_ev {R S : Type} [CommRing R] [CommRing S] {z z' : Sp S ⟶ Sp R} (h : ⊤ ≤ z ⁻¹ᵁ ⊤)
    (h' : ⊤ ≤ z' ⁻¹ᵁ ⊤) (e : ∀ a, ev z ⊤ h a = ev z' ⊤ h' a) : z = z' := by
  rw [← FlagMod.spMap_ev z (isAffineOpen_top _) h, ← FlagMod.spMap_ev z' (isAffineOpen_top _) h']
  congr 2
  exact RingHom.ext e

theorem ev_spMap_top {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : ⊤ ≤ (spMap f) ⁻¹ᵁ ⊤)
    (h₀ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) : ev (spMap f) ⊤ h a = f (ev (𝟙 (Sp R)) ⊤ h₀ a) := by
  have e := FlagMod.ev_spMap f (𝟙 (Sp R)) ⊤ h₀ (by simpa using h)
  rw [FlagMod.ev_congr (Category.comp_id (spMap f)).symm ⊤ h (by simpa using h), e]
  rfl

end GlobalTheory.LogPole


open GlobalTheory.LogPole in
theorem GlobalTheory.LogPole.exists_tanPt_of_logDer : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), ∃ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) ∧ spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ ∧ ∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P₀ ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P₀ ≫ TF.Y.j) U.1 hU (D.1 r)) := by
  intro E _ _ _ H Dw l Xo c TF U D K _ _ P₀ hU
  set φ := ev (frX P₀ ≫ TF.Y.j) U.1 hU with hφ
  let θ : Γ(TF.Y.X, U.1) →+* DualNumber K :=
    { toFun := fun r => TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r))
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]; ring
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring }
  have hθ : ∀ r, θ r = TrivSqZeroExt.inl (φ r) + TrivSqZeroExt.inr (φ (D.1 r)) := fun _ => rfl
  let z : Sp (DualNumber K) ⟶ TF.Y.X := spMap θ ≫ U.2.fromSpec
  have hred : spMap (FlagTan.red c K).toRingHom ≫ z = frX P₀ ≫ TF.Y.j := by
    have e : (FlagTan.red c K).toRingHom.comp θ = φ := RingHom.ext fun r => by simp [hθ]
    rw [← Category.assoc, spMap_comp_spMap', e]
    exact FlagMod.spMap_ev _ U.2 hU
  have hint : Set.range z ⊆ Set.range TF.Y.j := by
    have h1 : ⊤ ≤ z ⁻¹ᵁ TF.Y.j.opensRange :=
      le_preimage_of_dualNumber _ z _ (by rw [hred]; rintro s -; exact ⟨frX P₀ s, rfl⟩)
    rintro _ ⟨s, rfl⟩
    exact h1 (Set.mem_univ s)
  let y' := IsOpenImmersion.lift TF.Y.j z hint
  have hy' : y' ≫ TF.Y.j = z := IsOpenImmersion.lift_fac _ _ _
  have hzU : ⊤ ≤ z ⁻¹ᵁ U.1 := FlagMod.le_preimage_comp (spMap θ) (FlagMod.tau_le U.2 le_rfl)
  have hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1 := by rw [hy']; exact hzU
  have hevz : ev z U.1 hzU = θ := FlagMod.ev_spMap_tau U.2 θ hzU

  have hjs : TF.Y.j ≫ TF.Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, TF.Y.jQ_over]
    exact (congrArg (_ ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)
  have htop : ∀ {S : Type} [CommRing S] (w : Sp S ⟶ Sp c.F), ⊤ ≤ w ⁻¹ᵁ ⊤ := fun _ => fun _ _ => trivial
  have hUs : U.1 ≤ TF.Y.s ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨y', hU', ?_, ?_, fun r => ?_⟩
  ·
    have e1 : y' ≫ pullback.snd _ _ = z ≫ TF.Y.s := by rw [← hjs, ← Category.assoc, hy']
    rw [e1]
    refine sp_ext_ev (htop _) (htop _) fun a => ?_
    rw [← FlagMod.ev_appLE z TF.Y.s hUs hzU (htop _) a, hevz, hθ]
    have hc : (TF.Y.s.appLE ⊤ U.1 hUs).hom a =
        constFn TF.Y.s U.1 ((Scheme.ΓSpecIso (CommRingCat.of c.F)).hom.hom a) := by
      simp only [constFn]
      congr 1
      simp
    have hD : D.1 ((TF.Y.s.appLE ⊤ U.1 hUs).hom a) = 0 := by rw [hc]; exact D.2.1 _
    rw [hD, map_zero, TrivSqZeroExt.inr_zero, add_zero, hφ,
      FlagMod.ev_appLE (frX P₀ ≫ TF.Y.j) TF.Y.s hUs hU (htop _) a,
      FlagMod.ev_congr (show (frX P₀ ≫ TF.Y.j) ≫ TF.Y.s = spMap (algebraMap c.F K) by
        rw [Category.assoc, hjs, FlagMod.frX_snd]) ⊤ (htop _) (htop _),
      ev_spMap_top _ (htop _) (fun _ _ => trivial), ev_spMap_top _ (htop _) (fun _ _ => trivial), TrivSqZeroExt.algebraMap_eq_inl']
  · rw [← cancel_mono TF.Y.j, Category.assoc, hy', hred]
  · rw [FlagMod.ev_congr hy' U.1 hU' hzU, hevz]
    exact hθ r
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HeightOneCompletion

open IsLocalRing


set_option autoImplicit false in
open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.CompHt.algPadicInt _root_.GlobalTheory.CompHt.algPadicField
  _root_.GlobalTheory.CompHt.towerPadic _root_.GlobalTheory.CompHt.factPadic
  _root_.GlobalTheory.PadicComplexHost.isAdicComplete in
open IsLocalRing in
theorem _root_.GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A]
      (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 →
      ∃ (T : _root_.Formalism.L2.Pj.CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V),
        Function.Injective iT ∧ IsLocalHom iT := by
  intro A _ _ _ _ _ 𝔭 h
  obtain ⟨hdom, hic⟩ :=
    _root_.GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal)
  haveI := hdom
  haveI := hic
  haveI : IsNoetherianRing (Localization.AtPrime 𝔭.asIdeal) :=
    IsLocalization.isNoetherianRing 𝔭.asIdeal.primeCompl _ inferInstance
  have hdim : ringKrullDim (Localization.AtPrime 𝔭.asIdeal) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭.asIdeal (Localization.AtPrime 𝔭.asIdeal), h]
    rfl
  haveI := _root_.GlobalTheory.CdvrExt.isDVR_of_ringKrullDim_eq_one hdim
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime 𝔭.asIdeal)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors 𝔭.asIdeal)
  obtain ⟨O, _, _, _, j, r, hc, hj, hl, -, -, -⟩ :=
    _root_.GlobalTheory.exists_complete_discreteValuationRing_with_residues (Localization.AtPrime 𝔭.asIdeal)
      (ResidueField (Localization.AtPrime 𝔭.asIdeal)) (residue _) ∅ (ker_residue)
  haveI : CharZero (Localization.AtPrime 𝔭.asIdeal) := ⟨fun m n hmn =>
    Nat.cast_injective (R := A) (hinj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  haveI : CharZero O := ⟨fun m n hmn =>
    Nat.cast_injective (R := Localization.AtPrime 𝔭.asIdeal)
      (hj (by rw [map_natCast, map_natCast]; exact hmn))⟩
  exact ⟨@_root_.Formalism.L2.Pj.CDVR.mk O _ _ _ hc _, j, hj, hl⟩

end GlobalTheory.HeightOneCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMap
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.StalkField

theorem exists_stalk_field_hom : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  intro Ω _ X p hfin
  have hpt : genericPoint (Sp Ω) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [hpt] at hfin ⊢
  refine ⟨(Scheme.stalkClosedPointTo p).hom, ?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo p = p.stalkMap _ ≫ (stalkClosedPointIso (CommRingCat.of Ω)).hom := rfl
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).2) hfin
  · intro K _ τ₁ τ₂ h
    have hs : ∀ τ : Ω →+* K, (spMap τ ≫ p) (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω) := by
      intro τ
      apply specializes_of_eq
      exact congrArg p (Subsingleton.elim ((spMap τ).base (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint Ω))
    have H : ∀ (q₁ q₂ : Sp K ⟶ X), q₁ = q₂ → ∀ (h₁ : q₁ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω))
        (h₂ : q₂ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω)) a,
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.stalkSpecializes h₁).hom a) =
          (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.stalkSpecializes h₂).hom a) := by
      rintro _ _ rfl _ _ _; rfl
    ext a
    simp only [RingHom.comp_apply]
    rw [← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₁ (hs τ₁) a,
      ← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₂ (hs τ₂) a]
    exact H _ _ h _ _ a

end GlobalTheory.StalkField
end

