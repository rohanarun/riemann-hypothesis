module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomial
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.MonoOrd

variable {Y : Scheme.{0}} [IsIntegral Y]

def schOrdHom [IsLocallyNoetherian Y] (v : Y) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (Scheme.ord (g : Y.functionField) v)
  map_one' := by
    have h := Scheme.ord_mul (x := v) (one_ne_zero (α := Y.functionField))
      (one_ne_zero (α := Y.functionField))
    rw [mul_one] at h
    have h0 : Scheme.ord (1 : Y.functionField) v = 0 := by omega
    simp [h0]
  map_mul' f g := by
    simp [Units.val_mul, Scheme.ord_mul f.ne_zero g.ne_zero, ofAdd_add]

theorem schOrd_prod_zpow [IsLocallyNoetherian Y] {ι : Type} (s : Finset ι)
    (u : ι → Y.functionFieldˣ) (m : ι → ℤ) (v : Y) :
    Scheme.ord ((∏ j ∈ s, u j ^ m j : Y.functionFieldˣ) : Y.functionField) v =
      ∑ j ∈ s, m j * Scheme.ord (u j : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_prod (schOrdHom v) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

theorem schOrd_inv [IsLocallyNoetherian Y] (g : Y.functionFieldˣ) (v : Y) :
    Scheme.ord ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) v =
      - Scheme.ord (g : Y.functionField) v := by
  have h := congrArg Multiplicative.toAdd (map_inv (schOrdHom v) g)
  rw [toAdd_inv] at h
  exact h

variable {k : Type} [Field k] {q : Y ⟶ Sp k}

def divOrdHom (E : DivOver q) : Y.functionFieldˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (E.ord g)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul, ofAdd_add]

theorem divOrd_prod_zpow (E : DivOver q) {ι : Type} (s : Finset ι) (u : ι → Y.functionFieldˣ)
    (m : ι → ℤ) : E.ord (∏ j ∈ s, u j ^ m j) = ∑ j ∈ s, m j * E.ord (u j) := by
  have h := congrArg Multiplicative.toAdd (map_prod (divOrdHom E) (fun j => u j ^ m j) s)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul]
  rfl

end GlobalTheory.Discrepancy.MonoOrd


open GlobalTheory.Discrepancy.MonoOrd in
theorem GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  intro k _ Y _ _ _ q E y hE ι _ w u hw _ _ hself hother φ hφ
  classical
  set a : ι → ℤ := fun j => Scheme.ord (φ : Y.functionField) (w j) with ha
  set ψ : Y.functionFieldˣ := φ * ∏ j, u j ^ (-a j) with hψ
  have hord : ∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (ψ : Y.functionField) v = 0 := by
    intro v hv h1
    rw [hψ, Units.val_mul, Scheme.ord_mul φ.ne_zero (Units.ne_zero _), schOrd_prod_zpow]
    by_cases h : ∃ i, v = w i
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · rw [hself i, ha]
        ring
      · intro j _ hji
        rw [hother j (w i) hv h1 (fun e => hji (hw e.symm)), mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · push_neg at h
      rw [Finset.sum_eq_zero fun j _ => by rw [hother j v hv h1 (h j), mul_zero],
        hφ v hv h1 h, add_zero]
  have hreg : ∀ g : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → Scheme.ord (g : Y.functionField) v = 0) →
        0 ≤ E.ord g := fun g hg =>
    (E.ord_nonneg_iff g).2 (hE _ (regAt_of_forall_coheight_eq_one fun z hz h1 =>
      (GlobalTheory.RegCodimOne.regAt_iff_ord_nonneg h1 g.ne_zero).2 (hg z hz h1).ge))
  have h0 := hreg ψ hord
  have h0' := hreg ψ⁻¹ fun v hv h1 => by rw [schOrd_inv, hord v hv h1, neg_zero]
  rw [E.ord_inv] at h0'
  have hψ0 : E.ord ψ = 0 := by omega
  rw [hψ, E.ord_mul, divOrd_prod_zpow] at hψ0
  simp only [neg_mul, Finset.sum_neg_distrib] at hψ0
  rw [ha] at hψ0
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PrimitiveAmpleLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat
open GlobalTheory.PrimitiveOverLocalRing hiding exists_section_translate
open GlobalTheory.PrimitiveOverValuationRing hiding exists_geometric_point exists_section_translate

theorem theta_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := hΘ
  let U : Over.mk ((G3 G').hom ≫ f) ⟶ G3 G :=
    lift (pushPt h.1.w (x3 G' 0)) (lift (pushPt h.1.w (x3 G' 1)) (pushPt h.1.w (x3 G' 2)))
  have hx : ∀ i, pushPt h.1.w (x3 G' i) = U ≫ x3 G i := fun i => by fin_cases i <;> simp [U, x3]
  exact gen_chartPull (chartPullLinComb L φ (thφ G' (x3 G')) (thφ G (x3 G)) thε U.left
    fun k => psum_push h _ _ U hx k.down) t ht

theorem exists_geometric_point {A : Type} [CommRing A] {B : Over (Sp A)} [GrpObj B] [IsCommMonObj B] {d : ℕ}
    {L O : LB B.left} (hB : IsAbelianScheme B) (hd : SmoothOfRelativeDimension d B.hom) (hL : L.IsLB)
    (ha : RelAmple B L) (hk : KTriv B L) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen) (hO : O.IsLB)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ Sp A) :
    ∃ x : Over.mk f ⟶ B, Triv (LB.div (translDiff B L x) (O.pull (snd (Over.mk f) B).left)) := by
  obtain ⟨B', _, _, g, h, hB'⟩ : ∃ (B' : Over (Spec (CommRingCat.of K))) (_ : GrpObj B') (_ : IsCommMonObj B')
      (g : B'.left ⟶ B.left), IsGrpPullback B' B f g ∧ IsAbelianScheme B' :=
    ⟨(Over.pullback f).obj B, inferInstance, (TLinPf.isAb_pullback f B hB).comm, _, isGrpPullback_pullback B f,
      TLinPf.isAb_pullback f B hB⟩
  have hg := h.1
  have hm : ∀ (T : Over (Spec (CommRingCat.of K))) (x y : T ⟶ B'),
      toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y := fun T x y =>
    Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hL' := pull_isLB hL g
  have hd' : SmoothOfRelativeDimension d B'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg hd
  obtain ⟨w₀, hw₀⟩ : LBIso (L.pull g) (L.pull g) := ⟨idIso _, idIso_isGen hL'⟩
  have ha' : RelAmple B' (L.pull g) :=
    relAmple_pull hg hL hL' ((isGen_iff w₀).1 hw₀) ⊤ (isAffineOpen_top _) (fun _ => trivial) ha
  have hk' : KTriv B' (L.pull g) := kTriv_pull h hL hL' ((isGen_iff w₀).1 hw₀) hk
  have hΘ' := theta_pull h hΘ
  have hc : CechPic.pull g (cls L hL) = cls (L.pull g) hL' := (cls_pull hL _ _).symm
  have hO' := pull_isLB hO g
  have one : ∀ T : Over (Spec (CommRingCat.of K)), toBase hg.w (1 : T ⟶ B') = 1 := fun T => by
    have := hm T 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have lamO : lam (cls O hO) (fst B B) (snd B B) = 0 :=
    (cls_cube_two hO _ _ (LB.isLB_linComb hO _ _)).symm.trans ((cls_eq_zero_iff _).2 hu)
  have lamO' : lam (cls _ hO') (fst B' B') (snd B' B') = 0 := by
    have e := congrArg (CechPic.pull (lift (toBase hg.w (fst B' B')) (toBase hg.w (snd B' B'))).left) lamO
    rw [pull_lam, lift_fst, lift_snd, map_zero, lam, ← hm, ← one] at e
    rw [cls_pull hO, lam, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
    exact e
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_point_translate_primitive_of_ample_K_trivial K B' d (L.pull g) (O.pull g) hB' hd' hL' ha' hk' hΘ' hO'
    ((cls_eq_zero_iff (LB.isLB_linComb hO' _ _)).1 ((cls_cube_two hO' _ _ (LB.isLB_linComb hO' _ _)).trans lamO'))
  have e := ((cls_eq_iff hO' (LB.isLB_linComb hL' _ _)).2 hx').trans (cls_pair hL' _ _ _)
  let T : Over (Sp A) := Over.mk f
  have wx : x'.left ≫ B'.hom = 𝟙 _ := Over.w x'
  let x : T ⟶ B := Over.homMk (x'.left ≫ g) (by
    show (x'.left ≫ g) ≫ B.hom = f
    rw [Category.assoc, hg.w, ← Category.assoc, wx]
    exact Category.id_comp _)
  have w : (snd T B).left ≫ B.hom = (fst T B).left ≫ f := (Over.w (snd T B)).trans (Over.w (fst T B)).symm
  let T' : Over (Spec (CommRingCat.of K)) := Over.mk (Y := (T ⊗ B).left) (fst T B).left
  let h : T' ⟶ B' := Over.homMk (hg.lift (snd T B).left (fst T B).left w) (hg.lift_snd _ _ _)
  have hh : h.left ≫ g = (snd T B).left := hg.lift_fst _ _ _
  let u : Over.mk (T'.hom ≫ f) ⟶ T ⊗ B := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Over.w (fst T B)).symm)
  have b₁ : u ≫ snd T B = toBase hg.w h := Over.OverMorphism.ext ((Category.id_comp _).trans hh.symm)
  have b₂ : u ≫ fst T B ≫ x = toBase hg.w (toUnit T' ≫ x') := by
    refine Over.OverMorphism.ext ((Category.id_comp _).trans ?_)
    have : (toUnit T').left = (fst T B).left := (Category.comp_id _).symm.trans (Over.w (toUnit T'))
    show (fst T B).left ≫ x'.left ≫ g = ((toUnit T').left ≫ x'.left) ≫ g
    rw [this]
    exact (Category.assoc _ _ _).symm
  have b : h.left ≫ ((toUnit B' ≫ x') * 𝟙 B').left ≫ g = ((fst T B ≫ x) * snd T B).left := by
    have b₃ : toBase hg.w (h ≫ ((toUnit B' ≫ x') * 𝟙 B')) = u ≫ ((fst T B ≫ x) * snd T B) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, b₁, b₂, ← hm, Category.comp_id, ← Category.assoc, comp_toUnit]
    exact (Category.assoc _ _ _).symm.trans ((congrArg CommaMorphism.left b₃).trans (Category.id_comp _))
  have e' := congrArg (CechPic.pull h.left) e
  rw [cls_pull hO, ← hc, pull_id, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, Category.assoc, b, hh] at e'
  have h₁ : (translDiff B L x).IsLB := LB.isLB_linComb hL _ _
  have h₂ := pull_isLB hO (snd T B).left
  refine ⟨x, (cls_eq_zero_iff (LB.isLB_div h₁ h₂)).1 ?_⟩
  rw [cls_div h₁ h₂, sub_eq_zero]
  exact (cls_pair hL _ _ h₁).trans e'.symm

theorem exists_section_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  intro V _ _ _ B _ _ d L O hB hd hL ha hk hΘ hO hu
  have hG : GlobalFnsSt := _root_.GlobalTheory.allSixLaws.1.globalFns
  have proj : IsProjBy B.hom := by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy V B L hL).1 ha
    exact ⟨_, isLB_pw hL _, n, s, hs⟩
  obtain ⟨H, j, hj, hH⟩ := _root_.GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG V B hB proj L O hL hO
  have fin : IsFinite H.hom := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L O hL hO
    ha H j hj hH
  have mono : Mono H.hom := ⟨fun {Z} a b e => by
    let a' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk a e
    let b' : Over.mk (b ≫ H.hom) ⟶ H := Over.homMk b rfl
    have := (inK_mul_inv hL hO (a' ≫ j) (b' ≫ j) ((hH _ _).2 ⟨_, rfl⟩) ((hH _ _).2 ⟨_, rfl⟩)).eq_one hk
    rw [mul_inv_eq_one] at this
    exact (cancel_mono j.left).1 (congrArg CommaMorphism.left this)⟩
  have : IsClosedImmersion H.hom := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨fin, mono⟩
  let K : Type := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* K := (algebraMap (IsLocalRing.ResidueField V) K).comp (IsLocalRing.residue V)
  have : IsLocalHom φ := RingHom.isLocalHom_comp _ _
  obtain ⟨x₀, hx₀⟩ := exists_geometric_point hB hd hL ha hk hΘ hO hu K (Spec.map (CommRingCat.ofHom φ))
  obtain ⟨y, -⟩ := (hH _ x₀).1 fun p => ⟨⊤, trivial, by
    have hM := LB.isLB_div (show (translDiff B L x₀).IsLB from LB.isLB_linComb hL _ _)
      (pull_isLB hO (snd _ B).left)
    refine (cls_eq_zero_iff (pull_isLB hM _)).1 ?_
    rw [cls_pull hM, (cls_eq_zero_iff hM).2 hx₀, map_zero]⟩
  let y' : Spec (CommRingCat.of K) ⟶ H.left := y.left
  have hy : H.hom (y' (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint V :=
    (congrArg (fun q => q (IsLocalRing.closedPoint K)) (Over.w y)).trans (IsLocalRing.comap_closedPoint φ)
  obtain ⟨R, _, _, _, _, ξ, g₀, hfl, hξ, hξV, hg₀, hξK, hreg, hdim⟩ :=
    FibreAcyclic.exists_localRing B.hom d hd (y' ≫ j.left) (by
      have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom _ hy)
      rwa [Set.image_singleton] at this) ((congrArg (fun q => q (y' (IsLocalRing.closedPoint K))) (Over.w j)).trans hy)
  obtain ⟨I, C, c₁, ⟨n, c₂⟩, ⟨e⟩, c₃, hI⟩ := exists_ideal_complex hG B hB proj hd hL hO
    hΘ hu j hH R ξ K g₀ hg₀ ⟨y', hξK.symm⟩
  have hI₀ : I ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top g₀) ((hI K g₀).1 ⟨y', hξK.symm⟩)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI₀
  have : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := (hI (R ⧸ I) (Ideal.Quotient.mk I)).2 Ideal.mk_ker.ge
  have hwV : w ≫ H.hom = Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := by
    rw [← Over.w j, ← Category.assoc, hw, Category.assoc, hξV, ← Spec.map_comp]
    rfl
  have hN : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hloc : IsLocalHom (algebraMap V R) := ((IsLocalRing.local_hom_tfae (algebraMap V R)).out 3 1).1 hN
  have hsurj : Function.Surjective (algebraMap V (R ⧸ I)) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsPreimmersion (w ≫ j.left) := hw ▸ inferInstance
    have : IsPreimmersion w := IsPreimmersion.of_comp w j.left
    have h₁ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) := hwV ▸ inferInstance
    have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap V (R ⧸ I)) := RingHom.isLocalHom_comp (Ideal.Quotient.mk I) (algebraMap V R)
    exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.1 ((IsPreimmersion.SpecMap_iff _).1 h₁).2
  have hinj : Function.Injective (algebraMap V (R ⧸ I)) := by
    have hfree := fun i => (c₁ i).1
    have hfin := fun i => (c₁ i).2
    refine FibreAcyclic.injective_of_exact (C.d 0 1).hom (C.d 1 2).hom (DualCokernel.d_d_apply C 0 1 2) ?_ I hI₀ e hsurj
    refine FibreAcyclic.exact_hom_one _ hN _ (fun s hs x => ?_) d (FibreAcyclic.extZero_quotient _ _ hdim) C c₁ n c₂
      fun p hp hNp => ?_
    · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hs, zero_mul]
    · obtain ⟨K', _, ψ, hψ, hex⟩ := c₃ p hp
      refine ⟨K', inferInstance, ψ, hψ, fun i hi => hex i (hi.imp_left fun hne hIp => hne ?_)⟩
      refine (IsLocalRing.le_maximalIdeal hp.ne_top).antisymm fun s hs => ?_
      obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk I s)
      have h₁ : algebraMap V R a - s ∈ I := Ideal.Quotient.eq.1 ha
      have h₂ : algebraMap V R a ∈ IsLocalRing.maximalIdeal R := by
        simpa using add_mem (IsLocalRing.le_maximalIdeal hI₀ h₁) hs
      have h₃ : a ∈ IsLocalRing.maximalIdeal V := fun h => h₂ (h.map _)
      simpa using sub_mem (hNp (Ideal.mem_map_of_mem _ h₃)) (hIp h₁)
  have : IsIso (CommRingCat.ofHom (algebraMap V (R ⧸ I))) := (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩
  let σ : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ H :=
    Over.homMk (inv (Spec.map (CommRingCat.ofHom (algebraMap V (R ⧸ I)))) ≫ w) (by
      rw [Category.assoc, hwV]
      exact IsIso.inv_hom_id _)
  obtain ⟨U, hU, ht⟩ := (hH _ (σ ≫ j)).2 ⟨σ, rfl⟩ (IsLocalRing.closedPoint V)
  obtain rfl : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hU
  have e := pull_eq_zero_of_mem ((fst _ B).left ⁻¹ᵁ ⊤) (lift (toUnit B) (𝟙 B)).left (fun _ => trivial)
    ((triv_iff hL hO (σ ≫ j) _).1 ht)
  rw [map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_snd, lift_fst_assoc, sub_eq_zero, Over.id_left, pull_id (cls O hO)] at e
  exact ⟨σ ≫ j, (cls_eq_iff hO (LB.isLB_linComb hL _ _)).1 (e.symm.trans (cls_pair hL _ _ _).symm)⟩

end GlobalTheory.PrimitiveAmpleLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid

theorem serreAmple : SerreAmpleSt :=
  serreAmple_of_finiteOrder_of_separated (GlobalTheory.AmpleFiniteOrder.finiteOrder_of_const_of_cube constSt GlobalTheory.AmpleCube.cubeSt)
    (separatedSt_of_const_cube constSt GlobalTheory.AmpleCube.cubeSt)

theorem exists_aut {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback A' A f φ') :
    ∃ σ : A' ≅ A', IsMonHom σ.hom ∧ σ.hom.left ≫ φ' = φ := by
  let ψ : A'.left ⟶ A'.left := h'.1.lift φ A'.hom h.1.w
  have e₁ : ψ ≫ φ' = φ := h'.1.lift_fst _ _ _
  have e₂ : ψ ≫ A'.hom = A'.hom := h'.1.lift_snd _ _ _
  have hψ : IsGrpPullback A' A' (𝟙 _) ψ :=
    IsGrpPullback.cancel h' (by rw [Category.id_comp, e₁]; exact h) (by rw [e₂, Category.comp_id])
  haveI : IsIso ψ := hψ.1.isIso_fst_of_isIso
  let σ : A' ≅ A' := Over.isoMk (asIso ψ) e₂
  exact ⟨σ, isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y, e₁⟩

theorem eq_of_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hamp : Out.RelAmple A L)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    (hc : pull φ (cls L hL) = pull φ' (cls L hL)) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have hL' := pull_isLB hL φ'
  obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
  obtain ⟨U, hU, hcl, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := z (IsLocalRing.closedPoint K)) trivial
  have hy : ∀ y, z y ∈ U := fun y =>
    (congrArg (fun V => y ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem z hcl)).mpr trivial
  have key := serreAmple K A' hA' (L.pull φ') hL'
    (relAmple_pull h'.1 hL hL' ((isGen_iff w).1 hw) U hU hy hamp) N hN hNK σ hσ
    (by rw [cls_pull hL, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

variable {h n n' : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
  {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}

theorem pull_cls_diag {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    pull φ (cls c.diag (pull_isLB c.isLB _)) = cls c'.diag (pull_isLB c'.isLB _) := by
  have e : (lift (𝟙 c'.A) (𝟙 c'.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c.A) (𝟙 c.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c.A) (𝟙 c.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c.A) (𝟙 c.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 c'.A) (𝟙 c'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 c'.A) (𝟙 c'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = (_ ≫ _) ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd c.A c.A).left = (_ ≫ _) ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull φ₂ (cls c.P c.isLB) = cls c'.P c'.isLB :=
    ((cls_eq_iff c'.isLB (pull_isLB c.isLB φ₂)).2 hw).symm
  unfold SiegPre.diag
  rw [cls_pull c.isLB, cls_pull c'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion (hζ : IsUnit ζ) (c : SiegPre h n ζ s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ c.A.left} (hφ : IsGrpPullback A' c.A f φ)
    (lv : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (c.lev a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (c.lev a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ n = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : B →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨-, hs, -⟩ := c.geom k (x ≫ f) β (hζ.map β).unit (Spec.map_preimage _).symm rfl
  have hy₁ : pushHom hφ (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := hs _ hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (c.lev a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ha
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_of_sRelBy : ∀ (h n n' d' : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (c : SiegPre h n (b.ζ : B) s) (c' : SiegPre h n' ζ' s') (f : S' ⟶ S) (φ φ' : c'.A.left ⟶ c.A.left), 3 ≤ n → Odd n → c.Principal → SRelBy c' c d' 1 f φ → SRelBy c' c d' 1 f φ' → φ = φ' := by
  intro h n n' d' B B' _ _ b ζ' S S' s s' c c' f φ φ' hn _ hc ⟨g, ⟨φ₂, q, w⟩, l⟩ ⟨g', ⟨φ₂', q', w'⟩, l'⟩
  simp only [pow_one] at l l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 c'.A c'.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback c'.A j
    have := c'.ab.smooth
    have := c'.ab.proper
    have := c'.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj c'.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd c'.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd c'.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd c'.A.hom j); infer_instance }
    have hNK : (n : K) ≠ 0 := by
      have hu := b.unit.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hc.1 hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hn hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ n = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion b.ζ.isUnit c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientPointsFiniteRepresentativesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientPoints_finite_representatives : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hB : D.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), k ≠ 0 → Finite {x : TF (R := R) F ⟶ D.P.A // x ^ k = 1} → ∃ Rep : Set (QkPt D F k), Rep.Finite ∧ ∀ p : QkPt D F k, ∃ p' ∈ Rep, ∃ (z : D.X) (t : GtPtF D F), t.b = 1 ∧ (letI := GlobalTheory.TorusExt.gtGroup D F; k • t = 0 ∧ p.g = p'.g + GlobalTheory.TorusExt.iota hB F z + t) := by
  first | exact @GlobalTheory.Mum.qkPt_finite_reps | exact GlobalTheory.Mum.qkPt_finite_reps | (intros; apply GlobalTheory.Mum.qkPt_finite_reps <;> assumption)
end

