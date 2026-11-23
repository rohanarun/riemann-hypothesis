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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfIsPullback
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Obs.BaseChg

section Nat
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}

def ofNat (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := sm

theorem ofNat_pull2_bijective (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (sm : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) (hb : ∀ T, Function.Bijective (α T)) :
    Function.Bijective (ofNat α nat sm).pull2 := by
  let e : ∀ T, F.obj T ≃+* F'.obj T := fun T ↦ RingEquiv.ofBijective (α T) (hb T)
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (e T).symm.toRingHom
  have hβα : ∀ T b, β T (α T b) = b := fun T b ↦ (e T).symm_apply_apply b
  have hαβ : ∀ T b, α T (β T b) = b := fun T b ↦ (e T).apply_symm_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := fun a b ↦ by
    apply (hb _).1; rw [hαβ, nat, hαβ]
  have smβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := fun T r b ↦ by
    apply (hb T).1; rw [hαβ, sm, hαβ]
  have h1 : ∀ c, (ofNat β natβ smβ).pull2 ((ofNat α nat sm).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F T b).trans (hβα T b).symm) c
  have h2 : ∀ c, (ofNat α nat sm).pull2 ((ofNat β natβ smβ).pull2 c) = c := fun c ↦ by
    rw [← CoefMap.pullCohomologyTwo_comp]
    conv_rhs => rw [← CoefMap.pullCohomologyTwo_id c]
    exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ { app := fun T ↦ 𝟙 T, naturality := fun _ _ f ↦ by dsimp [ofNat, CoefMap.comp, CoefMap.id]; simp } (fun T b ↦ by
      exact (mp_id F' T b).trans (hαβ T b).symm) c
  exact ⟨fun x y hxy ↦ by rw [← h1 x, hxy, h1], fun y ↦ ⟨_, h2 y⟩⟩

end Nat

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

theorem isAffineHom_of_isPullback (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : IsAffineHom pr :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) hp.flip inferInstance

abbrev pre (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : X₁.affineOpens :=
  haveI := isAffineHom_of_isPullback hp
  ⟨pr ⁻¹ᵁ U.1, U.2.preimage pr⟩

def preF (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) : AffOp X₀ ⥤ AffOp X₁ :=
  (Monotone.functor (f := pre hp) fun _ _ h ↦ (show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from
    fun _ hx ↦ (Subtype.coe_le_coe.2 h) hx)).op

abbrev pairOf (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) : Pair pr :=
  ⟨(pre hp U, U), le_rfl⟩

def secP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull s₀ s₁ (pairOf hp U)

theorem pullbackSection_smul₂ (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₀)
    (b : Sec s₀ U.1) : secP hp U (r • b) = algebraMap R₀ R₁ r • secP hp U b :=
  semiHom_secPull hp.w (pairOf hp U) r b

def beta (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) :
    R₁ ⊗[R₀] Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  (Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { toRingHom := secP hp U
      commutes' := fun r ↦ by
        have := pullbackSection_smul₂ hp U r 1
        rw [map_one] at this
        change secP hp U (algebraMap R₀ _ r) = _
        rw [Algebra.algebraMap_eq_smul_one r, this, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          Algebra.algebraMap_eq_smul_one r]
        exact (Algebra.algebraMap_eq_smul_one _).symm }
    (fun _ _ ↦ Commute.all _ _)).toRingHom

theorem beta_tmul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (b : Sec s₀ U.1) : beta hp U (r ⊗ₜ b) = algebraMap R₁ _ r * secP hp U b := by
  simp [beta]

theorem beta_smul (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (r : R₁)
    (x : R₁ ⊗[R₀] Sec s₀ U.1) : beta hp U (r • x) = r • beta hp U x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, beta_tmul, beta_tmul, map_mul, _root_.mul_assoc, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem beta_nat (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) {U V : AffOp X₀} (a : U ⟶ V)
    (x : (ext R₁ (OAff s₀)).obj U) :
    beta hp V.unop (mp (ext R₁ (OAff s₀)) a x) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop x) := by
  revert x
  change ∀ x : R₁ ⊗[R₀] Sec s₀ U.unop.1, _
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (map_zero _).symm
  | tmul r b =>
    have hn := (pairPull hp.w).naturality
      (homOfLE (show pairOf hp V.unop ≤ pairOf hp U.unop from
        Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨fun _ hx ↦ (Subtype.coe_le_coe.2 (leOfHom a.unop) : V.unop.1 ≤ U.unop.1) hx,
          leOfHom a.unop⟩))).op b
    change beta hp V.unop (r ⊗ₜ mp (OAff s₀) a b) = mp (preF hp ⋙ OAff s₁) a (beta hp U.unop (r ⊗ₜ b))
    rw [beta_tmul, beta_tmul]
    erw [map_mul]
    congr 1
    all_goals first | exact ((Sec.res s₁ _).commutes r).symm | exact hn
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy]
    exact (map_add _ _ _).symm

def fwd (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preF hp ⋙ OAff s₁) :=
  ofNat (fun U ↦ beta hp U.unop) (fun a x ↦ beta_nat hp a x) (fun U r x ↦ beta_smul hp U.unop r x)

section PairMaps
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem comp_base_eq (hf : f₁ ≫ pr = pr' ≫ f₀) (y : Y₁) : pr.base (f₁.base y) = f₀.base (pr'.base y) := by
  have := congrArg (fun g : Y₁ ⟶ X₀ ↦ g.base y) hf
  simpa using this

abbrev preP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(pre hp' p.1.1, pre hp p.1.2), fun y hy ↦ by
    show pr.base (f₁.base y) ∈ p.1.2.1
    rw [comp_base_eq hf]; exact p.2 hy⟩

def preFP (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ :=
  (Monotone.functor (f := preP hp hp' hf) fun _ _ h ↦ Subtype.coe_le_coe.1 (Prod.le_def.2
    ⟨show pr' ⁻¹ᵁ _ ≤ pr' ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_fst h)) hx,
     show pr ⁻¹ᵁ _ ≤ pr ⁻¹ᵁ _ from fun _ hx ↦ (Subtype.coe_le_coe.2 (Pair.le_snd h)) hx⟩)).op

def zMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) :
    CoefMap (RingHom.id R₁) (preF hp ⋙ OAff s₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairSnd f₀
  α p := (pairPull h₁).α ((preFP hp hp' hf).obj p)
  naturality a b := (pairPull h₁).naturality ((preFP hp hp' hf).map a) b
  smul p r b := (pairPull h₁).smul ((preFP hp hp' hf).obj p) r b

def zRes (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (preF hp' ⋙ OAff t₁) (preFP hp hp' hf ⋙ OPair f₁ t₁) where
  G := pairFst f₀
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kMap (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀) :
    CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (preFP hp hp' hf ⋙ OPair f₁ t₁) :=
  ofNat (fun p ↦ beta hp' p.unop.1.1) (fun a x ↦ beta_nat hp' ((pairFst f₀).map a) x)
    (fun p r x ↦ beta_smul hp' _ r x)

end PairMaps

section Pointwise
variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
  {X₀ X₁ Y₀ Y₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}
  {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁} {pr' : Y₁ ⟶ Y₀} {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}

theorem preF_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (x : X₁) (U : X₁.Opens) (hx : x ∈ U) :
    ∃ t : AffOp X₀, x ∈ ((preF hp).obj t).unop.1 ∧ ((preF hp).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x) (U := W₀) hx
  exact ⟨Opposite.op ⟨V, hV⟩, hxV, fun y hy ↦ hVW hy⟩

theorem preF_dir (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hW : ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W) (t₁ t₂ : AffOp X₀) (x : X₁) (U : X₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preF hp).obj t₁).unop.1) (h₂ : x ∈ ((preF hp).obj t₂).unop.1) :
    ∃ t₃ : AffOp X₀, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ ((preF hp).obj t₃).unop.1 ∧
      ((preF hp).obj t₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := pr.base x)
    (U := W₀ ⊓ t₁.unop.1 ⊓ t₂.unop.1) ⟨⟨hx, h₁⟩, h₂⟩
  exact ⟨Opposite.op ⟨V, hV⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₁.unop from fun y hy ↦ (hVW hy).1.2)).op⟩,
    ⟨(homOfLE (show (⟨V, hV⟩ : X₀.affineOpens) ≤ t₂.unop from fun y hy ↦ (hVW hy).2)).op⟩,
    hxV, fun y hy ↦ (hVW hy).1.1⟩

theorem preFP_cover (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (x : Y₁) (U : Y₁.Opens) (hx : x ∈ U) :
    ∃ t : (Pair f₀)ᵒᵖ, x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ∧
      ((preFP hp hp' hf ⋙ pairFst f₁).obj t).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := (⊤ : X₀.Opens)) trivial
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ f₀ ⁻¹ᵁ V) ⟨hx, hxV⟩
  exact ⟨Opposite.op ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩, hxV', fun z hz ↦ (hV'W hz).1⟩

theorem preFP_directed (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)))
    (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (hf : f₁ ≫ pr = pr' ≫ f₀)
    (hW : ∀ W : Y₁.Opens, ∃ W₀ : Y₀.Opens, pr' ⁻¹ᵁ W₀ = W) (a₁ a₂ : (Pair f₀)ᵒᵖ) (x : Y₁) (U : Y₁.Opens)
    (hx : x ∈ U) (h₁ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₁).unop.1)
    (h₂ : x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₂).unop.1) :
    ∃ a₃ : (Pair f₀)ᵒᵖ, Nonempty (a₁ ⟶ a₃) ∧ Nonempty (a₂ ⟶ a₃) ∧
      x ∈ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ∧ ((preFP hp hp' hf ⋙ pairFst f₁).obj a₃).unop.1 ≤ U := by
  obtain ⟨W₀, rfl⟩ := hW U
  have g₁ : f₀.base (pr'.base x) ∈ a₁.unop.1.2.1 := a₁.unop.2 h₁
  have g₂ : f₀.base (pr'.base x) ∈ a₂.unop.1.2.1 := a₂.unop.2 h₂
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (x := f₀.base (pr'.base x))
    (U := a₁.unop.1.2.1 ⊓ a₂.unop.1.2.1) ⟨g₁, g₂⟩
  obtain ⟨V', hV', hxV', hV'W⟩ := exists_isAffineOpen_mem_and_subset (x := pr'.base x)
    (U := W₀ ⊓ a₁.unop.1.1.1 ⊓ a₂.unop.1.1.1 ⊓ f₀ ⁻¹ᵁ V) ⟨⟨⟨hx, h₁⟩, h₂⟩, hxV⟩
  let a₃ : Pair f₀ := ⟨(⟨V', hV'⟩, ⟨V, hV⟩), fun z hz ↦ (hV'W hz).2⟩
  refine ⟨Opposite.op a₃, ⟨(homOfLE (show a₃ ≤ a₁.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.1.2, fun z hz ↦ (hVW hz).1⟩))).op⟩,
    ⟨(homOfLE (show a₃ ≤ a₂.unop from Subtype.coe_le_coe.1 (Prod.le_def.2
      ⟨fun z hz ↦ (hV'W hz).1.2, fun z hz ↦ (hVW hz).2⟩))).op⟩, hxV', fun z hz ↦ (hV'W hz).1.1.1⟩

end Pointwise

end GlobalTheory.Obs.BaseChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorLbPowMonoOfGenerated
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleTwistLarger

theorem isAmpleLB_tens_lbPow_succ {S : Scheme.{0}} {L M : LB S} {N m : ℕ} (hL : L.IsLB) (hM : M.IsLB)
    (hG : GlobalTheory.IsGenerated (lbPow L N)) (hA : GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * m)) M)) :
    GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * (m + 1))) M) := by
  have h₁ := GlobalTheory.isLB_lbPow hL (N * (m + 1))
  have h₂ := GlobalTheory.isLB_lbPow hL (N * m)
  have h₃ := GlobalTheory.isLB_lbPow hL N
  have hT := GlobalTheory.CechPic.isLB_tens h₁ hM
  have hS := GlobalTheory.CechPic.isLB_tens h₂ hM
  have hq := LB.isLB_div hT hS
  refine hA.tensor_isGenerated hG hT ((GlobalTheory.CechPic.cls_eq_zero_iff (LB.isLB_div hq h₃)).1 ?_)
  rw [GlobalTheory.CechPic.cls_div hq h₃, GlobalTheory.CechPic.cls_div hT hS, GlobalTheory.CechPic.cls_tens h₁ hM,
    GlobalTheory.CechPic.cls_tens h₂ hM, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_lbPow hL,
    Nat.mul_succ, add_smul]
  abel

theorem isAmpleLB_tens_lbPow_of_le : ∀ (S : Scheme.{0}) (L M : LB S) (N k : ℕ), L.IsLB → M.IsLB → GlobalTheory.IsGenerated (lbPow L N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k)) M) → ∀ k', k ≤ k' → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow L (N * k')) M) := by
  intro S L M N k hL hM hG hA k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact isAmpleLB_tens_lbPow_succ hL hM hG ih

end GlobalTheory.AmpleTwistLarger
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitSpecQuotientComplementaryIdempotents
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits

theorem specQuotIdemCoprod_bij (R : Type) [CommRing R] (e e' : R) (he : IsIdempotentElem e)
    (hs : e + e' = 1) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))) := by
  have he' : e' = 1 - e := by rw [← hs]; ring
  have hee : e * e' = 0 := by rw [he', mul_sub, _root_.mul_one, he.eq, sub_self]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [RingHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := hx
    have h1 : a * e * e' = 0 := by rw [_root_.mul_assoc, hee, mul_zero]
    have h2 : a * e * e = 0 := by
      rw [← hb, _root_.mul_assoc, mul_comm e' e, hee, mul_zero]
    calc a * e = a * e * (e + e') := by rw [hs, _root_.mul_one]
      _ = 0 := by rw [mul_add, h1, h2, add_zero]
  · rintro ⟨x, y⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨a * e' + b * e, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq]
    constructor
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨b - a, by rw [he']; ring⟩
    · rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨a - b, by rw [he']; ring⟩

theorem specQuotIdemCoprod : ∀ (R : Type) [CommRing R] (e e' : R), IsIdempotentElem e → e + e' = 1 → Nonempty (Limits.IsColimit (Limits.BinaryCofan.mk (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e'}))))) := by
  intro R _ e e' he hs
  let A := R ⧸ Ideal.span {e}
  let B := R ⧸ Ideal.span {e'}
  let φ : R →+* A × B := (Ideal.Quotient.mk (Ideal.span {e})).prod
      (Ideal.Quotient.mk (Ideal.span {e'}))
  have hφ : Function.Bijective φ := specQuotIdemCoprod_bij R e e' he hs
  let ψ : R ≃+* A × B := RingEquiv.ofBijective φ hφ
  let g : Spec (CommRingCat.of A) ⨿ Spec (CommRingCat.of B) ⟶ Sp R :=
    coprodSpec A B ≫ Spec.map (CommRingCat.ofHom φ)
  haveI : IsIso (Spec.map (CommRingCat.ofHom φ)) := by
    have : IsIso (CommRingCat.ofHom φ) := by
      change IsIso (RingEquiv.toCommRingCatIso ψ).hom
      infer_instance
    infer_instance
  haveI : IsIso g := by dsimp only [g]; infer_instance
  let i := asIso g
  refine ⟨IsColimit.ofIsoColimit (coprodIsCoprod (Spec (CommRingCat.of A)) (Spec (CommRingCat.of B)))
    (Cocone.ext i ?_)⟩
  rintro ⟨⟨⟩⟩
  · simp only [i, asIso_hom, g]
    show coprod.inl ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inl_assoc, ← Spec.map_comp]
    rfl
  · simp only [i, asIso_hom, g]
    show coprod.inr ≫ coprodSpec A B ≫ _ = spMap _
    rw [coprodSpec_inr_assoc, ← Spec.map_comp]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroSummand

variable {R : Type} [CommRing R] (I : Ideal R) {C : Type 1} [AddCommGroup C] [Module R C]

theorem smul_top_eq_sup {P Q : Submodule R C} (h : IsCompl P Q) :
    I • (⊤ : Submodule R C) = I • P ⊔ I • Q := by
  rw [← h.sup_eq_top, Submodule.smul_sup]

theorem sup_smul_top_eq {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊔ I • (⊤ : Submodule R C) = P ⊔ I • Q := by
  rw [smul_top_eq_sup I h, ← sup_assoc, sup_eq_left.mpr (Submodule.smul_le_right : I • P ≤ P)]

theorem inf_smul_top {P Q : Submodule R C} (h : IsCompl P Q) :
    P ⊓ I • (⊤ : Submodule R C) = I • P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxP, hxJ⟩ := Submodule.mem_inf.mp hx
    rw [smul_top_eq_sup I h, Submodule.mem_sup] at hxJ
    obtain ⟨a, ha, b, hb, rfl⟩ := hxJ
    have hbQ : b ∈ Q := Submodule.smul_le_right hb
    have hbP : b ∈ P := by
      have e : b = (a + b) - a := by abel
      rw [e]; exact P.sub_mem hxP (Submodule.smul_le_right ha)
    have hb0 : b = 0 := (Submodule.disjoint_def.mp h.disjoint) b hbP hbQ
    simpa [hb0] using ha
  · exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)

theorem smul_smul_top (hI : I ^ 2 = 0) : I • I • (⊤ : Submodule R C) = ⊥ := by
  rw [← Submodule.mul_smul, ← sq, hI, Submodule.zero_eq_bot, Submodule.bot_smul]

theorem smul_le_of_sup_eq (hI : I ^ 2 = 0) {K F : Submodule R C}
    (h : K ⊔ I • ⊤ = F ⊔ I • ⊤) : I • K ≤ I • F := by
  calc I • K ≤ I • (K ⊔ I • ⊤) := Submodule.smul_mono le_rfl le_sup_left
    _ = I • F := by rw [h, Submodule.smul_sup, smul_smul_top I hI, sup_bot_eq]

end GlobalTheory.SqZeroSummand


open GlobalTheory.SqZeroSummand in
theorem GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero :
    ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  intro R _ I hI C _ _ F K N hFN hKF
  have isCompl_of : K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N := by
    intro hi
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxK hxN
      have hx : x ∈ F ⊔ I • N := by
        rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hxK
      obtain ⟨y, hy, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      have hbN : b ∈ N := Submodule.smul_le_right hb
      have hyN : y ∈ N := by
        have e : y = (y + b) - b := by abel
        rw [e]; exact N.sub_mem hxN hbN
      have hy0 : y = 0 := (Submodule.disjoint_def.mp hFN.disjoint) y hy hyN
      subst hy0
      rw [zero_add] at hxK hxN ⊢
      have hbJ : b ∈ K ⊓ I • (⊤ : Submodule R C) :=
        ⟨hxK, Submodule.smul_mono le_rfl le_top hb⟩
      rw [hi] at hbJ
      exact (Submodule.disjoint_def.mp hFN.disjoint) b hbJ.1 hbN
    · rw [codisjoint_iff, eq_top_iff, ← hFN.sup_eq_top]
      have h1 : I • F ≤ K := by
        have : I • F ≤ K ⊓ I • ⊤ := by
          rw [hi]; exact le_inf Submodule.smul_le_right (Submodule.smul_mono le_rfl le_top)
        exact this.trans inf_le_left
      have h2 : F ≤ K ⊔ N := by
        calc F ≤ F ⊔ I • ⊤ := le_sup_left
          _ = K ⊔ I • ⊤ := hKF.symm
          _ = K ⊔ (I • F ⊔ I • N) := by rw [smul_top_eq_sup I hFN]
          _ ≤ K ⊔ N := sup_le le_sup_left
              (sup_le (h1.trans le_sup_left) (Submodule.smul_le_right.trans le_sup_right))
      exact sup_le h2 le_sup_right
  refine ⟨isCompl_of, ?_⟩
  rintro ⟨N', hKN'⟩
  have hi : K ⊓ I • ⊤ = F ⊓ I • ⊤ := by
    rw [inf_smul_top I hKN', inf_smul_top I hFN]
    exact le_antisymm (smul_le_of_sup_eq I hI hKF) (smul_le_of_sup_eq I hI hKF.symm)
  have hKN := isCompl_of hi
  refine ⟨hi, (N.projection K hKN.symm) ∘ₗ F.subtype, ?_, ?_, ?_⟩
  · intro c
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    refine ⟨?_, Submodule.projection_apply_mem _ _, Submodule.sub_projection_mem _ _⟩
    have hc : c.1 ∈ K ⊔ I • N := by
      rw [← sup_smul_top_eq I hKN, hKF]; exact Submodule.mem_sup_left c.2
    obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp hc
    rw [← hkb, map_add (f := _), (Submodule.projection_apply_eq_zero_iff _).mpr hk, zero_add,
      Submodule.projection_apply_of_mem_left _ (Submodule.smul_le_right hb)]
    exact Submodule.smul_mono le_rfl le_top hb
  · intro c hc
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have h' : c.1 ∈ K ⊓ I • (⊤ : Submodule R C) := by rw [hi]; exact ⟨c.2, hc⟩
    exact (Submodule.projection_apply_eq_zero_iff _).mpr h'.1
  · intro k hk
    have hk' : k ∈ F ⊔ I • N := by
      rw [← sup_smul_top_eq I hFN, ← hKF]; exact Submodule.mem_sup_left hk
    obtain ⟨f, hf, b, hb, hfb⟩ := Submodule.mem_sup.mp hk'
    refine ⟨⟨f, hf⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    have hbN : b ∈ N := Submodule.smul_le_right hb
    have ef : f = k - b := by rw [← hfb]; abel
    rw [ef, map_sub, (Submodule.projection_apply_eq_zero_iff _).mpr hk,
      Submodule.projection_apply_of_mem_left _ hbN]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso : ∀ (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (b' : B' ⟶ S') (P' : LB (A ⊗ B').left), Rep A b P → Rep A b' P' → ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  first | exact @GlobalTheory.DualCon.rep_unique | exact GlobalTheory.DualCon.rep_unique | (intros; apply GlobalTheory.DualCon.rep_unique <;> assumption)
end

