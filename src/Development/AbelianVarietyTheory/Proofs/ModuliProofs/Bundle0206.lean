module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open GlobalTheory.HeckePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_transfer_pts {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'} {X S : Scheme.{0}}
    {sX : X ⟶ Sp B} {s : S ⟶ Sp B'} {u : Obj D l b sX} {o : Obj D l b' s} {f : S ⟶ X} (m : ObjMap o u f)
    {k : Type} [Field k] (z : Sp k ⟶ S) :
    ∃ ρ : (Over.mk z ⟶ o.t.G) ≃* (Over.mk (z ≫ f) ⟶ u.t.G),
      (∀ x, (ρ x).left = x.left ≫ m.toSABMap.φ) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (toUnit _ ≫ o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (toUnit _ ≫ o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (Over.mk z) (z ≫ f) rfl
  obtain ⟨w, hw, -⟩ := m.lin
  have tu : (toUnit (Over.mk z)).left = z := by simp
  have tv : (toUnit (Over.mk (z ≫ f))).left = z ≫ f := by simp
  refine ⟨ρ, hρ, fun a x => Over.OverMorphism.ext ?_,
    fun n x x' c => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩
      (Over.mk z) n x x' _ _ _ (hρ x) (hρ x'), fun a => Over.OverMorphism.ext ?_,
    fun a => Over.OverMorphism.ext ?_⟩
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.eta a, Category.assoc]
  · rw [hρ, Over.comp_left, Over.comp_left, tu, tv, Category.assoc, m.etaA a, Category.assoc]

theorem pointQuot_snd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), admitted l 𝔓 p → ∀ (k : Type) [Field k] [IsAlgClosed k] (z : Sp k ⟶ Z.Hk) (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Z.toKerScheme.Carries z y C → PointQuot Xo p y (z ≫ Z.π₂) C := by
  intro E _ _ _ H D l Xo 𝔓 p i Z hA k _ _ z y C hC
  obtain ⟨rfl, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  have c₂ := Z.m₂.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left :=
    c₁.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z) (by rw [pullback.condition, Category.assoc])
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := c₁.lift_fst _ _ _
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := c₁.lift_snd _ _ _
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  refine ⟨by rw [Category.assoc, Category.assoc, Z.base₂], pullback.lift (α ≫ Z.ψ.left ≫ Z.m₂.cm.F) (pullback.snd _ _)
    (by rw [Category.assoc, Category.assoc, c₂.w, Over.w_assoc, reassoc_of% α₂]), ψp, pullback.lift_snd _ _ _,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P' := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P' n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P.isAb P'.isAb P.isLB P'.isLB hom hiso
      hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinFlatEtSplitTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorusTorsion

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}

theorem val_unitGen {X Y Z : Scheme.{0}} {L : LB X} (u : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) {z : Z} {J} (hJ : Good L z J) :
    val (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u) r z J = gm r z ⊤ u :=
  gm_res _ z le_top (hJ.mem PEmpty.elim _) _

theorem isGen_unitGen {X Y : Scheme.{0}} (L : LB X) (u : Γ(Y, ⊤)ˣ) : (GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen L u).IsGen :=
  fun i j => by
    obtain rfl : i = j := funext fun k => k.elim
    exact ((congrArg₂ (· * ·) (Fintype.prod_empty _) rfl).trans (_root_.one_mul _)).symm

theorem TorusVal.val_eq {g : GtPt D T} {χ : D.X} {u : Γ(T.left, ⊤)ˣ} (h : TorusVal g χ u) {Z : Scheme.{0}}
    (r : Z ⟶ T.left) {z : Z} {J} (hJ : Good D.P.L z J) : val (g.s χ) r z J = gm r z ⊤ u :=
  (val_corr hJ h.2 r).trans (val_unitGen u r hJ)

theorem exists_torusPt (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) :
    ∃ g : GtPt D T, ∀ χ, TorusVal g χ (Additive.toMul (u χ)) := by
  obtain ⟨g, hb, hv⟩ := exists_pt (D := D) (T := T) 1 (K := PEmpty) (φ := fun _ => PEmpty.elim) (ε := PEmpty.elim)
    (fun χ => GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.unitGen D.P.L (Additive.toMul (u χ))) (fun χ => isGen_unitGen _ _)
    (fun χ U i h => (GlobalTheory.FieldRestrictionTest.formEq_zero (D := D) (T := T) χ U h).symm)
    (fun y J hJ => by rw [val_unitGen _ _ hJ, map_zero, toMul_zero, map_one]) (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, val_unitGen _ _ hJ, val_unitGen _ _ hJ, val_unitGen _ _ hJ, map_add (f := _), toMul_add, map_mul,
        _root_.mul_one])
  exact ⟨g, fun χ => ⟨hb, corr_of_val D.P.isLB fun y J hJ => hv χ _ _ y J hJ⟩⟩

theorem isZero_iff' (g : GtPt D T) : g.IsZero ↔ g.b = 1 ∧ ∀ χ y J, Good D.P.L y J → cv g χ y J = 1 :=
  and_congr Iff.rfl (forall_congr' fun _ => ⟨fun h _ _ hJ => (val_corr hJ h _).trans (val_one _),
    fun h => corr_of_val D.P.isLB fun y J hJ => (h y J hJ).trans (val_one _).symm⟩)

theorem exists_nsmul_zero (k : ℕ) (u : D.X →+ Additive Γ(T.left, ⊤)ˣ) (hu : k • u = 0) {g : GtPt D T}
    (hg : ∀ χ, TorusVal g χ (Additive.toMul (u χ))) : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ h.IsZero := by
  choose gs hgs using fun i : ℕ => exists_torusPt (D := D) (T := T) (i • u)
  have z : ∀ i : ℕ, i • u = 0 → (gs i).IsZero := fun i hi => (isZero_iff' _).2 ⟨(hgs i 0).1, fun χ y J hJ => by
    have := TorusVal.val_eq (hgs i χ) (𝟙 _) hJ
    rw [hi] at this
    exact this.trans (map_one _)⟩
  refine ⟨gs k, ⟨fun i => gs i, z 0 (zero_smul _ _), fun i => (TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => ?_⟩,
    rfl⟩, z k hu⟩
  · rw [(hgs _ 0).1, (hgs _ 0).1, (hg 0).1]
    exact (_root_.mul_one (1 : T ⟶ D.P.A)).symm
  · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
    have hb : g.b = 1 := (hg 0).1
    rw [show th D y J (cP D _ χ) (gs (i.castSucc : Fin (k + 1))).b g.b = 1 by rw [hb, C.face₃], _root_.mul_one]
    refine (TorusVal.val_eq (hgs _ χ) _ hJ).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (TorusVal.val_eq (hgs _ χ) _ hJ) (TorusVal.val_eq (hg χ) _ hJ)).symm)
    rw [Fin.val_succ, Fin.val_castSucc, succ_nsmul, AddMonoidHom.add_apply, toMul_add, map_mul]

theorem isPull_of_units (h : T' ⟶ T) {g : GtPt D T} {g' : GtPt D T'} {u : D.X → Γ(T.left, ⊤)ˣ}
    {u' : D.X → Γ(T'.left, ⊤)ˣ} (hg : ∀ χ, TorusVal g χ (u χ)) (hg' : ∀ χ, TorusVal g' χ (u' χ))
    (e : ∀ χ, h.left.appTop.hom (u χ).val = (u' χ).val) : GtPt.IsPull h.left g g' := by
  refine (TorusModel.isPull_iff h g g').2 ⟨?_, fun χ y J hJ => ?_⟩
  · rw [(hg 0).1, (hg' 0).1]
    exact (MonObj.comp_one h).symm
  · refine (TorusVal.val_eq (hg' χ) _ hJ).trans (Eq.trans (Units.ext ?_) (TorusVal.val_eq (hg χ) _ hJ).symm)
    rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial, ← e χ]
    rfl

variable {W : (Sp R).Opens}

end Points

end GlobalTheory.TorusTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
section
noncomputable section

namespace GlobalTheory.FinitePartGeneric

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

theorem exists_normal_factor (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (A : Type) [CommRing A]
    [Algebra R A] [Module.Finite R A] (ψ : A →+* F)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap (FractionRing R) F (algebraMap R _ r)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (a : A →+* R'), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map (a.comp (algebraMap R A)) ≤ maximalIdeal R' ∧
      ∀ y, algebraMap (FractionRing R') F (algebraMap R' _ (a y)) = ψ y := by
  obtain ⟨h₁, -, h₃, h₄⟩ := hR
  letI : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ' : A →ₐ[R] F := { ψ with commutes' := hψ }
  have hi : ∀ y, IsIntegral R (ψ y) := fun y => (Algebra.IsIntegral.isIntegral (R := R) y).map ψ'
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := A)
  let L := IntermediateField.adjoin (FractionRing R) (ψ '' s)
  have : Finite (ψ '' s) := (s.finite_toSet.image ψ).to_subtype
  have : FiniteDimensional (FractionRing R) L :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨y, -, rfl⟩; exact (hi y).tower_top)
  have hm : ∀ y, ψ y ∈ L := fun y => by
    have hy : y ∈ Submodule.span R (s : Set A) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy => rw [Algebra.smul_def, map_mul, hψ]; exact mul_mem (L.algebraMap_mem _) hy
  obtain ⟨f₁, f₂, f₃, f₄, -⟩ := integralClosure_finite_local_of_isAdicComplete R h₄ L
  have : IsScalarTower R L F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let j : integralClosure R L →+* F := (algebraMap L F).comp (algebraMap _ L)
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  let a : A →+* integralClosure R L := (ψ.codRestrict L hm).codRestrict (integralClosure R L) fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R L F) Subtype.val_injective).1 (hi y)
  have ha : a.comp (algebraMap R A) = algebraMap R _ := RingHom.ext fun r => hj (hψ r)
  refine ⟨integralClosure R L, inferInstance, inferInstance, f₂, (IsFractionRing.lift (g := j) hj).toAlgebra, a,
    ⟨f₃, inferInstance, f₄, CompleteFiniteExtension.isAdicComplete_of_finite_local R _⟩, ?_,
    fun y => IsFractionRing.lift_algebraMap (g := j) hj _⟩
  rw [ha]
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) _ _ inferInstance

theorem exists_normal_point (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : Over (Sp R))
    [IsFinite N.hom] (x : Sp F ⟶ N.left) (hx : x ≫ N.hom = jFK (R := R) F ≫ jK R) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : Algebra (FractionRing R') F)
      (φ : R →+* R') (ξ : Sp R' ⟶ N.left), AdmBase R' (maximalIdeal R') ∧
      (maximalIdeal R).map φ ≤ maximalIdeal R' ∧ ArcPull.Compat φ F ∧ ξ ≫ N.hom = spMap φ ∧
      (jFK (R := R') F ≫ jK R') ≫ ξ = x := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (x ≫ N.left.isoSpec.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have e : φ ≫ ψ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc, hx])
  have e' : ∀ r, ψ.hom (φ.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) e
  obtain ⟨R', i₁, i₂, i₃, i₄, a, h₁, h₂, h₃⟩ := exists_normal_factor R hR F Γ(N.left, ⊤) ψ.hom e'
  refine ⟨R', i₁, i₂, i₃, i₄, a.comp φ.hom, Spec.map (CommRingCat.ofHom a) ≫ N.left.isoSpec.inv, h₁, h₂,
    fun r => (e' r).symm.trans (h₃ _).symm, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext h₃))

section Transport

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLin GlobalTheory.FormalPoint
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

theorem isPointOf_thru {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'}
    {hD : IsPullDeg φ D.toPre D'.toPre} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') {T : Over (Sp R)} {T' : Over (Sp R')} {h : T'.left ⟶ T.left}
    {g₀ : GtPt D.toPre T} {g : GtPt D'.toPre T'} (H : Thru hD.w hD.xe h g₀ g) {x₀ : T ⟶ G} {x : T' ⟶ G'}
    (hx : x.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = h ≫ x₀.left)
    (h₀ : IsPointOf U.toUnifPre g₀ x₀) : IsPointOf U'.toUnifPre g x := by
  intro e Z r y hy
  obtain ⟨wL, -, he, -, HU⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  obtain ⟨k, hf, hpt, -⟩ := HU e
  have gp := pull_grp hD
  obtain ⟨cb, cv⟩ := (hasCoords_iff _ _ _ _ _).1 (h₀ e Z (r ≫ h) (y ≫ k) (by
    rw [Category.assoc, hf, ← Category.assoc, hy, Category.assoc, hx, Category.assoc]))
  have hy' : y ≫ ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom = r ≫ T'.hom := by
    rw [← Over.w (fstG I' e G'), ← Category.assoc, hy, Category.assoc, Over.w]
  let y' : Over.mk (r ≫ T'.hom) ⟶ (Over.map (thick R' I' e)).obj (thickObj R' I' e G') := Over.homMk y hy'
  let r' : Over.mk (r ≫ T'.hom) ⟶ T' := Over.homMk r rfl
  have hb : y ≫ (U'.gt e).pG.left = r ≫ g.b.left := gp.1.hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (y ≫ ·) hpt.1).trans ((Category.assoc _ _ _).symm.trans (cb.trans
      ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) ((H 0).1 2).symm).trans (Category.assoc _ _ _).symm))))))
    (by rw [Category.assoc, Category.assoc, Over.w, Over.w]; exact hy')
  refine (hasCoords_iff _ _ _ _ _).2 ⟨hb, fun χ z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
  have v := ConstFam.pmaps_val (hpt.2 χ).1 (hpt.2 χ).2 y hJ hJ'
  have eP : ∏ i, ConstFam.wVal hD.w z J J' (y ≫ D'.toPre.Oφ (U'.gt e).pG χ i) ^ Oinvε i =
      ∏ i, ConstFam.wVal hD.w z J J' (r ≫ DegPre.gtφT D'.toPre T' g.b χ i) ^ DegPre.gtε i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w z J J' q ^ DegPre.gtε i)
      (comp_Oφ y' r' _ _ (Over.OverMorphism.ext hb) χ i)
  rw [eP] at v
  exact mul_left_cancel (v.symm.trans ((cv _ z J hJ).trans ((H χ).2 _ r z J J' hJ hJ')))

theorem isPullGtF_thru {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} {T : Over (Sp R)} {T' : Over (Sp R')}
    {h : T'.left ⟶ T.left} {g₀ : GtPt D T} {g : GtPt D' T'} (H : Thru hD.w hD.xe h g₀ g) {F : Type} [Field F]
    [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] {σ : Sp F ⟶ T'.left} {q : GtPtF D F}
    {q' : GtPtF D' F} (hq : GtPt.IsPullF F (σ ≫ h) g₀ q) (hq' : GtPt.IsPullF F σ g q') : IsPullGtF φ hD F q q' := by
  have m := FieldRestrictionTest.maps_eq hq
  have m' := FieldRestrictionTest.maps_eq hq'
  have hψ : ∀ χ i, DegPre.gtφ D' F q'.b χ i ≫ proj hD = 𝟙 _ ≫ DegPre.gtφ D F q.b (hD.xe χ) i := fun χ i => by
    rw [m, m', Category.id_comp]
    exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) ((H χ).1 i)).trans (Category.assoc _ _ _).symm)
  refine ⟨(hψ 0 2).trans (Category.id_comp _), fun χ => ⟨hψ χ, maps_of_good ((isGen_iff _).1 hD.w_gen) D.P.isLB
    D'.P.isLB _ (q'.isGen χ) _ (q.isGen _) (hψ χ) fun y J J' hJ hJ' => ?_⟩⟩
  have a := (val_corr hJ (hq.2 (hD.xe χ)) (𝟙 _)).trans (val_pull hJ _ _ _)
  have a' := (val_corr hJ' (hq'.2 χ) (𝟙 _)).trans (val_pull hJ' _ _ _)
  rw [Category.id_comp] at a a'
  refine a.trans (((H χ).2 _ σ y J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ a'.symm))
  exact Finset.prod_congr rfl fun i _ => congrArg (fun q => ConstFam.wVal hD.w y J J' q ^ DegPre.gtε i) (m' χ i).symm

end Transport

theorem main : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∀ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinitePart P.U.toUnifPre k N g₀ x₀ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : Sp F ⟶ N.left), OverGen F N x → ∀ q : QkPt P.D.toPre F k, q.y = 0 → GtPt.IsPullF F x g₀ q.g → IsImage P F k q (x ≫ x₀.left) := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk N g₀ x₀ hN F _ _ _ x hx q hq hg
  have hL := firstFiveLaws
  have := hN.finite
  obtain ⟨R', _, _, _, _, φ, ξ, hR', hI, hF, hξ, rfl⟩ := exists_normal_point R hR F N x hx
  have hφ : Function.Injective φ := fun a b e => IsFractionRing.injective R (FractionRing R)
    ((algebraMap (FractionRing R) F).injective (by rw [hF a, hF b, e]))
  obtain ⟨D', hD, A', U', hU⟩ := UT.EndBaseChange.exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange
    hL.2.2.2.2.psiOnExists hR hR' φ hφ hI t.semi P.U
  have hh : ξ ≫ N.hom = (𝟙_ (Over (Sp R'))).hom ≫ spMap φ := hξ.trans (Category.id_comp _).symm
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp R'))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh g₀
  let x₁ : 𝟙_ (Over (Sp R')) ⟶ (Over.pullback (specOf φ)).obj t.G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp R'))).hom (by rw [Category.assoc, Over.w]; exact hh))
      (pullback.lift_snd _ _ _)
  have e₁ : x₁.left ≫ pullback.fst t.G.hom (specOf φ) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ (Iso.refl ((Over.pullback (specOf φ)).obj t.G)).hom.left ≫ pullback.fst t.G.hom (specOf φ) =
      ξ ≫ x₀.left := (congrArg (x₁.left ≫ ·) (Category.id_comp _)).trans e₁
  have gG := isGrpPullback_pullback t.G (spMap φ)
  have hk₁ : x₁ ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ⟶ N := Over.homMk ξ hh
    have e : pushHom gG _ x₁ = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, hN.g_tors, MonObj.comp_one])
  have hp := isPointOf_thru hU hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hN.formal)
  obtain ⟨g', hg'⟩ := FieldRestrictionTest.exists_isPullF (toUnit (TF (R := R') F)) gp
  let y : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj t.G :=
    Over.homMk (pullback.lift (((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left) (jFK (R := R) F)
      (by rw [Category.assoc, Over.w]; exact hx)) (pullback.lift_snd _ _ _)
  have hy : (y ≫ P.U.gen.hom).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      ((jFK (R := R') F ≫ jK R') ≫ ξ) ≫ x₀.left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  refine ⟨_, hy, FiniteTorsionExt.main hL.1 R R' _ _ hR hR' φ P.D P.A t.G P.U _ (Iso.refl _)
    (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hU (maximalIdeal.isMaximal R').ne_top F hF k hk x₁ gp hk₁
    (fun e => ?_) q g' _ hq (isPullGtF_thru hgp hg hg') hg' ?_⟩
  · let xe : Over.mk (thick R' (maximalIdeal R') e) ⟶ (Over.map (thick R' (maximalIdeal R') e)).obj
        (thickObj R' (maximalIdeal R') e ((Over.pullback (specOf φ)).obj t.G)) :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick R' (maximalIdeal R') e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick R' (maximalIdeal R') e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩
  · rw [hy, Over.comp_left, Category.assoc (toUnit (TF (R := R') F)).left, e₂]
    exact Category.assoc _ _ _

end GlobalTheory.FinitePartGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.MulFiniteFlat

open GlobalTheory.AbLaw.MulN

theorem finite_preimage_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left) (y : Y.left) : (f.left ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hv : pullback.fst Y.hom t (v p) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)
  have hfin := ((Over.pullback t).map f).left.finite_preimage_singleton (v p)
  refine (hfin.image (pullback.fst X.hom t)).subset fun x hx => ?_
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback (isPullback_baseChange t f) x (v p)
    ((show f.left x = y from hx).trans hv.symm)
  exact ⟨z, hz₂, hz₁⟩

theorem pullback_map_mulA {S T : Scheme.{0}} (t : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ) :
    (Over.pullback t).map (mulA A n) = mulA ((Over.pullback t).obj A) n := by
  change (Over.pullback t).map (𝟙 A ^ n) = 𝟙 _ ^ n
  induction n with
  | zero => rw [pow_zero, pow_zero, Functor.map_one]
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, CategoryTheory.Functor.map_id]

theorem isFinite_and_flat_mul : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  intro S _ A _ _ hA k hk
  change IsFinite (mulA A k).left ∧ Flat (mulA A k).left
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

end GlobalTheory.MulFiniteFlat
end

