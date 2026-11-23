module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionFrameIsUnitAlongSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThird
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y : Fin g → ℂ) : (DegPre.BF D ℂ).left ⟶ (G3 D.P.A).left :=
  (lift (fst _ _ ≫ ν.eA (d.ex x)) (lift (fst _ _ ≫ ν.eA (d.ex y)) (snd _ _))).left

theorem ptB_phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) :
    ptB ν d z ≫ phiXY ν d x y = pt3 ν d x y z := by
  rw [ptB, phiXY, pt3, ← Over.comp_left, comp_lift, lift_fst_assoc, comp_lift, lift_fst_assoc, lift_snd,
    Category.id_comp, Category.id_comp]

theorem isOpen_and_differentiableOn_valF_pt3_cubW : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  intro R _ _ D _ N g ν d G x y j
  have hs : {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} = {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ (phiXY ν d x y ⁻¹ᵁ cubW D j)} := by
    ext z
    simp only [Set.mem_setOf_eq, ← ptB_phiXY ν d x y z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := G.hol (phiXY ν d x y ⁻¹ᵁ cubW D j)
    (((phiXY ν d x y).appLE (cubW D j) (phiXY ν d x y ⁻¹ᵁ cubW D j) le_rfl).hom (D.cub.t.s j).val)
  rw [hs]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have e := UnitVal.valF_appLE' (x := ptB ν d z) (phiXY ν d x y) (cubW D j) le_rfl hz (D.cub.t.s j).val
  rw [ptB_phiXY] at e
  exact e.symm

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueComplexPointsEqFrameAlternatingProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.CubeVal

theorem prod_three' {M : Type} [CommMonoid M] (F : Finset (Fin 3) → M) :
    ∏ s, F s = F ∅ * F {0} * F {1} * F {2} * F {0, 1} * F {0, 2} * F {1, 2} * F {0, 1, 2} := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ac_rfl

theorem prod_three {M : Type} [CommMonoid M] (F : thK.{0} → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{2}⟩ * F ⟨{0, 1}⟩ * F ⟨{0, 2}⟩ * F ⟨{1, 2}⟩ * F ⟨{0, 1, 2}⟩ :=
  (Equiv.prod_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F).symm.trans (prod_three' fun s => F ⟨s⟩)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem ex_sum (d : AB N.toNumB g) {κ : Type} (s : Finset κ) (v : κ → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  have h0 : d.ex 0 = 1 := by
    have e := d.ex_add 0 0
    rw [add_zero] at e
    exact (mul_eq_left.1 e.symm)
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

theorem pt_thφ (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, ex_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  fin_cases i <;> simp [x3]

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl.CubeVal

theorem thε_vals : thε ⟨(∅ : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({1} : Finset (Fin 3))⟩ = 1 ∧
    thε ⟨({2} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({0, 1} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 2} : Finset (Fin 3))⟩ = -1 ∧
    thε ⟨({1, 2} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 1, 2} : Finset (Fin 3))⟩ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem prod_const_zpow (r : ℂ) (hr : r ≠ 0) : ∏ I : thK.{0}, r ^ thε I = 1 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  field_simp

theorem alg (a b f : thK.{0} → ℂ) (r θ V : ℂ) (hr : r ≠ 0) (hf : ∀ I, f I ≠ 0) (h : ∀ I, f I * r = a I * b I)
    (h1 : θ = (∏ I, a I ^ thε I) * V) (h2 : θ = ∏ I, f I ^ thε I) : V = ∏ I, b I ^ thε I := by
  have ha : ∀ I, a I ≠ 0 := fun I => left_ne_zero_of_mul (h I ▸ mul_ne_zero (hf I) hr)
  have hA : (∏ I, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hAB : (∏ I, a I ^ thε I) * ∏ I, b I ^ thε I = ∏ I, f I ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ I, a I ^ thε I * b I ^ thε I = f I ^ thε I * r ^ thε I := fun I => by
      rw [← mul_zpow, ← mul_zpow, h I]
    simp only [e, Finset.prod_mul_distrib, prod_const_zpow r hr, _root_.mul_one]
  rw [h1] at h2
  exact mul_left_cancel₀ hA (h2.trans hAB.symm)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem theta_eq_prod (d : AB N.toNumB g) (hc : d.Cub) (x y z : Fin g → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = ∏ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) ^ thε I := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  have h := congrArg Units.val (hc x y z)
  simp only [Units.val_mul] at h
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  simp [Finset.sum_insert, d.fr_zero, ← add_assoc]
  have := (d.fr (x + y)).ne_zero
  have := (d.fr (x + z)).ne_zero
  have := (d.fr (y + z)).ne_zero
  field_simp
  linear_combination h

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl


open CubeVal in
theorem cube_val_frame : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  intro R _ _ D _ N g ν d hc G x y z j hj
  have hpt := pt_thφ ν d x y z
  set p := (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left with hp
  have htr : ∀ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) * ν.rg =
      valF (p ≫ thφ D.P.A (x3 D.P.A) I) (D.P.L.U (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓ D.P.L.U (j I))
        (D.P.L.g (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) (j I)).val * G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) := by
    intro I
    rw [hpt I, G.fr_eq]
    exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hj I (x := q) trivial⟩
  have hin : ⊤ ≤ p ⁻¹ᵁ (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I => ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓
      LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j) := fun q _ =>
    ⟨Set.mem_iInter.2 fun I => ν.good (p ≫ thφ D.P.A (x3 D.P.A) I) (x := q) trivial,
      Set.mem_iInter.2 fun I => by
        have h := hj I
        rw [← hpt I] at h
        exact h (x := q) trivial⟩
  have e1 := PullbackSections.vtf_isGen_val D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen p _ j hin
  have e2 := ν.θ_eq (d.ex x) (d.ex y) (d.ex z)
  exact alg _ _ (fun I => (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ)) ν.rg _ _ (SymFrame.rg_ne ν) (fun I => Units.ne_zero _)
    htr (e2.trans e1) (theta_eq_prod d hc x y z)

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGauge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

section Val
variable {F : Type} [Field F] {X : Scheme.{0}}

theorem valF_eq_hom (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF x U f = ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valF
  rw [dite_eq_left h]
  rfl

theorem valF_zpow (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valF x U (u ^ n).val = valF x U u.val ^ n := by
  rw [valF_eq_hom x h, valF_eq_hom x h]
  have e := congrArg Units.val
    (map_zpow (Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (x.appLE U ⊤ h).hom).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val] at e
  exact e

theorem valF_prod {K : Type} [Fintype K] (x : Sp F ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : K → Γ(X, U)ˣ) :
    valF x U (∏ k, u k).val = ∏ k, valF x U (u k).val := by
  simp only [valF_eq_hom x h, Units.coe_prod, map_prod]

end Val

theorem cubF_mul_prod_fr {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) :
    cubF d x y z * ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I = (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) := by
  have p := GlobalTheory.FrameValue.prod_thK (fun s : Finset (Fin 3) => ((d.fr (∑ a ∈ s, ![x, y, z] a) : ℂˣ) : ℂ))
  simp only [GlobalTheory.FrameValue.sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, d.fr_zero, Units.val_one] at p
  simp only [wI]
  rw [p, cubF, inv_one, _root_.mul_one]
  have h1 := (d.fr (x + y + z)).ne_zero
  have h2 := (d.fr (x + y)).ne_zero
  have h3 := (d.fr (x + z)).ne_zero
  have h4 := (d.fr (y + z)).ne_zero
  have h5 := (d.fr x).ne_zero
  have h6 := (d.fr y).ne_zero
  have h7 := (d.fr z).ne_zero
  field_simp

theorem cubF_mul_prod_frG {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι)
    (hj : ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j) :
    cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I =
      valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  set r := pt3 ν d x y z with hr
  set φ := thφ D.P.A (x3 D.P.A) with hφ
  set J' : thK → D.P.L.ι := fun I => ν.J (r ≫ φ I) with hJ'
  have hθ : (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = valF r (cubW D J') (D.cub.t.s J').val := ν.θ_eq _ _ _
  have hgood : ⊤ ≤ r ⁻¹ᵁ cubW D J' := fun p _ => Set.mem_iInter.2 fun I => ν.good (r ≫ φ I) (x := p) trivial
  have hboth := GlobalTheory.ZH.TorsFrame.le_preimage_inf r hgood hj
  have hg := D.cub.isGen J' j
  have e2 : valF r (cubW D J') (D.cub.t.s J').val =
      valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val * valF r (cubW D j) (D.cub.t.s j).val :=
    (GlobalTheory.ZH.TorsFrame.valF_res r (inf_le_left : cubW D J' ⊓ cubW D j ≤ cubW D J') hboth (D.cub.t.s J')).symm.trans
      ((congrArg (fun u => valF r (cubW D J' ⊓ cubW D j) (Units.val u)) hg).trans
        ((GlobalTheory.ZH.TorsFrame.valF_mul r hboth _ _).trans
          (congrArg (_ * ·) (GlobalTheory.ZH.TorsFrame.valF_res r inf_le_right hboth _))))
  have e3 : valF r (cubW D J' ⊓ cubW D j) ((Theta D.P.A D.P.L).g J' j).val =
      ∏ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val ^ thε I := by
    refine (valF_prod r hboth _).trans (Finset.prod_congr rfl fun I _ => ?_)
    refine (valF_zpow r hboth _ _).trans ?_
    congr 1
    exact (GlobalTheory.ZH.TorsFrame.valF_res r _ hboth _).trans (GlobalTheory.ZH.TorsFrame.valF_pullU r (φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)))
  have hc : ∀ I : thK, valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg := by
    intro I
    have hin : ⊤ ≤ (r ≫ φ I) ⁻¹ᵁ (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) := fun p _ =>
      ⟨ν.good (r ≫ φ I) (x := p) trivial, Set.mem_iInter.1 (hj (x := p) trivial) I⟩
    have hp : r ≫ φ I = (ν.eA (d.ex (wI x y z I))).left := complexCubeAbelianPoint_thetaFace_eq_partialSum ν d x y z I
    show valF (r ≫ φ I) (D.P.L.U (ν.J (r ≫ φ I)) ⊓ D.P.L.U (j I)) (D.P.L.g (ν.J (r ≫ φ I)) (j I)).val *
      geo.frG (j I) (wI x y z I) = d.fr (wI x y z I) * ν.rg
    rw [hp] at hin ⊢
    rw [geo.fr_eq]
    exact (geo.fr_compat _ _ _ hin).symm
  have hrg : ν.rg ≠ 0 := GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν
  set a : thK → ℂ := fun I => valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val with ha_def
  set fG : thK → ℂ := fun I => geo.frG (j I) (wI x y z I) with hfG
  set V := valF r (cubW D j) (D.cub.t.s j).val with hV
  set θ : ℂ := (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) with hθd
  have hθ' : θ = (∏ I : thK, a I ^ thε I) * V := by rw [hθ, e2, e3]
  have ha : ∀ I, a I ≠ 0 := fun I h0 => by
    have := hc I
    rw [show valF (r ≫ φ I) (D.P.L.U (J' I) ⊓ D.P.L.U (j I)) (D.P.L.g (J' I) (j I)).val = a I from rfl, h0,
      zero_mul] at this
    exact mul_ne_zero (Units.ne_zero _) hrg this.symm
  have hPa : (∏ I : thK, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hrg1 : (∏ _I : thK, ν.rg ^ thε _I) = 1 := by
    have p := GlobalTheory.FrameValue.prod_thK (fun _ : Finset (Fin 3) => ν.rg)
    refine p.trans ?_
    field_simp
  have hP : (∏ I : thK, a I ^ thε I) * (∏ I : thK, fG I ^ thε I) =
      ∏ I : thK, ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have : ∀ I : thK, a I ^ thε I * fG I ^ thε I = ((d.fr (wI x y z I) : ℂˣ) : ℂ) ^ thε I * ν.rg ^ thε I :=
      fun I => by rw [← mul_zpow, ← mul_zpow]; exact congrArg (· ^ thε I) (hc I)
    rw [Finset.prod_congr rfl fun I _ => this I, Finset.prod_mul_distrib, hrg1, _root_.mul_one]
  have hcub := cubF_mul_prod_fr d x y z
  show cubF d x y z * ∏ I : thK, fG I ^ thε I = V
  refine mul_left_cancel₀ hPa ?_
  linear_combination cubF d x y z * hP + hcub + hθ'

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_clear_denominators_away_from_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  first | exact @GlobalTheory.RefSum.Clear.clear | exact GlobalTheory.RefSum.Clear.clear | (intros; apply GlobalTheory.RefSum.Clear.clear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem isOpenMap_scheme_comp {X₁ X₂ X₃ : Scheme.{0}} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (hf : IsOpenMap f)
    (hg : IsOpenMap g) : IsOpenMap (f ≫ g) := hg.comp hf

theorem isOpenMap_cbase {X : Scheme.{0}} {T : Type} (m : T → ℕ) (U : X.affineOpens) : IsOpenMap (cbase m U) := by
  haveI : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact isOpenMap_scheme_comp (MvPolynomial.isOpenMap_comap_C) U.2.fromSpec.isOpenEmbedding.isOpenMap

theorem dense_genMap_preimage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ
  have hcell : ∀ b w, IsOpenMap (κ b w ≫ π) := fun b w => by
    rw [hZ.plk.base b w]; exact isOpenMap_cbase _ _
  have hπ : IsOpenMap π := by
    intro O hO
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hZ.cover z
    refine ⟨(κ b w ≫ π) '' (κ b w ⁻¹' O), ?_, hcell b w _ (hO.preimage (κ b w).continuous), y, hz, rfl⟩
    rintro _ ⟨y', hy', rfl⟩
    exact ⟨κ b w y', hy', rfl⟩
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]; infer_instance
  have he : genMap π = pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F)) ≫ π ≫
      inv (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    rw [← cancel_mono (pullback.fst Y.s (spMap (RingHom.id c.F)))]
    simp only [genMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id, pullback.lift_fst]
  have hgen : IsOpenMap (genMap π) := by
    rw [he]
    exact isOpenMap_scheme_comp (pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))).isOpenEmbedding.isOpenMap
      (isOpenMap_scheme_comp hπ (inv (pullback.fst Y.s (spMap (RingHom.id c.F)))).isOpenEmbedding.isOpenMap)
  exact Y.jQ_dense.preimage hgen

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedDataTransportIdentityLevelChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem descData_transport_id : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  intro h n N d B B' _ _ ζ ζ' X Y s s' C c π A₀ _ φ φ₂ P₀ lev₀ hS hA hsq hP₀ hw hlev
  obtain ⟨ψ, hψ, ⟨ψ₂, hsqψ, hC⟩, hlevψ⟩ := hS
  haveI : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl c.A)) hψ
  haveI := he
  have heψ' : e.hom.left ≫ ψ = 𝟙 _ := by simpa using heψ
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hψe : ψ = e.inv.left := by
    rw [← Category.id_comp ψ, ← hie, Category.assoc, heψ', Category.comp_id]
  let E₂ : G2 c.A ⟶ G2 C.A := lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)
  have hE₂ : E₂.left ≫ ψ₂ = 𝟙 _ := by
    have := GlobalTheory.SiegelDescent.lift_square hsqψ (τ := 𝟙 (G2 c.A).left) (a := fst c.A c.A ≫ e.hom)
      (b := snd c.A c.A ≫ e.hom) (a₀ := fst c.A c.A) (b₀ := snd c.A c.A)
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
    rw [this, lift_fst_snd, Over.id_left, Category.comp_id]
  refine ⟨e.hom.left ≫ φ, E₂.left ≫ φ₂, ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp π) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h1 : LBIso (C.P.pull E₂.left) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame P₀ _ (fun _ => φ₂) _ E₂.left fun _ => rfl) hw
    have h2 : LBIso (C.P.pull E₂.left) (c.P.pull (E₂.left ≫ ψ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame c.P _ (fun _ => ψ₂) _ E₂.left fun _ => rfl) hC
    have h3 : LBIso (c.P.pull (E₂.left ≫ ψ₂)) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.trans (pull_isLB c.isLB _) (pull_isLB C.isLB _) (pull_isLB hP₀ _) h2.symm h1
    exact LBIso.chartPull (chartPullUnpull c.P _ hE₂)
      (chartPullSame P₀ _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h3
  · intro a
    have h₀ := hlevψ a
    rw [pow_one, Category.id_comp, hψe] at h₀
    rw [← h₀, Category.assoc, ← Category.assoc e.inv.left, hie, Category.id_comp, hlev a]

end GlobalTheory.SiegLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultiplStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_rigidifiedSection_of_scalarMultiple : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G)) (x : KeyIn R'), L.IsLB → IsFibreOf x G L rig θ w f → ∀ (θ₀ : L.Sec) (b : R), IsMul (X := G) θ b θ₀ → ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀), (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧ IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  first | exact @GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | exact GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul | (intros; apply GlobalTheory.KeySwapSec.exists_isFibreOf_of_isMul <;> assumption)
end

