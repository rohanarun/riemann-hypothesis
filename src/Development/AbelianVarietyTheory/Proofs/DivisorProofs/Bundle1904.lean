module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormValFUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.AbKey

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (u : Γ(X, U)ˣ) :
    res h (res h' u) = res (h.trans h') u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_unit_sec {X : Scheme.{0}} (L : LB X) (F : X ⟶ X) (hF : F = 𝟙 X) (t : LB.Gen (L.pull F)) (ht : t.IsGen) :
    ∃ s : H0 L 1, ∀ j, IsUnit (s.f j) := by
  subst hF
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨⟨fun j => (res (le j) (t.s fun _ => j 0)).val, fun i j => ?_⟩, fun j => Units.isUnit _⟩
  have h := congrArg (res (inf_le_inf (le i) (le j))) (ht (fun _ => i 0) (fun _ => j 0))
  replace h := h.trans (map_mul (res (inf_le_inf (le i) (le j))) _ _)
  have e : res (inf_le_inf (le i) (le j)) ((L.pull (𝟙 X)).g (fun _ => i 0) (fun _ => j 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j := by
    simp only [LB.pull, LB.LinComb, Fintype.prod_unique, Nat.cast_one, zpow_one]
    exact res_res' _ _ _
  have h' : res inf_le_left (res (le i) (t.s fun _ => i 0)) =
      (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))).g i j *
        res inf_le_right (res (le j) (t.s fun _ => j 0)) := by
    refine ((res_res' _ _ _).trans (res_res' _ _ _).symm).trans (h.trans ?_)
    exact congrArg₂ (· * ·) e ((res_res' _ _ _).trans (res_res' _ _ _).symm)
  exact congrArg Units.val h'

theorem norm_th_one {V : Type} [CommRing V] [IsDomain V] {D : DegPre V} {C : Type} [NormedField C]
    [Algebra (FractionRing V) C] {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) (hg : D.P.g = 0) : ‖N.th 1‖ = 1 := by
  haveI : IsIso D.P.A.hom := GlobalTheory.ZM.Model.isIso_of_dim_zero D.P.A D.P.isAb (hg ▸ D.P.smoothDim)
  have he : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
  have he' : D.P.A.hom ≫ eSec D.P.A = 𝟙 _ := by
    rw [← cancel_mono D.P.A.hom, Category.assoc, Category.id_comp]
    exact (congrArg _ he).trans (Category.comp_id _)
  obtain ⟨s, hs⟩ := exists_unit_sec D.P.L (D.P.A.hom ≫ eSec D.P.A) he'
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom)
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)
  obtain ⟨r, hr⟩ := ν.th_gen s
  have hu : ∀ j, IsUnit (ν.th.f j) := fun j => isUnit_of_mul_isUnit_right (hr j ▸ hs j)
  obtain ⟨S, hS, hI⟩ := hν
  obtain ⟨x₀, hx, hU⟩ := hI (ν.eA 1)
  have h := congrArg norm (ν.th_eq 1)
  have hT : (TF (R := V) C).hom = spMap S.subtype ≫ x₀ ≫ D.P.A.hom := by
    rw [← Over.w (ν.eA 1), ← hx, Category.assoc]
  have hT' : (TF (R := V) C).hom ≫ eSec D.P.A = (ν.eA 1).left := by
    rw [← Over.w (ν.eA 1), Category.assoc]
    exact (congrArg _ he').trans (Category.comp_id _)
  have h1 : ‖sF ν.th (ν.eA 1).left ν.J‖ = 1 := by
    unfold sF
    have := UnitNorm.norm_valF_unit hS x₀ (LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left)
      fun _ => ν.J ((ν.eA 1).left ≫ 𝟙 _)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [Category.comp_id]; exact hU hy) _ (hu _)
    rw [hx] at this
    exact this
  have h2 : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := V) C).hom ν.J‖ = 1 := by
    unfold vF
    have := UnitNorm.norm_valF_unit hS (x₀ ≫ D.P.A.hom) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A)
      fun _ => ν.J ((TF (R := V) C).hom ≫ eSec D.P.A)) (fun y hy => Set.mem_iInter.2 fun _ => by
        rw [hT']
        change ((x₀ ≫ D.P.A.hom) ≫ eSec D.P.A) y ∈ D.P.L.U _
        have e : (x₀ ≫ D.P.A.hom) ≫ eSec D.P.A = x₀ :=
          (Category.assoc _ _ _).trans ((congrArg _ he').trans (Category.comp_id _))
        rw [e]; exact hU hy) _ (Units.isUnit (D.rig.s _))
    rw [← hT] at this
    exact this
  rwa [norm_mul, h1, h2, _root_.mul_one] at h

theorem sec_unique {X : Scheme.{0}} {L : LB X} (t : H0 L 1) {a b : L.Sec}
    (ha : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (a.f i))
    (hb : ∀ i : L.ι, ∀ h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i, t.f (fun _ => i) = resG _ h (b.f i)) :
    a = b := by
  have key : a.f = b.f := funext fun i => by
    have h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) ≤ L.U i := LB.wchart_le L _ _ 0
    have h' : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := fun y hy => Set.mem_iInter.2 fun _ => hy
    have e := congrArg (resG _ h') ((ha i h).symm.trans (hb i h))
    have r : ∀ z : Γ(X, L.U i), resG _ h' (resG _ h z) = z := fun z => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      exact (congrArg (fun f => (X.presheaf.map f).hom z) (Subsingleton.elim _ (𝟙 _))).trans (by rw [X.presheaf.map_id]; rfl)
    rwa [r, r] at e
  cases a; cases b; cases key; rfl

theorem exists_bKey : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  intro κ hκ V _ _ _ _ D C _ _ _ _ hC N ν hν vB hv
  by_cases hg : D.P.g = 0
  · have h := norm_th_one ν hν hg
    have h0 : N.th 1 ≠ 0 := fun e => by simp [e] at h
    refine ⟨(N.th 1 ^ 8)⁻¹, ⟨fun _ => mul_inv_cancel₀ (pow_ne_zero _ h0), fun hg' => by omega⟩, by
      rw [norm_inv, norm_pow, h, one_pow, inv_one]⟩
  by_cases hex : ∃ th : D.P.L.Sec, (∀ s : Sp V, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧
      ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i,
        ν.th.f (fun _ => i) = resG _ h (th.f i)
  · obtain ⟨th, hth, hf⟩ := hex
    obtain ⟨u, hu⟩ := hκ.2.2.2 V ⟨D.P, Nat.one_le_iff_ne_zero.2 hg, D.rig, D.rig_gen, th, hth, vB, hv⟩
    refine ⟨toF V C u, ⟨fun e => (hg e).elim, fun _ _ th' _ _ x hf' hx => ?_⟩, ?_⟩
    · obtain rfl := sec_unique ν.th hf hf'
      exact hu C _ x hx
    · have h1 : ‖toF V C u‖ ≤ 1 := hC.1 _
      have h2 : ‖toF V C ↑u⁻¹‖ ≤ 1 := hC.1 _
      have h3 : ‖toF V C u‖ * ‖toF V C ↑u⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
      nlinarith [norm_nonneg (toF V C u), norm_nonneg (toF V C ↑u⁻¹)]
  · exact ⟨1, ⟨fun e => (hg e).elim, fun _ _ th hth _ _ hf _ => (hex ⟨th, hth, hf⟩).elim⟩, norm_one⟩

end GlobalTheory.MBLow.AbKey

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAt
section
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharIndepAt

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

def liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    X.presheaf.stalk x →+* X.presheaf.stalk x where
  toFun s := (h _ ⟨s, rfl⟩).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_one, map_one])
  map_mul' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_mul, map_mul, map_mul, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_zero, map_zero])
  map_add' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_add (f := _), map_add (f := _), map_add (f := _), (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])

theorem algebraMap_liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f))
    (s : X.presheaf.stalk x) :
    algebraMap _ X.functionField (liftStalk σ h s) = σ (algebraMap _ X.functionField s) :=
  (h _ ⟨s, rfl⟩).choose_spec

theorem residue_liftStalk_eq_iff (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp (liftStalk σ h) = IsLocalRing.residue (X.presheaf.stalk x) ↔
      ∀ f, RegAt x f → ZeroAt x (σ f - f) := by
  constructor
  · rintro e f ⟨s, rfl⟩
    refine ⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact RingHom.congr_fun e s
  · intro H
    ext s
    obtain ⟨m, hm, e⟩ := H _ ⟨s, rfl⟩
    have : m = liftStalk σ h s - s := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
      rw [e, map_sub, algebraMap_liftStalk])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    exact hm

end GlobalTheory.CharIndepAt


open GlobalTheory.CharIndepAt in
theorem GlobalTheory.CharIndepAt.main : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by

  intro X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6
  classical
  let R := X.presheaf.stalk x
  let res := IsLocalRing.residue R
  let g : Γ(X, U) →+* R := (X.presheaf.germ U x hx).hom
  let ψ : ι → (R →+* IsLocalRing.ResidueField R) := fun i => res.comp (liftStalk (σ i) (h1 i))
  let χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R) := fun i => ((ψ i).comp g : Γ(X, U) →+* _)
  let χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R := (res.comp g : Γ(X, U) →+* _)
  letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hext : ∀ i, χ i = χ₀ → ψ i = res := by
    intro i e
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_
    ext a
    exact DFunLike.congr_fun e a
  choose t ht using h3
  have hone : ∀ j, χ j = χ₀ → res (t j) = 1 := by
    intro j e
    obtain ⟨m, hm, em⟩ := h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))
    have : m = t j - 1 := IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  obtain ⟨i₀, hi₀⟩ := h6
  have h0 : χ i₀ = χ₀ := by
    have := (residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀
    ext a
    exact RingHom.congr_fun this (g a)
  by_contra hne
  push_neg at hne
  have hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0 := by
    intro a
    by_contra hz
    refine hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
      intro h
      apply hz
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_comm]
      rfl
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_liftStalk, ht]
      congr 2
      exact algebraMap_germ hx a
  have hli := linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)
  rw [linearIndependent_iff'] at hli
  let c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R :=
    fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)
  have hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0 := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hc := hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))
  have hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R) := by
    change ∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _
    rw [Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]
  have hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'
  obtain ⟨s, hs, es⟩ := h5 _ hn
  have : s = ((Finset.univ.filter fun i => χ i = χ₀).card : R) :=
    IsFractionRing.injective R X.functionField (by rw [es, map_natCast])
  subst this
  have := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs
  rw [map_natCast, ← hc'] at this
  exact this hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRigidifiedSectionOfScalarMultipl
section
noncomputable section

namespace GlobalTheory.KeySwapSec

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open ReciprocityTheory.ChartRestriction.G.H1

theorem exists_isFibreOf_of_isMul (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR R ⟶ G))
    (x : KeyIn R') (hL : L.IsLB) (hx : IsFibreOf x G L rig θ w f) (θ₀ : L.Sec) (b : R) (hb : IsMul (X := G) θ b θ₀) :
    ∃ (th₀ : x.P.L.Sec) (hth₀ : ∀ s : Sp R', ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th₀),
      (∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i) ∧
      IsFibreOf ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, x.v, x.basis⟩ G L rig θ₀ w f := by
  obtain ⟨φ, he, e, hg, F, hp, hgen, hr, hs, hF, hFe, hv⟩ := hx
  obtain ⟨th₀, h₀⟩ := sec_pull_down ((isGen_iff e).1 hgen) hL x.P.isLB θ₀
  have h₁ := (KeyCancel.appLE_eq_iff_stalk e θ x.th).1 hs
  have hm : ∀ i, LB.Sec.f x.th i = constFn x.P.A.hom _ (f b) * LB.Sec.f th₀ i := by
    refine (sec_eq_iff _ _ _ _).2 fun k y hk => ?_
    obtain ⟨j, hj⟩ := exists_chart hL (φ y)
    have e₁ := h₁ _ (𝟙 _) y j k hj hk
    have e₀ := h₀ _ (𝟙 _) y j k hj hk
    rw [hb j, gs_mul (𝟙 _ ≫ φ) y _ hj, gs_constFn _ _ (𝟙 _ ≫ φ) y hj, e₀, Category.id_comp, hp.1.w, cst_comp,
      mul_left_comm] at e₁
    exact ((Units.mul_right_inj _).1 e₁).symm
  refine ⟨th₀, fun s => ?_, hm, φ, he, e, hg, F, hp, hgen, hr, (KeyCancel.appLE_eq_iff_stalk e θ₀ th₀).2 h₀, hF, hFe, hv⟩
  obtain ⟨z, hz, hne⟩ := x.th_ne s
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hne
  refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩⟩
  rw [hm k, Scheme.basicOpen_mul] at hk
  exact hk.2

end GlobalTheory.KeySwapSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
section
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.Modif

theorem exists_bijective_stalkMap_of_dvr : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    (U : Y.Opens) (d : ℕ) (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y,
      IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  intro F _ Y _ p U d M hp hU y hR
  have hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s := by
    intro Z s hs
    obtain ⟨N, c, hc, rfl⟩ := hs
    have := isProper_str F N
    infer_instance
  haveI : IsProper p := hprop hp
  haveI : IsProper (M.σ ≫ p) := hprop M.proj
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI : Nonempty M.X := by
    haveI := M.iso
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, -⟩ := (M.σ ∣_ U).surjective ⟨u, hu⟩
    exact ⟨z.1⟩
  haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M
  let R := Y.presheaf.stalk y
  haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  haveI : IsDiscreteValuationRing R := hR
  let η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let i₂ : Spec R ⟶ Y := Y.fromSpecStalk y

  have hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η := by
    intro w hw
    have hq : η ∈ Set.range i₂ := by
      rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Y).specializes (Set.mem_univ y)
    obtain ⟨q, hq⟩ := hq
    have h1 : i₂ w ⤳ η := hq ▸ (hw q).map i₂.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  let K := FractionRing R
  let j : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u := by
    intro s u
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal
    haveI : s.asIdeal.IsPrime := s.isPrime
    rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U := fun s _ => by
    show i₂ (j s) ∈ U
    rw [hgen (j s) (hj s)]
    exact hηU
  obtain ⟨i₁, hi₁, -⟩ := M.existsUnique_lift (j ≫ i₂) hKU
  have hE : ValuativeCriterion.Existence M.σ := by
    have h : UniversallyClosed M.σ := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨L⟩⟩ := hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance
    inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)
  let c := IsLocalRing.closedPoint R
  have hfr : L.l ≫ M.σ = i₂ := L.fac_right
  refine ⟨L.l c, ?_, ?_⟩
  · show (L.l ≫ M.σ) c = y
    rw [hfr]
    exact Scheme.fromSpecStalk_closedPoint

  have key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom := by
    rintro _ rfl
    have e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk y
    haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance
    haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom
    exact ConcreteCategory.bijective_of_isIso _
  have hb := key _ hfr
  have e₀ := Scheme.Hom.stalkMap_comp L.l M.σ c
  have hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom := by rw [← e₀]; exact hb
  replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2

  let t := genericPoint (Spec R)
  have ht : ∀ u : Spec R, t ⤳ u := fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)
  have hσt : M.σ (L.l t) = η := by
    show (L.l ≫ M.σ) t = η
    rw [hfr]; exact hgen t ht
  have hσg : M.σ (genericPoint M.X) = η := by
    have h1 : M.σ (genericPoint M.X) ⤳ η :=
      hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hlt : L.l t = genericPoint M.X := by
    haveI := M.iso
    have m1 : L.l t ∈ M.opn := show M.σ (L.l t) ∈ U from hσt ▸ hηU
    have m2 : genericPoint M.X ∈ M.opn := show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU
    have e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩ :=
      Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans
        ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))
    exact congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)

  have hBinj : Function.Injective (L.l.stalkMap c).hom := by
    have hsp : t ⤳ c := ht c
    have nat := Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp
    have hf : IsField (M.X.presheaf.stalk (L.l t)) := by
      rw [hlt]; exact Field.toIsField M.X.functionField
    have i1 : Function.Injective (L.l.stalkMap t).hom := by
      letI := hf.toField
      exact RingHom.injective _
    have i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom := by
      refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨V, hV, f, rfl⟩ := M.X.presheaf.germ_exist a
      have e := congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      rw [e] at ha
      rw [germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]
    have i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom) := by
      have h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom :=
        i1.comp i2
      rw [nat] at h4
      exact h4
    exact i3.of_comp
  refine ⟨hb.1.of_comp, fun a => ?_⟩
  obtain ⟨b, hb'⟩ := hb.2 ((L.l.stalkMap c).hom a)
  exact ⟨b, hBinj hb'⟩

end GlobalTheory.CompHS.Modif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalThetaNormalFormKeyDatum
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.MBLow.Cl

namespace GlobalTheory.MBLow.Cl

theorem exists_NF : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g), ∃ u τ a b c W, NF x hg u τ a b c W := by
  intro g x hg
  subst hg
  obtain ⟨⟨τ, M, a, b, c, hab, hc, -, u, h₁, h₂, h₃, h₄, h₅, h₆⟩, -⟩ :=
    GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x
  exact ⟨u, τ, a, b, c, fun i => (2 * Real.pi * Complex.I : ℂ)⁻¹ • M i, h₁, h₂, hab.1, hab.2, hc, h₃, h₄, h₅, h₆⟩

end GlobalTheory.MBLow.Cl
end

