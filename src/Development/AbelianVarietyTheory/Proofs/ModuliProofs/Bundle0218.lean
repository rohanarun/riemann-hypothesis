module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem moduli_scheme_exists : N1ab :=
  _root_.GlobalTheory.ZM.moduli_nonempty_all_levels _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1 _root_.GlobalTheory.Moduli.cube_of_isLB _root_.GlobalTheory.thetaUnifAV_closed

end GlobalTheory.Moduli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHeckeQuotientReducedBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem kerSet_of_isPullback {S : Scheme.{0}} {G G' C : Over S} [GrpObj G'] {ψ : G ⟶ G'} {j : C ⟶ G}
    [IsClosedImmersion j.left] (hP : IsPullback j (toUnit C) ψ η[G']) : KerSet ψ (Set.range j.left) := by
  intro k _ _ x z
  constructor
  · intro h
    have hl := hP.lift_fst z (toUnit _) h
    rintro _ ⟨a, rfl⟩
    exact ⟨(hP.lift z (toUnit _) h).left a, by rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hl]⟩
  · intro h
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec _))
    have h4 : j.left.ker ≤ z.left.ker := ker_le_ker_of_range_subset_of_isReduced _ _ h
    have h3 := IsClosedImmersion.lift_fac _ _ h4
    let l : Over.mk x ⟶ C := Over.homMk (IsClosedImmersion.lift _ _ h4) (by
      rw [← Over.w j, ← Category.assoc, h3, Over.w])
    have hl : l ≫ j = z := Over.OverMorphism.ext h3
    rw [← hl, Category.assoc, hP.w, ← Category.assoc, toUnit_unique (l ≫ _) (toUnit _)]
    rfl

theorem existsUnique_heckeQuot :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (C : Over S) (j : C ⟶ o.t.G), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsReduced S → IsFinite C.hom → Etale C.hom → IsClosedImmersion j.left → HeckeSet D o.t 𝔓 p i (Set.range j.left) → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ∧ ∃ (o' : Ob D l s) (_ : ObjMap o' Xo.univ f) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ IsPullback j (toUnit C) ψ η[o'.t.G] := by
  intro E _ _ _ H D l Xo 𝔓 p i S s o C j hD hA hS hf he hj hK
  obtain ⟨Z⟩ := _root_.GlobalTheory.HkFam.corr_nonempty E H D l Xo 𝔓 p i hD hA
  obtain ⟨h, ⟨hs, n, hn⟩, -⟩ := Z.rep S s hS o (Set.range j.left) ⟨C, j, hf, he, hj, rfl⟩ hK
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  obtain ⟨o', ⟨n'⟩⟩ := GlobalTheory.obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ _
    (Z.π₁ ≫ Xo.s) s h rfl rfl (by rw [hid, Category.comp_id, hs]) Z.o₂
  obtain ⟨⟨ψ, hψ, -⟩, hall⟩ := _root_.GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ h Z.o₁ Z.o₂ o o' n n' Z.ψ
  obtain ⟨hi, hk⟩ := hall ψ hψ
  have hi := hi Z.isog
  have hk := hk Z.K Z.isog.1.1 Z.ker
  rw [← hn] at hk
  obtain ⟨m, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z.o₂ o').2 Z.π₂ h Z.m₂).1 n'
  have hfs : (h ≫ Z.π₂) ≫ Xo.s = s := by rw [Category.assoc, Z.base₂, hs]
  have := o'.proper
  refine ⟨h ≫ Z.π₂, ⟨hfs, o', m, ψ, hi, ?_⟩, ?_⟩
  · exact (etSet_of_kerSet S _ _ ψ _ inferInstance hi.1.2.1 hi.1.2.2.1 hk).2 hS C j he hj rfl
  · rintro f ⟨hf₁, o₁, m₁, ψ₁, hi₁, hP⟩
    exact (_root_.GlobalTheory.heckeQuot_unique E H D l Xo 𝔓 p i S s o o₁ o' ψ₁ ψ _ f _ m₁ m hA hK hf₁ hfs hi₁ hi
      (kerSet_of_isPullback hP) hk).1

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeCorrespondenceSecondProjectionFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam.Swap

theorem id_pow_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (𝟙 G' ^ n).left ≫ φ = φ ≫ (𝟙 G ^ n).left := by
  have hw : φ ≫ G.hom = G'.hom ≫ f := h.1.w
  let Φ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ hw
  have key : ∀ m : ℕ, (Φ ^ m).left = (𝟙 G' ^ m).left ≫ φ := by
    intro m
    induction m with
    | zero =>
      let Ψ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ) (by
        rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have hΨ : Ψ * Ψ = Ψ * 1 := by
        rw [_root_.mul_one]
        apply Over.OverMorphism.ext
        have := h.2 G' 1 1 Ψ Ψ rfl rfl
        rw [this, _root_.mul_one]
        rfl
      have h1 : Ψ = 1 := mul_left_cancel hΨ
      simp only [pow_zero]
      rw [← h1]
      rfl
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact h.2 G' (𝟙 G' ^ m) (𝟙 G') (Φ ^ m) Φ ih (by simp [Φ])
  have hc : Φ ≫ 𝟙 G ^ n = Φ ^ n := by rw [MonObj.comp_pow, Category.comp_id]
  calc (𝟙 G' ^ n).left ≫ φ = (Φ ^ n).left := (key n).symm
    _ = (Φ ≫ 𝟙 G ^ n).left := by rw [hc]
    _ = φ ≫ (𝟙 G ^ n).left := by simp [Φ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {P P' : Ideal (𝓞 E)} {p i : ℕ}

theorem isAdmissibleSplitHeckePrime_conj (h : admitted l P p) : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := by
  obtain ⟨hmax, hcop, hp, hpP, hl⟩ := h
  refine ⟨?_, ?_, hp, ?_, hl⟩
  · exact Ideal.map_isMaximal_of_equiv H.bar (p := P)
  · rw [GlobalTheory.HeckeDual.map_bar_map_bar, sup_comm]
    exact hcop
  · have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this

theorem isReduced_Hk (Z : Corr Xo P p i) : IsReduced Z.Hk := by
  have : Etale Z.π₁ := Z.et₁
  have : SmoothOfRelativeDimension D.dim Xo.s := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field (KA l) Z.Hk
    (Z.π₁ ≫ Xo.s) inferInstance).1

theorem isHecke (Z : Corr Xo P p i) : IsHecke Z.o₁ Z.o₂ P p i Z.ψ := ⟨Z.isog, Z.K, Z.ker, Z.hecke⟩

private theorem oAct_act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] (A : OAct (𝓞 E) G) (n : ℕ) :
    A.act (n : 𝓞 E) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h0 := A.5 0 0
    rw [add_zero] at h0
    have h1 : A.act 0 * A.act 0 = A.act 0 * 1 := by rw [_root_.mul_one]; exact h0.symm
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel h1
  | succ n ih => rw [Nat.cast_succ, A.5, ih, A.3, pow_succ]

theorem exists_dual (Z : Corr Xo P p i) (h : admitted l P p) : ∃ χ : Z.o₂.t.G ⟶ Z.o₁.t.G,
    Z.ψ ≫ χ = 𝟙 Z.o₁.t.G ^ p ^ 2 ∧ χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2 ∧
      IsHecke Z.o₂ Z.o₁ (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i χ := by
  have hh := h
  obtain ⟨-, -, hp, -, hl⟩ := hh
  have := isReduced_Hk Z
  have hpb : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := (isAdmissibleSplitHeckePrime_conj h).2.2.2.1
  have hker : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.Hk) (z : Over.mk x ⟶ Z.o₁.t.G),
      z ≫ Z.ψ = 1 → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hK⟩ := Z.hecke k x
    have hzC : z ∈ C := (hC z).2 ((Z.ker k x z).1 hz)
    have hmem : ((p : 𝓞 E) * p) ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hpb
    have h1 : z ≫ Z.o₁.t.act.act ((p : 𝓞 E) * p) = 1 := hK.2.2.1 hzC _ hmem
    rw [← Nat.cast_mul, oAct_act_natCast, MonObj.comp_pow, Category.comp_id, ← sq] at h1
    exact h1
  obtain ⟨χ, h1, h2, h3⟩ :=
    exists_dual_isogeny E H D l p Z.Hk (Z.π₁ ≫ Xo.s) Z.o₁ Z.o₂ Z.ψ hp hl Z.isog hker
  exact ⟨χ, h1, h2, GlobalTheory.isHecke_dual E H D l P p i Z.Hk _ Z.o₁ Z.o₂ Z.ψ χ h (isHecke Z) h3 h1⟩

def Exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (a : Z.Hk ⟶ Z'.Hk) : Prop :=
  a ≫ Z'.π₁ ≫ Xo.s = Z.π₁ ≫ Xo.s ∧ ∃ (n₁ : ObjMap Z.o₂ Z'.o₁ a) (n₂ : ObjMap Z.o₁ Z'.o₂ a),
    χ.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ Z'.ψ.left ∧ Z.ψ.left ≫ n₁.toSABMap.φ = n₂.toSABMap.φ ≫ χ'.left

theorem exists_exch (Z : Corr Xo P p i) (Z' : Corr Xo P' p i) (χ : Z.o₂.t.G ⟶ Z.o₁.t.G) (χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G)
    (h : χ ≫ Z.ψ = 𝟙 Z.o₂.t.G ^ p ^ 2) (h' : Z'.ψ ≫ χ' = 𝟙 Z'.o₁.t.G ^ p ^ 2) (hχ : IsHecke Z.o₂ Z.o₁ P' p i χ) :
    ∃ a, Exch Z Z' χ χ' a := by
  have := isReduced_Hk Z
  obtain ⟨a, ⟨ha1, n₁, n₂, hn⟩, -⟩ := Z'.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂ Z.o₁ χ hχ
  refine ⟨a, ha1, n₁, n₂, hn, ?_⟩
  obtain ⟨⟨⟨-, hfin, het, hsurj, -⟩, -⟩, -⟩ := hχ
  have : Epi χ.left := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi χ.left]
  have hp1 : IsGrpPullback Z.o₂.t.G Z'.o₁.t.G a n₁.toSABMap.φ := n₁.toSABMap.2
  calc χ.left ≫ Z.ψ.left ≫ n₁.toSABMap.φ = (χ ≫ Z.ψ).left ≫ n₁.toSABMap.φ := by simp
    _ = (𝟙 Z.o₂.t.G ^ p ^ 2).left ≫ n₁.toSABMap.φ := by rw [h]
    _ = n₁.toSABMap.φ ≫ (𝟙 Z'.o₁.t.G ^ p ^ 2).left := id_pow_left_comp hp1 (p ^ 2)
    _ = n₁.toSABMap.φ ≫ (Z'.ψ ≫ χ').left := by rw [h']
    _ = χ.left ≫ n₂.toSABMap.φ ≫ χ'.left := by rw [Over.comp_left, ← Category.assoc, ← hn, Category.assoc]

theorem Exch.comp_eq_id {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} {b : Z'.Hk ⟶ Z.Hk} (ha : Exch Z Z' χ χ' a)
    (hb : Exch Z' Z χ' χ b) : a ≫ b = 𝟙 _ := by
  obtain ⟨ha1, n₁, n₂, -, hn2⟩ := ha
  obtain ⟨hb1, m₁, m₂, hm1, -⟩ := hb
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Z.univ Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₁ Z.o₂ Z.ψ (isHecke Z)
  obtain ⟨c₁, hc₁⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z'.o₂ Z.o₁).2
    b a m₁).1 n₂
  obtain ⟨c₂, hc₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z'.o₁ Z.o₂).2
    b a m₂).1 n₁
  obtain ⟨i₁, hi₁⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₁ Z.o₁ Z.o₁).1
  obtain ⟨i₂, hi₂⟩ := (GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z.o₂ Z.o₂ Z.o₂).1
  have e1 := huniq (a ≫ b) ⟨by rw [Category.assoc, hb1, ha1], c₁, c₂, by
    rw [hc₁, hc₂, ← Category.assoc, hn2, Category.assoc, hm1, Category.assoc]⟩
  have e2 := huniq (𝟙 _) ⟨by rw [Category.id_comp], i₁, i₂, by rw [hi₁, hi₂, Category.id_comp, Category.comp_id]⟩
  exact e1.trans e2.symm

theorem Exch.comp_π₁ {Z : Corr Xo P p i} {Z' : Corr Xo P' p i} {χ : Z.o₂.t.G ⟶ Z.o₁.t.G}
    {χ' : Z'.o₂.t.G ⟶ Z'.o₁.t.G} {a : Z.Hk ⟶ Z'.Hk} (ha : Exch Z Z' χ χ' a) : a ≫ Z'.π₁ = Z.π₂ := by
  obtain ⟨ha1, n₁, n₂, -, -⟩ := ha
  have := isReduced_Hk Z
  obtain ⟨_, -, huniq⟩ := Xo.rep Z.Hk (Z.π₁ ≫ Xo.s) inferInstance Z.o₂
  obtain ⟨c, -⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ Z'.o₁ Z.o₂).2
    Z'.π₁ a Z'.m₁).1 n₁
  have e1 := huniq (a ≫ Z'.π₁) ⟨by rw [Category.assoc]; exact ha1, ⟨c⟩⟩
  have e2 := huniq Z.π₂ ⟨Z.base₂, ⟨Z.m₂⟩⟩
  exact e1.trans e2.symm

end GlobalTheory.HkFam.Swap

namespace GlobalTheory.HkFam

open Swap

theorem second_projection_finite_etale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo 𝔓 p i), 1 ≤ D.p + D.q → admitted l 𝔓 p → IsFinite Z.π₂ ∧ Etale Z.π₂ ∧ (i ≤ D.p + D.q → Surjective Z.π₂) := by
  intro E _ _ _ H D l Xo P p i Z hpq h
  have h' : admitted l (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p := isAdmissibleSplitHeckePrime_conj h
  obtain ⟨Z'⟩ := _root_.GlobalTheory.HkFam.corr_nonempty E H D l Xo (P.map (H.bar : 𝓞 E →+* 𝓞 E)) p i hpq h'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := exists_dual Z h
  obtain ⟨χ', hχ'1, hχ'2, hχ'3⟩ := exists_dual Z' h'
  rw [GlobalTheory.HeckeDual.map_bar_map_bar] at hχ'3
  obtain ⟨a, ha⟩ := exists_exch Z Z' χ χ' hχ2 hχ'1 hχ3
  obtain ⟨b, hb⟩ := exists_exch Z' Z χ' χ hχ'2 hχ1 hχ'3
  have : IsIso a := ⟨b, Exch.comp_eq_id ha hb, Exch.comp_eq_id hb ha⟩
  have := Z'.fin₁
  have := Z'.et₁
  rw [← Exch.comp_π₁ ha]
  refine ⟨inferInstance, inferInstance, fun hi => ?_⟩
  have := (_root_.GlobalTheory.kerScheme_points E H D l Xo _ p i Z'.toKerScheme h').2 hi
  infer_instance

end GlobalTheory.HkFam

end
end

