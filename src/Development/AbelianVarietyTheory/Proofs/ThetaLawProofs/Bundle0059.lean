module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow

namespace GlobalTheory.KeyRuleUnique


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
open Cardinal in
theorem _root_.GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex (K : Type) [Field K] [CharZero K]
    [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  let i : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  haveI : CharZero L := (RingHom.charZero_iff i.injective).1 inferInstance
  have hK : #K ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  have hP : #(MvPolynomial ℝ K) = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max_lift]
    simp only [lift_id, mk_real]
    rw [max_eq_right hK, max_eq_left aleph0_le_continuum]
  have hF : #F = 𝔠 := by rw [FractionRing.cardinalMk, hP]
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · calc #L ≤ max #F ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max F L
        _ = 𝔠 := by rw [hF, max_eq_left aleph0_le_continuum]
    · rw [← hF]
      exact mk_le_of_injective (algebraMap F L).injective
  have hlt : ℵ₀ < #L := hL ▸ aleph0_lt_continuum
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_char_eq (K := L) (L := ℂ) 0 hlt
    (Cardinal.eq.1 (hL.trans mk_complex.symm))
  exact ⟨e.toRingHom.comp i⟩

end GlobalTheory.KeyRuleUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RulePow
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem rule_pow : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ThetaOne κ → ∀ (K : Type) [Field K] [CharZero K]
    (x y : KeyIn K) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j := by
  intro κ hH hF hT K _ _ x y j hp
  have hj : 1 ≤ j := by
    obtain ⟨_, hg, -⟩ := hp
    have := y.g_pos
    rcases Nat.eq_zero_or_pos j with rfl | h
    · omega
    · exact h
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (_root_.GlobalTheory.KeyCountableDescent.keyIn_descends_countable GlobalTheory.firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := GlobalTheory.KeyHouse.nonempty_ringHom_complex K₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₀ j hj
  obtain ⟨x₁, hx₁⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x₀ σ
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₁ j hj
  have e₀ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x y j hx₀ hy₀ hp
  have e₁ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x₁ y₁ j hx₁ hy₀ hy₁
  have e := congrArg Units.val (_root_.GlobalTheory.KeyCl.value_pow_complex κ hH hT x₁ y₁ j hy₁)
  rw [Units.val_pow_eq_pow_val, hF _ _ σ y₀ y₁ e₁, hF _ _ σ x₀ x₁ hx₁, ← map_pow] at e
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hF _ _ _ y₀ y e₀, hF _ _ _ x₀ x hx₀, ← map_pow, σ.injective e]

end GlobalTheory.KeyCl
end

