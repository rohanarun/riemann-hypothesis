module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsEtaRuleExistsUniqueMemSec
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValue

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaProductRule_value_eq_productForm_of_testRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod Dw (R ^ 4)) (f : Rul Xo c), IsEtaRule Xo c R cf xs f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → EtaValAt Xo c R cf xs y (evR Xo c f y) ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (z : FrPt Xo c S'), FrMap φ y z → EtaValAt Xo c R cf xs z (φ (evR Xo c f y)) := by
  first | exact @GlobalTheory.EtaForm.etaValAt_evR_of_fromTest | exact GlobalTheory.EtaForm.etaValAt_evR_of_fromTest | (intros; apply GlobalTheory.EtaForm.etaValAt_evR_of_fromTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClassesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergLifts_span_latticeClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  first | exact @GlobalTheory.EtaVal.exists_qkPt_span | exact GlobalTheory.EtaVal.exists_qkPt_span | (intros; apply GlobalTheory.EtaVal.exists_qkPt_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsSmallCoeffRuleNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaAn

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem nonzeroRule_dom_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP hg using X.signature
  have hs : ∀ a : ℕ, sgn X.p0 a ≠ 0 := fun a => by unfold sgn; split_ifs <;> norm_num
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have e : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [show gram τ.1 X.Gm (mat (fun τ => P τ) τ) = gram τ.1 X.Gm (P τ) from rfl, hg τ,
      Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  rw [e, Complex.ofReal_re]
  have h0 : psgn X.p0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hs a
  exact mul_self_pos.2 h0

theorem exists_small_coeff_rule_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → AllTest Xo c → ∀ (R : ℕ), Odd R → 1 < R → 2 ≤ r → ∃ (i : ℕ) (_ : Fintype (LatMod Dw R)) (x₀ : Fin r → Dw.La) (cf : (Fin r → LatMod Dw R) → ℤ) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Fintype.card (Fin r → LatMod Dw R) ≤ R ^ (2 * I2.PT.f E * r ^ 2) ∧ (∀ j, |cf j| ≤ (max 1 (Fintype.card U.Comp) * R ^ (8 * I2.PT.f E * r ^ 2) : ℕ)) ∧ Spans (shiftFam R x₀ : (Fin r → LatMod Dw R) → Fin r → LatMod Dw (R ^ 4)) ∧ IsEtaRule Xo c R cf (shiftFam R x₀) f ∧ ∀ k, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU hT R hR h1 h2
  have hr : r = Dw.p + Dw.q := hU.1
  subst hr
  obtain ⟨hfG, hfL, hcL, hcG, hdiv, ⟨x₀, hx₀⟩, hspan⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw R h1
  obtain ⟨i, hi⟩ := hdiv hR h2
  letI hFin : Fintype (LatMod Dw R) := Fintype.ofFinite _
  have hf : FD.fdeg E = I2.PT.f E := rfl
  rw [hf] at hcL hcG
  choose xk hxk using fun k => nonzeroRule_dom_nonempty (U.X k)
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  let e := Fintype.equivFin U.Comp
  obtain ⟨cf, hcf, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR h1
    (Dw.p + Dw.q) x₀ (CAt σ) (Fintype.card U.Comp) (fun a => U.un (e.symm a) ⟨xk _, hxk _⟩)
  obtain ⟨f, hrule, -⟩ := (GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c R hR
    (Fin (Dw.p + Dw.q) → LatMod Dw R) (Dw.p + Dw.q) (fun j => (cf j : ℤ)) (shiftFam R x₀)).1
  refine ⟨i, hFin, x₀, fun j => (cf j : ℤ), f, ?_, hi, ?_, ?_, ?_, hrule, ?_⟩
  · have hpos : 0 < Nat.card (LevGrp Dw (R ^ 4)) := Nat.card_pos
    rw [hi] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  · rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcL, ← pow_mul]
    exact le_of_eq (by congr 1; ring)
  · intro j
    rw [Nat.abs_cast]
    exact_mod_cast (hcf j).trans (Nat.mul_le_mul (le_max_right _ _) hcG)
  · intro j
    exact hspan _ x₀ hx₀ j (LinearEquiv.refl _ _)
  · intro k
    obtain ⟨a, rfl⟩ := e.symm.surjective k
    refine ⟨xk _, hxk _, ?_⟩
    have hv := (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c R hR _ _ _ _ f hrule (CAt σ) (U.un (e.symm a) ⟨xk _, hxk _⟩)
      (hT _ _)).1
    have h0 := hne a _ hv
    have e1 : rdU U f (e.symm a) (xk _) = toC (evR Xo c f (U.un (e.symm a) ⟨xk _, hxk _⟩)) := dif_pos (hxk _)
    rw [e1]
    exact h0

end GlobalTheory.EtaAn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralThetaSection_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  first | exact @GlobalTheory.EtaVal.intSec_exists_and_baseChange | exact GlobalTheory.EtaVal.intSec_exists_and_baseChange | (intros; apply GlobalTheory.EtaVal.intSec_exists_and_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormalisedThetaConstantOfUniversalOriginValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedThetaConstant_of_universal_origin_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (x : Sp (FractionRing R) ⟶ Xo.X) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (Φ : Fib Xo x A) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra c.F F] (z : FrPt Xo c F), z.x = spMap (algebraMap (FractionRing R) F) ≫ x → ∀ th : GlobalTheory.UT.SecA A F 1, Φ.SecTie z.x z.s th → ∀ (m : ℕ), Odd m → ∀ (p : ptO Xo z.x ⟶ Xo.univ.t.G) (p' : TFK (R := R) F ⟶ A.A) (w : F), p ^ (m ^ 2) = 1 → p'.left ≫ Φ.φ = p.left → IsNullVal Xo c m z p w → ∃ t, GlobalTheory.UT.ThC A Φ.ρ m th p' t w := by
  first | exact @GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | exact GlobalTheory.EtaVal.NullMove.thC_of_isNullVal | (intros; apply GlobalTheory.EtaVal.NullMove.thC_of_isNullVal <;> assumption)
end

