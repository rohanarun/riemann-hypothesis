module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
section
open IsLocalRing GlobalTheory.FormalOrigin

noncomputable section
namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_succ {A : Type} {n : ℕ} (ds : Fin (n+1) → A → A) (α : Fin (n+1) →₀ ℕ) (f : A) :
    iterOp ds α f = (ds 0)^[α 0] (iterOp (fun i => ds i.succ) α.tail f) := by
  unfold iterOp
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  congr 1

def iterHom {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) : A →+ A where
  toFun := (⇑D)^[k]
  map_zero' := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_zero]
  map_add' x y := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_add (f := _), Function.iterate_succ_apply',
        Function.iterate_succ_apply']

theorem iterHom_apply {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) (x : A) :
    iterHom D k x = (⇑D)^[k] x := rfl

theorem exists_iterOpHom {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    ∃ F : A →+ A, ∀ x, F x = iterOp (fun i => ⇑(ds i)) α x := by
  intro n
  induction n with
  | zero =>
      intro ds α
      refine ⟨AddMonoidHom.id A, fun x => ?_⟩
      have : α = 0 := Subsingleton.elim _ _
      subst this; rw [iterOp_zero]; rfl
  | succ n ih =>
      intro ds α
      obtain ⟨F, hF⟩ := ih (fun i => ds i.succ) α.tail
      exact ⟨(iterHom (ds 0) (α 0)).comp F, fun x => by
        rw [iterOp_succ, AddMonoidHom.comp_apply, iterHom_apply, hF]⟩

theorem sum_antidiagonal_succ {M : Type} [AddCommMonoid M] {n : ℕ} (α : Fin (n+1) →₀ ℕ)
    (F : (Fin (n+1) →₀ ℕ) → (Fin (n+1) →₀ ℕ) → M) :
    ∑ p ∈ antidiagonal α, F p.1 p.2 =
      ∑ q ∈ antidiagonal (α 0), ∑ r ∈ antidiagonal α.tail,
        F (Finsupp.cons q.1 r.1) (Finsupp.cons q.2 r.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => ((p.1 0, p.2 0), (p.1.tail, p.2.tail)))
    (fun x => (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨p1, p2⟩ h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal]
    subst h
    refine ⟨by simp, ?_⟩
    ext i; simp [Finsupp.tail_apply]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ h
    simp only [mem_coe, mem_product, HasAntidiagonal.mem_antidiagonal] at h
    simp only [mem_coe, HasAntidiagonal.mem_antidiagonal]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h.1]
    · have := DFunLike.congr_fun h.2 i
      simpa [Finsupp.tail_apply] using this
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]
  · rintro ⟨⟨j, k⟩, ⟨r1, r2⟩⟩ _
    simp [Finsupp.tail_cons]
  · rintro ⟨p1, p2⟩ _
    simp [Finsupp.cons_tail]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterOp_mul {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A),
    iterOp (fun i => ⇑(ds i)) α (f * g) = ∑ p ∈ antidiagonal α,
      (∏ i, (α i).choose (p.1 i)) • (iterOp (fun i => ⇑(ds i)) p.1 f * iterOp (fun i => ⇑(ds i)) p.2 g)
  | 0, ds, α, f, g => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α, f, g => by
      have ih := iterOp_mul (fun i => ds i.succ) α.tail f g
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, ih, ← iterHom_apply, map_sum, sum_antidiagonal_succ α (fun a b => (∏ i, (α i).choose (a i)) •
        (iterOp (fun i => ⇑(ds i)) a f * iterOp (fun i => ⇑(ds i)) b g))]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_nsmul, iterHom_apply, GlobalTheory.derivation_iterate_leibniz, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hs, hs, Fin.prod_univ_succ]
      simp only [Finsupp.cons_zero, Finsupp.tail_cons, Finsupp.cons_succ, Finsupp.tail_apply]
      rw [← nsmul_eq_mul, smul_smul, mul_comm]

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin.TaylorRingHom
open Finset

theorem iterate_one {A : Type} [CommRing A] (D : Derivation ℤ A A) (k : ℕ) :
    (⇑D)^[k] 1 = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Function.iterate_succ_apply, D.map_one_eq_zero, ← iterHom_apply, map_zero]
    simp

theorem eq_zero_iff_succ {n : ℕ} (α : Fin (n+1) →₀ ℕ) : α = 0 ↔ α 0 = 0 ∧ α.tail = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, by ext i; simp [Finsupp.tail_apply]⟩
  · rintro ⟨h0, ht⟩
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using h0
    · have := DFunLike.congr_fun ht i
      simpa [Finsupp.tail_apply] using this

theorem iterOp_one {A : Type} [CommRing A] : ∀ {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ),
    iterOp (fun i => ⇑(ds i)) α 1 = if α = 0 then 1 else 0
  | 0, ds, α => by
      have : α = 0 := Subsingleton.elim _ _
      subst this
      simp [iterOp_zero]
  | n+1, ds, α => by
      have ih := iterOp_one (fun i => ds i.succ) α.tail
      have hs : ∀ (β : Fin (n+1) →₀ ℕ) x, iterOp (fun i => ⇑(ds i)) β x =
          (⇑(ds 0))^[β 0] (iterOp (fun i => ⇑(ds i.succ)) β.tail x) := fun β x => iterOp_succ _ β x
      rw [hs, ih]
      by_cases ht : α.tail = 0
      · rw [if_pos ht, iterate_one]
        simp [eq_zero_iff_succ α, ht]
      · rw [if_neg ht, ← iterHom_apply, map_zero]
        simp [eq_zero_iff_succ α, ht]

theorem iterOp_add {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) (f g : A) :
    iterOp (fun i => ⇑(ds i)) α (f + g) = iterOp (fun i => ⇑(ds i)) α f + iterOp (fun i => ⇑(ds i)) α g := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, ← hF, ← hF, map_add (f := _)]

theorem iterOp_zero' {A : Type} [CommRing A] {n : ℕ} (ds : Fin n → Derivation ℤ A A) (α : Fin n →₀ ℕ) :
    iterOp (fun i => ⇑(ds i)) α 0 = 0 := by
  obtain ⟨F, hF⟩ := exists_iterOpHom ds α
  rw [← hF, map_zero]

theorem factor_identity {n : ℕ} (α : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ)) (hp : p.1 + p.2 = α) :
    (∏ i, ((α i).factorial : ℚ))⁻¹ * ((∏ i, (α i).choose (p.1 i) : ℕ) : ℚ) =
      (∏ i, ((p.1 i).factorial : ℚ))⁻¹ * (∏ i, ((p.2 i).factorial : ℚ))⁻¹ := by
  have hfac : ∀ i, ((α i).choose (p.1 i) : ℚ) * (((p.1 i).factorial : ℚ) * ((p.2 i).factorial : ℚ)) =
      ((α i).factorial : ℚ) := by
    intro i
    have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
    have h2 : p.2 i = α i - p.1 i := by omega
    have := Nat.choose_mul_factorial_mul_factorial (n := α i) (k := p.1 i) (by omega)
    rw [← h2] at this
    rw [← mul_assoc]
    exact_mod_cast this
  have hprod : (∏ i, ((α i).choose (p.1 i) : ℚ)) *
      ((∏ i, ((p.1 i).factorial : ℚ)) * ∏ i, ((p.2 i).factorial : ℚ)) = ∏ i, ((α i).factorial : ℚ) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hfac i
  have h1 : (∏ i, ((p.1 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (∏ i, ((p.2 i).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (∏ i, ((α i).choose (p.1 i) : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.choose_pos (by
      have e : α i = p.1 i + p.2 i := by rw [← hp]; rfl
      omega)).ne'
  push_cast
  rw [← hprod]
  field_simp

end GlobalTheory.FormalOrigin.TaylorRingHom

namespace GlobalTheory.FormalOrigin
open Finset TaylorRingHom

theorem taylor_isRingHom : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B)
    (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  intro A B _ _ _ n ev ds
  refine ⟨{ toFun := taylor ev (fun i => ⇑(ds i))
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun f => rfl⟩
  · ext α
    rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_one]
    unfold taylor
    rw [iterOp_one]
    split_ifs with h
    · subst h; simp
    · simp
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_mul]
    simp only [MvPowerSeries.coeff_apply]
    unfold taylor
    set_option synthInstance.maxHeartbeats 100000 in
      rw [iterOp_mul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_nsmul, map_mul, nsmul_eq_mul, Algebra.smul_def,
      Algebra.smul_def, Algebra.smul_def, ← map_natCast (algebraMap ℚ B), ← mul_assoc,
      ← map_mul, factor_identity α p hp, map_mul]
    ring
  · ext α
    rw [MvPowerSeries.coeff_apply, map_zero]
    unfold taylor
    rw [iterOp_zero', map_zero, smul_zero]
  · intro f g
    ext α
    rw [MvPowerSeries.coeff_apply, map_add (f := _), MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
    unfold taylor
    rw [iterOp_add, map_add (f := _), smul_add]

end GlobalTheory.FormalOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftsOfRationalFormsRationalOfClauses
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField


set_option maxHeartbeats 2000000 in
theorem ratG_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → (∀ i, OMPins T R κ v₀ O i) → (∀ i, PhaseTie T R κ v₀ O ph i) → IoExt R → (∀ i, OneMapRow0 T R κ v₀ O i) → QGuard R → R.LUnif → EvInj T R v₀ → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.RatG R ph := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hC hoff hused hW hO hph hio h0 hQ hU hinj hcov i t x
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hC.lev fw.laws hO
  have hex : PinsOverL T R κ v₀ i := GlobalTheory.T.exists_normalisedTupleData_over_rowField_conditions D G Pl0 T0 A T R F κ v₀ O i hC hoff hused hW (hO i) hQ hcov
  have hsp : GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) :=
    _root_.GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses D G Pl0 T0 A T R F κ v₀ O i hnV hC hoff hused hW hio (hO i) (h0 i) hQ
  have hone : OneMapOverL T R κ v₀ (ph i) i :=
    GlobalTheory.T.oneFormMap_allTuples_coeffField_of_clauses D G Pl0 T0 A T R F κ v₀ O ph i hC hoff hused hW hpb (hO i) (hph i) hio (h0 i) hex hsp
  have hev : fw.Evaluates := GlobalTheory.evaluates_of_unif D G Pl0 T0 A T R F κ v₀ fw hU
  have hrat := GlobalTheory.TwistField.Read.rat_of_oneMapOverL D G Pl0 T0 A T R F κ v₀ fw (ph i) i hC.lev hC.grp hC.models hC.thP hU
    hev hinj hone t x
  obtain ⟨y, -, hy⟩ := hrat
  exact ⟨_, hy.symm⟩

end GlobalTheory.TwistField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg.LevSurj

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : R) :
    (g.appLE U V h).hom (AbLaw.cst f U a) = AbLaw.cst (g ≫ f) V a := by
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  change ((X.presheaf.map (homOfLE le_top).op ≫ g.appLE U V h).hom) _ =
    ((g.appTop ≫ X'.presheaf.map (homOfLE le_top).op).hom) _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem appLE_of_eq {X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens) (V : X'.Opens) (hV : g ⁻¹ᵁ U = V)
    (h : V ≤ g ⁻¹ᵁ U) (hs : Function.Surjective (g.app U).hom) :
    Function.Surjective (g.appLE U V h).hom ∧ RingHom.ker (g.appLE U V h).hom = RingHom.ker (g.app U).hom := by
  subst hV
  have : g.appLE U (g ⁻¹ᵁ U) h = g.app U := by simp [Scheme.Hom.appLE]
  rw [this]
  exact ⟨hs, rfl⟩

end GlobalTheory.FormalAlg.LevSurj

namespace GlobalTheory.FormalAlg.LevSurj

theorem ev_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  intro R _ I Y β hβ n C
  have h1 : ∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    intro e V
    rw [towerIdeal, show thick R I e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) from rfl,
      cst_comp_spec, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  refine ⟨h1, fun e i => ?_⟩
  induction e with
  | zero =>
    have hc : AbLaw.cst ((Y 0).hom ≫ thick R I 0) (C.D 0 i) =
        (AbLaw.cst (Y 0).hom (C.D 0 i)).comp (Ideal.Quotient.mk _) := cst_comp_spec _ _ _
    have : C.ev 0 i = (MvPolynomial.eval₂Hom (AbLaw.cst (Y 0).hom (C.D 0 i)) (C.ρ 0 i)).comp
        (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      ext <;> simp [Charts.ev, hc]
    rw [this]
    exact (C.surj i).comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  | succ e ih =>
    have hp : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
      rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
    have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      rw [Charts.ev, MvPolynomial.comp_eval₂Hom, Charts.ev]
      congr 1
      · ext a
        simp only [RingHom.comp_apply]
        rw [appLE_cst]
        exact congrArg (fun q => AbLaw.cst q (C.D e i) a) (by simpa only [Category.assoc] using hp)
      · funext j
        exact C.ρ_pull e i j
    have hk := (_root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
      (β e) (Y e).hom ((_root_.GlobalTheory.FormalAlg.towerSquares R I Y β hβ).1 e)).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
    obtain ⟨hr, hker⟩ := appLE_of_eq (β e) (C.D (e + 1) i) (C.D e i) (C.pre e i) (C.pre e i).ge hk.1
    rw [hk.2] at hker
    set r := ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom with hr_def
    set c := AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) with hc_def
    set S := (C.ev (e + 1) i).range with hS_def
    have hsq : ∀ x y, x ∈ RingHom.ker r → y ∈ RingHom.ker r → x * y = 0 := by
      intro x y hx hy
      rw [hker] at hx hy
      have hxy := Ideal.mul_mem_mul hx hy
      rw [← Ideal.map_mul, ← pow_add] at hxy
      have hle : (I ^ (e + 1 + (e + 1))).map c ≤ (I ^ (e + 1 + 1)).map c :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      have h0 : (I ^ (e + 1 + 1)).map c = ⊥ := h1 (e + 1) (C.D (e + 1) i)
      have := hle hxy
      rw [h0] at this
      exact (Submodule.mem_bot _).1 this
    have hsplit : ∀ b, ∃ s ∈ S, b - s ∈ RingHom.ker r := by
      intro b
      obtain ⟨P, hP⟩ := ih (r b)
      refine ⟨C.ev (e + 1) i P, ⟨P, rfl⟩, ?_⟩
      rw [RingHom.mem_ker, map_sub, ← hP, ← hev, RingHom.comp_apply, sub_self]
    have hKS : ∀ x ∈ RingHom.ker r, x ∈ S := by
      intro x hx
      have hx' := hx
      rw [hker] at hx'
      change x ∈ Submodule.span _ _ at hx'
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, -, rfl⟩ := hy
        exact ⟨MvPolynomial.C a, by simp [Charts.ev, c]⟩
      | zero => exact S.zero_mem
      | add y z hy hz ihy ihz =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        have hz' : z ∈ RingHom.ker r := hker ▸ hz
        exact S.add_mem (ihy hy') (ihz hz')
      | smul a y hy ihy =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        obtain ⟨s, hs, has⟩ := hsplit a
        have : a • y = s * y + (a - s) * y := by rw [smul_eq_mul]; ring
        rw [this, hsq _ _ has hy', add_zero]
        exact S.mul_mem hs (ihy hy')
    intro b
    obtain ⟨s, hs, hbs⟩ := hsplit b
    have : b ∈ S := by
      have := S.add_mem hs (hKS _ hbs)
      rwa [add_sub_cancel] at this
    exact this

end GlobalTheory.FormalAlg.LevSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def Obj.toSieg {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    SiegPre h M ζ t₁ where
  A := o.A
  ab := o.ab
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  lev := lev
  lev_add := hl.1
  lev_tors := hl.2.1
  geom := hl.2.2

theorem Obj.toSieg_ample {b : Base D R} {N : ℕ} {t : S ⟶ Sp R} (o : Obj b N t) {h M : ℕ} {B : Type} [CommRing B]
    {ζ : B} {t₁ : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)} (hl : IsSympLev o.P h M ζ t₁ lev) :
    Out.RelAmple (o.toSieg hl).A (o.toSieg hl).diag := o.ample

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrix
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

namespace GlobalTheory.LogKSDiv

theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
end

