module

public import Mathlib
public import GroundTheory.Brauer.SkolemNoether
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0848
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
section
attribute [-instance] GlobalTheory.AdmLoc.modTens GlobalTheory.AdmLoc.modFun GlobalTheory.AdmLoc.modProd GlobalTheory.AdmLoc.modQuot
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

section Generic2

variable {S : Type*} [Ring S]

theorem triv_change (σ : S →+* Sᵐᵒᵖ) (x u : Sˣ) (b : S) :
    ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop =
      x * b * (σ x).unop := by
  have h1 : (σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop
      = x * ((((u⁻¹ : Sˣ) : S) * u) * b * ((σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop)) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Generic2

namespace Pair

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

end Pair

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRoots
section
open IsLocalRing Polynomial

namespace GlobalTheory.KummerUnram

theorem etale_adjoinRoot_pow_sub {R : Type} [CommRing R] [Nontrivial R] {k : ℕ} (hk : IsUnit (k : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ k - C (u : R))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hk)
  have hm : (X ^ k - C (u : R)).Monic := monic_X_pow_sub_C _ hk0
  have h1 : AdjoinRoot.root (X ^ k - C (u : R)) ^ k = algebraMap R _ (u : R) := by
    have := AdjoinRoot.eval₂_root (X ^ k - C (u : R))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ k - C (u : R))) :=
    (isUnit_pow_iff hk0).1 (h1 ▸ (u.isUnit.map _))
  let P : StandardEtalePair R := ⟨X ^ k - C (u : R), hm, derivative (X ^ k - C (u : R)), 1, 0, 1, by simp⟩
  have h : IsUnit (AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R)))) := by
    have e : AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R))) =
        algebraMap R _ (k : R) * AdjoinRoot.root _ ^ (k - 1) := by
      simp [derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hk.map _).mul (hr.pow _)
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk _ (derivative (X ^ k - C (u : R))))) _
      h).symm.restrictScalars R))

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_root_step {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) (u : Tˣ)
    (ub : AlgebraicClosure (ResidueField T)) (hub : ub ^ k = algebraMap _ _ (residue T u)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∃ y ∈ T', y ^ k = ((u : T) : F) ∧
      ∀ n : ℕ, ub ^ n ≠ 1 → y ^ n ≠ 1 := by
  have := etale_adjoinRoot_pow_sub hk u
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  let ε : AdjoinRoot (X ^ k - C (u : T)) →+* AlgebraicClosure (ResidueField T) :=
    AdjoinRoot.lift ρ ub (by simp [ρ, hub])
  have hερ : ε.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε, AdjoinRoot.algebraMap_eq]
  have hε : IsLocalHom (ε.comp (algebraMap T (AdjoinRoot (X ^ k - C (u : T))))) := by
    rw [hερ]
    haveI : IsLocalHom (algebraMap (ResidueField T) (AlgebraicClosure (ResidueField T))) :=
      ⟨fun x hx => isUnit_iff_ne_zero.mpr fun h => by
        rw [h, map_zero] at hx
        exact (isUnit_iff_ne_zero.mp hx) rfl⟩
    exact RingHom.isLocalHom_comp (algebraMap (ResidueField T) (AlgebraicClosure (ResidueField T))) (residue T)
  obtain ⟨B, _, _, _, ψ, ρ', j', -, h2, h3, h4, h5⟩ :=
    TorsionUnram.exists_local_of_etale ε hε T.subtype Subtype.val_injective
  obtain ⟨hD, f, hf, hirr⟩ := UnramSub.range (i := j') h3
  refine ⟨j'.range, ⟨hD, f.comp (ψ.comp (algebraMap T _)), fun v => ?_,
    fun π hπ => hirr _ (h5 π hπ)⟩, j' (ψ (AdjoinRoot.root _)), ⟨_, rfl⟩, ?_, fun n hn hy => hn ?_⟩
  · rw [RingHom.comp_apply, hf]
    exact congr($h4 v)
  · have h1 : AdjoinRoot.root (X ^ k - C (u : T)) ^ k = algebraMap T _ (u : T) := by
      have := AdjoinRoot.eval₂_root (X ^ k - C (u : T))
      simpa [sub_eq_zero] using this
    rw [← map_pow, ← map_pow, h1]
    exact congr($h4 (u : T))
  · have e1 : ψ (AdjoinRoot.root (X ^ k - C (u : T))) ^ n = 1 :=
      h3 (by rw [map_pow, hy, map_one])
    have e2 : ρ' (ψ (AdjoinRoot.root (X ^ k - C (u : T)))) = ub := by
      rw [← RingHom.comp_apply, h2]
      simp [ε]
    rw [← e2, ← map_pow, e1, map_one]

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_rootsOfUnity {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∀ z : F, z ^ k = 1 → z ∈ T' := by
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  have hkΩ : ((k : ℕ) : AlgebraicClosure (ResidueField T)) ≠ 0 := by
    simpa [ρ] using (hk.map ρ).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkΩ)
  haveI : NeZero ((k : ℕ) : AlgebraicClosure (ResidueField T)) := ⟨hkΩ⟩
  obtain ⟨ub, hub⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ResidueField T)) k
  obtain ⟨T', hT', y, hyT, hy, hyn⟩ := exists_root_step T hk 1 ub (by simp [hub.pow_eq_one])
  have hy1 : y ^ k = 1 := by simpa using hy
  have hprim : IsPrimitiveRoot y k := IsPrimitiveRoot.mk_of_lt y hk0 hy1
    fun l hl hlk => hyn l (hub.pow_ne_one_of_pos_of_lt hl.ne' hlk)
  refine ⟨T', hT', fun z hz => ?_⟩
  haveI : NeZero k := ⟨hk0.ne'⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact pow_mem hyT i

end GlobalTheory.KummerUnram

namespace GlobalTheory


open KummerUnram in
theorem exists_unramSub_of_pow_eq_units : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  intro F _ _ T _ k hk U hU
  obtain ⟨T₁, h₁, hroots⟩ := exists_rootsOfUnity T hk
  suffices key : ∃ T' : Subring F, UnramSub T.subtype T' ∧ T₁ ≤ T' ∧
      ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' by
    obtain ⟨T', h, -, h'⟩ := key
    exact ⟨T', h, h'⟩
  induction U, hU using Set.Finite.induction_on with
  | empty => exact ⟨T₁, h₁, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨T', hT', hle, hmem⟩ := ih
    haveI := hT'.isDVR
    have hTT' : T ≤ T' := fun z hz => hT'.mem ⟨z, hz⟩
    let ι : T →+* T' := Subring.inclusion hTT'
    have hk' : IsUnit (k : T') := by simpa [ι] using hk.map ι
    let a' : T'ˣ := Units.map ι.toMonoidHom a
    have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := T) (by simpa using hk)
    obtain ⟨ub, hub⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (ResidueField T') (AlgebraicClosure (ResidueField T')) (residue T' a'))
      (Nat.pos_of_ne_zero hk0)
    obtain ⟨T'', hT'', y, hyT, hy, -⟩ := exists_root_step T' hk' a' ub hub
    have hy' : y ^ k = ((a : T) : F) := by simpa [a', ι] using hy
    have ha0 : ((a : T) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (by rw [← hy', zero_pow hk0])
    have hle' : T' ≤ T'' := UnramSub.le hT''
    refine ⟨T'', hT'.trans hT'', hle.trans hle', fun x ⟨u, hu, hx⟩ => ?_⟩
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · have hz : (x / y) ^ k = 1 := by rw [div_pow, hx, hy', div_self ha0]
      have : x = (x / y) * y := by field_simp
      rw [this]
      exact mul_mem (hle' (hle (hroots _ hz))) hyT
    · exact hle' (hmem x ⟨u, hu, hx⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationPowPrimePowSubGe
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PowLim

theorem pow_prime_step {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {p : ℕ}
    (hp : p.Prime) (hvp : v (p : C) = 1) {a b : C} (ha : 0 ≤ v a) (hb : 0 ≤ v b) {t ε : ℝ}
    (hεt : ε ≤ t) (hε1 : ε ≤ 1) (ht : (t : WithTop ℝ) ≤ v (a - b)) :
    ((t + ε : ℝ) : WithTop ℝ) ≤ v (a ^ p - b ^ p) := by
  let R : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        have ha' : 0 ≤ v a := ha
        have hb' : 0 ≤ v b := hb
        show 0 ≤ v (a * b)
        rw [v.map_mul]
        exact add_nonneg ha' hb'
      one_mem' := by
        show 0 ≤ v 1
        rw [v.map_one]
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (v.map_add _ _)
      zero_mem' := by
        show 0 ≤ v 0
        rw [v.map_zero]; exact le_top
      neg_mem' := fun {a} ha => by
        show 0 ≤ v (-a)
        rw [v.map_neg]; exact ha }
  have haR : a ∈ R := ha
  have hbR : b ∈ R := hb
  have hdR : a - b ∈ R := R.sub_mem haR hbR
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨a - b, hdR⟩ : R) ⟨b, hbR⟩
  have hr' := congrArg (fun z : R => (z : C)) hr
  simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_natCast,
    sub_add_cancel] at hr'
  obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have e : a ^ p - b ^ p = (a - b) * (a - b) * (a - b) ^ k + (p : C) * (a - b) * (b * r) := by
    rw [hr']
    have : (a - b) ^ p = (a - b) * (a - b) * (a - b) ^ k := by rw [hk]; ring
    rw [this]; ring
  have h1 : (0 : WithTop ℝ) ≤ v ((a - b) ^ k) := R.pow_mem hdR k
  have h2 : (0 : WithTop ℝ) ≤ v (b * (r : C)) := R.mul_mem hbR r.2
  have hε : (ε : WithTop ℝ) ≤ v (a - b) := le_trans (WithTop.coe_le_coe.2 hεt) ht
  have hε1' : (ε : WithTop ℝ) ≤ 1 := by exact_mod_cast hε1
  rw [e]
  refine le_trans (le_min ?_ ?_) (v.map_add _ _)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add]
    exact le_trans (add_le_add ht hε) (le_add_of_nonneg_right h1)
  · rw [v.map_mul, v.map_mul, WithTop.coe_add, hvp, add_comm (t : WithTop ℝ)]
    exact le_trans (add_le_add hε1' ht) (le_add_of_nonneg_right h2)

theorem pow_prime_pow_close : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ x y : C, IsIntV v x → IsIntV v y → 0 < v (x - y) → ∀ r : ℝ, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (r : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
  intro C _ v p hp hvp x y hx hy hxy r
  have hx' : 0 ≤ v x := hx
  have hy' : 0 ≤ v y := hy
  obtain ⟨ε, hε0, hε1, hε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ (ε : WithTop ℝ) ≤ v (x - y) := by
    generalize v (x - y) = w at hxy
    induction w using WithTop.recTopCoe with
    | top => exact ⟨1, one_pos, le_rfl, le_top⟩
    | coe s =>
      have hs : 0 < s := by exact_mod_cast hxy
      exact ⟨min s 1, lt_min hs one_pos, min_le_right _ _, WithTop.coe_le_coe.2 (min_le_left _ _)⟩
  have hpow : ∀ (z : C) (n : ℕ), 0 ≤ v z → 0 ≤ v (z ^ n) := by
    intro z n hz
    rw [v.map_pow]
    exact nsmul_nonneg hz n
  have key : ∀ N : ℕ, ((((N : ℝ) + 1) * ε : ℝ) : WithTop ℝ) ≤ v (x ^ p ^ N - y ^ p ^ N) := by
    intro N
    induction N with
    | zero => simpa using hε
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have := pow_prime_step v hp hvp (hpow x (p ^ N) hx') (hpow y (p ^ N) hy')
        (t := ((N : ℝ) + 1) * ε) (ε := ε) (by nlinarith) hε1 ih
      rw [← pow_mul, ← pow_mul, ← pow_succ] at this
      refine le_trans (WithTop.coe_le_coe.2 (le_of_eq ?_)) this
      push_cast; ring
  obtain ⟨M, hM⟩ := exists_nat_gt (r / ε)
  refine ⟨M, fun N hN => le_trans (WithTop.coe_le_coe.2 ?_) (key N)⟩
  have h1 : (M : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_lt_iff₀ hε0] at hM
  nlinarith

end GlobalTheory.PowLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicIntegersQuotPrimePowOfFiniteDim
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKLoc.IntFin

theorem finite_intK_quot_pow : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] L] (m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p L ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p L) ^ m}) := by
  intro p _ L hL m
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.Euler.card_OK_quot_natCast p L hL (pow_ne_zero m hp)
  have hf : Finite (ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L ⧸ Ideal.span {((p ^ m : ℕ) : ReciprocityTheory.DiscreteGroups.LocalClassField.OK p L)}) :=
    Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  push_cast at hf
  exact hf

end GlobalTheory.LKLoc.IntFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePadicTensorUnramifiedIntegersQuotPrimePow
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TenFin

theorem finite_quot_of_gen {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal R)
    (f : A →+* R) (g : B →+* R) (J₁ : Ideal A) (J₂ : Ideal B) (h₁ : J₁.map f ≤ I) (h₂ : J₂.map g ≤ I)
    [Finite (A ⧸ J₁)] [Finite (B ⧸ J₂)] (hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hI : (n : R) ∈ I) : Finite (R ⧸ I) := by
  let π := Ideal.Quotient.mk I
  let fa : A ⧸ J₁ →+* R ⧸ I := Ideal.Quotient.lift J₁ (π.comp f) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₁ (Ideal.mem_map_of_mem f ha)))
  let gb : B ⧸ J₂ →+* R ⧸ I := Ideal.Quotient.lift J₂ (π.comp g) (fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (h₂ (Ideal.mem_map_of_mem g ha)))
  have hfa : ∀ a, π (f a) = fa (Ideal.Quotient.mk J₁ a) := fun a => rfl
  have hgb : ∀ b, π (g b) = gb (Ideal.Quotient.mk J₂ b) := fun b => rfl
  let S : Set (R ⧸ I) := Set.image2 (· * ·) (Set.range fa) (Set.range gb)
  have hS : S.Finite := (Set.finite_range fa).image2 _ (Set.finite_range gb)
  let M : Submonoid (R ⧸ I) :=
    { carrier := S
      one_mem' := ⟨1, ⟨1, map_one _⟩, 1, ⟨1, map_one _⟩, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ ⟨_, ⟨a', rfl⟩, _, ⟨b', rfl⟩, rfl⟩
        refine ⟨fa (a * a'), ⟨_, rfl⟩, gb (b * b'), ⟨_, rfl⟩, ?_⟩
        simp only [map_mul]; ring }
  have hsub : π '' (Set.range f ∪ Set.range g) ⊆ (M : Set (R ⧸ I)) := by
    rintro _ ⟨_, ⟨a, rfl⟩ | ⟨b, rfl⟩, rfl⟩
    · exact ⟨fa (Ideal.Quotient.mk J₁ a), ⟨_, rfl⟩, 1, ⟨1, map_one _⟩, (mul_one _).trans (hfa a).symm⟩
    · exact ⟨1, ⟨1, map_one _⟩, gb (Ideal.Quotient.mk J₂ b), ⟨_, rfl⟩, (one_mul _).trans (hgb b).symm⟩
  have htop : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subring.closure (π '' (Set.range f ∪ Set.range g)) := by
      rw [← RingHom.map_closure, hgen, ← RingHom.range_eq_map]
      exact Ideal.Quotient.mk_surjective x
    rw [Subring.mem_closure_iff] at hx
    refine AddSubgroup.closure_mono ?_ hx
    exact Submonoid.closure_le.2 hsub
  haveI : AddGroup.FG (R ⧸ I) := AddGroup.fg_iff.mpr ⟨S, htop, hS⟩
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  rw [nsmul_eq_mul]
  have : (n : R ⧸ I) = 0 := by
    rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hI
  rw [this, zero_mul]

theorem finite_intKQ_quot : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r m : ℕ),
    Finite (GlobalTheory.LKLoc.intK p K ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m}) →
    Finite (GlobalTheory.LKLoc.intK p (Qr p r) ⧸ Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) →
    Finite (intKQ p K r ⧸ Ideal.span {(p : intKQ p K r) ^ m}) := by
  intro p _ K r m hA hB
  let f : GlobalTheory.LKLoc.intK p K →+* intKQ p K r :=
    ((inclK p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p K).subtype).codRestrict (intKQ p K r)
      (fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩))
  let g : GlobalTheory.LKLoc.intK p (Qr p r) →+* intKQ p K r :=
    ((inclQ p K r).toRingHom.comp (GlobalTheory.LKLoc.intK p (Qr p r)).subtype).codRestrict (intKQ p K r)
      (fun b => Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩))
  have hgen : Subring.closure (Set.range f ∪ Set.range g) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · exact Subring.subset_closure (Or.inr ⟨⟨b.1, b.2⟩, rfl⟩)
    | zero => exact zero_mem _
    | one => exact one_mem _
    | add y z _ _ h1 h2 => exact add_mem h1 h2
    | neg y _ h => exact neg_mem h
    | mul y z _ _ h1 h2 => exact mul_mem h1 h2
  refine finite_quot_of_gen (J₁ := Ideal.span {(p : GlobalTheory.LKLoc.intK p K) ^ m})
    (J₂ := Ideal.span {(p : GlobalTheory.LKLoc.intK p (Qr p r)) ^ m}) _ f g ?_ ?_ hgen (p ^ m) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) ?_
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  · rw [Nat.cast_pow]; exact Ideal.subset_span rfl

end GlobalTheory.TenFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSignsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i ≠ ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.FockOpp.fockS_of_opposite | exact GlobalTheory.FockOpp.fockS_of_opposite | (intros; apply GlobalTheory.FockOpp.fockS_of_opposite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisThetaLaws

theorem heis_theta_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), (∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f)) ∧ (∀ w w' f, heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f) ∧ ∀ g h x y, symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y :=
  fun D ψ hψ S T =>
    ⟨fun w _ hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w,
      fun w w' f => GlobalTheory.WeilVacMove.heisO_heisO ψ S T w w' f,
      GlobalTheory.SymplOInv.symplO_actO D S T⟩

end GlobalTheory.HeisThetaLaws
end

