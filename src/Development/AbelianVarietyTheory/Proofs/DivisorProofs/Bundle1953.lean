module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLevelOverIntegers
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem tsum_coeff_C_mul_pow_eq {K : Type} [NormedField K] (a u : K) :
    ∑' n, PowerSeries.coeff n (PowerSeries.C a) * u ^ n = a := by
  rw [tsum_eq_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])]
  simp

theorem summable_coeff_C_mul_pow {K : Type} [NormedField K] (a u : K) :
    Summable fun n => ‖PowerSeries.coeff n (PowerSeries.C a) * u ^ n‖ :=
  (hasSum_single 0 (fun n hn => by simp [PowerSeries.coeff_C, hn])).summable

theorem ring_of_deformation : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  intro C _ _ _ _ e I I' _ _ Φ c π b ε hπ hε hb hsum
  classical

  set o : Subfield C := Subfield.closure (Set.range c) with ho_def
  have hoc : Countable o := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact (Subfield.cardinalMk_closure_le_max _).trans
      (max_le (Cardinal.mk_le_aleph0_iff.2 (Set.finite_range c).countable.to_subtype) le_rfl)

  set G : Set (PowerSeries C) :=
    Set.range (fun x : o => PowerSeries.C (x : C)) ∪ Set.range Φ with hG
  set A : Subring (PowerSeries C) := Subring.closure G with hA
  obtain ⟨B, ev, t, hB, hev, ht, hevt, hfin⟩ := _root_.GlobalTheory.MBLow.BddPS.main C π hπ
  have hAB : A ≤ B := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨a, rfl⟩)
    · refine (hB _).2 ⟨‖(x : C)‖, fun n => ?_⟩
      rw [PowerSeries.coeff_C]; split_ifs <;> simp
    · exact (hB _).2 ⟨b, hb a⟩

  set S : Set (PowerSeries ℂ) := PowerSeries.map e '' G with hS
  have hSc : S.Countable :=
    ((Set.countable_range _).union (Set.finite_range Φ).countable).image _
  have hSs : ∀ Ψ ∈ S, ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → Summable fun n => ‖PowerSeries.coeff n Ψ * u ^ n‖ := by
    rintro _ ⟨g, (⟨x, rfl⟩ | ⟨a, rfl⟩), rfl⟩ u hu0 hu
    · rw [PowerSeries.map_C]; exact summable_coeff_C_mul_pow _ _
    · simpa [PowerSeries.coeff_map] using hsum u hu0 hu a
  obtain ⟨u, ig, hu0, hu, hig, hige⟩ := _root_.GlobalTheory.exists_injective_evalAt_closure ε S hε hSc hSs
  have hmapA : ∀ x ∈ A, PowerSeries.map e x ∈ Subring.closure S := by
    intro x hx
    rw [hS, ← RingHom.map_closure]
    exact Subring.mem_map.2 ⟨x, hx, rfl⟩
  let m : A →+* Subring.closure S := (PowerSeries.map e).restrict A (Subring.closure S) hmapA
  have hm : ∀ x : A, (m x : PowerSeries ℂ) = PowerSeries.map e (x : PowerSeries C) := fun _ => rfl
  have hmapinj : Function.Injective (PowerSeries.map e) := by
    intro x y h
    ext n
    have := congrArg (PowerSeries.coeff n) h
    simp only [PowerSeries.coeff_map] at this
    exact e.injective this
  have hminj : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    apply hmapinj
    rw [← hm, ← hm, h]
  let i : A →+* ℂ := ig.comp m
  have hi : Function.Injective i := hig.comp hminj
  let f : A →+* B := Subring.inclusion hAB
  have hf : Function.Injective f := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  obtain ⟨W, _, _, _, _, _, g, i₀, i₁, hi₀, hgi₀, hgi₁, hunit, hprime⟩ :=
    _root_.GlobalTheory.MBLow.exists_localRing_of_order A B C ℂ f ev t i hf hi ht hevt hfin
  let cA : o →+* A := (PowerSeries.C.comp o.subtype).codRestrict A
    (fun x => Subring.subset_closure (Or.inl ⟨x, rfl⟩))
  have hΦA : ∀ a, Φ a ∈ A := fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  haveI : CharZero W := RingHom.charZero i₁
  refine ⟨u, o, inferInstance, inferInstance, o.subtype,
    fun a => ⟨c a, Subfield.subset_closure ⟨a, rfl⟩⟩, hu0, hu, fun a => rfl,
    W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g.comp cA, i₀, i₁, fun a => g ⟨Φ a, hΦA a⟩, hi₀, ?_, ?_, hunit, hprime, fun a => ⟨?_, ?_⟩⟩
  · ext x
    have h1 := RingHom.congr_fun hgi₀ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1]
    show ig (m (cA x)) = e x
    rw [hige, hm]
    show ∑' n, PowerSeries.coeff n (PowerSeries.map e (PowerSeries.C (x : C))) * u ^ n = e x
    rw [PowerSeries.map_C, tsum_coeff_C_mul_pow_eq]
  · ext x
    have h1 := RingHom.congr_fun hgi₁ (cA x)
    simp only [RingHom.comp_apply] at h1 ⊢
    rw [h1, hev]
    show ∑' n, PowerSeries.coeff n (PowerSeries.C (x : C)) * π ^ n = x
    rw [tsum_coeff_C_mul_pow_eq]
  · have h1 := RingHom.congr_fun hgi₀ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    show ig (m ⟨Φ a, hΦA a⟩) = _
    rw [hige, hm]
    simp only [PowerSeries.coeff_map]
  · have h1 := RingHom.congr_fun hgi₁ ⟨Φ a, hΦA a⟩
    simp only [RingHom.comp_apply] at h1
    rw [h1, hev]
    rfl

end GlobalTheory.MBLow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory


open IsLocalRing in
theorem valuationRing_atPrime_of_minimal {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ValuationRing (Localization.AtPrime q) := by
  have hT := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)
  have h1 : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime →
      Q' = maximalIdeal (Localization.AtPrime q) := by
    intro Q' hQ' hQ'p
    have hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q := by
      intro x hx
      by_contra hxq
      exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
    have hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥ := by
      intro h0
      apply hQ'
      rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
      rw [Ideal.under, h0, Ideal.map_bot]
    have heq := hmin _ hc hne hle
    rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
    rw [Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]
  have h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q),
      Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q) := ⟨h1, h2⟩
  exact (hT.out 4 2).mp h12

theorem mul_eq_mul_of_atPrime {A : Type} [CommRing A] [IsDomain A] (q : Ideal A) [q.IsPrime]
    (x y a : A) (s : q.primeCompl)
    (h : algebraMap A (Localization.AtPrime q) x * IsLocalization.mk' _ a s =
      algebraMap A (Localization.AtPrime q) y) : x * a = y * s := by
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  exact IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h

end GlobalTheory

namespace GlobalTheory

theorem exists_div_of_center_height_le_one : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring →
    (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) →
      ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) →
    ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  intro K _ R _ _ _ E hRE hyp e he
  classical
  let φ : R →+* E :=
    { toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : Ideal R := (IsLocalRing.maximalIdeal E).comap φ
  have hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1 := fun r => E.valuation_lt_one_iff (φ r)
  have hRv : ∀ r : R, E.valuation (r : K) ≤ 1 := fun r => (E.valuation_le_one_iff _).2 (hRE r.2)
  have hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1 := fun s hs =>
    le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))
  have hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E := by
    intro s hs
    rw [← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]
  have hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0 := by
    intro s hs h
    have := hv1 s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e
  dsimp only at hxy
  rw [IsFractionRing.mk'_eq_div] at hxy
  have hy0 : (algebraMap R K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  change ((x : R) : K) / ((y : R) : K) = e at hxy
  change ((y : R) : K) ≠ 0 at hy0
  by_cases hq : q = ⊥
  · have hyq : (y : R) ∉ q := by
      rw [hq, Ideal.mem_bot]
      intro h; apply hy0; rw [h]; rfl
    exact ⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩
  · have hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q := by
      intro p hp hp0 hpq
      refine le_antisymm hpq ?_
      intro r hr
      refine hyp p hp hp0 (fun t ht => ?_) r ?_
      · exact E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))
      · exact E.mem_nonunits_iff.2 ((hqmem r).1 hr)
    haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime q) x)
      (algebraMap R (Localization.AtPrime q) y)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c
    dsimp only at hc
    have hsq : (s : R) ∉ q := s.2
    rcases hc with hc | hc
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      by_cases haq : a ∈ q
      · exfalso
        have hea : e * (a : K) = ((s : R) : K) := by
          rw [← hxy]
          field_simp
          linear_combination hK
        have h1 := hv1 _ hsq
        rw [← hea, map_mul] at h1
        have hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K) :=
          mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)
        have := (hqmem a).1 haq
        rw [h1] at hle
        exact absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)
      · refine ⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩
        rw [← hxy, div_eq_div_iff hy0 (hne0 a haq)]
        linear_combination hK
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      refine ⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩
      rw [← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]
      linear_combination -hK

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVariety
section
noncomputable section

namespace GlobalTheory.SiegPt

section Algebra

open Polynomial IsLocalRing

end Algebra

section Level

open CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp unitOn omegaStd IsGrpPullback LBIso pushPt)

theorem sec_bijective {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] (X : Over (Sp O)) [IsProper X.hom]
    (e : Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ 𝟙_ (Over (Sp O))) :
    Function.Bijective fun x : 𝟙_ (Over (Sp O)) ⟶ X => e ≫ x := by
  have he : e.left = Geo.Tor.spMap (algebraMap O C) := (Category.comp_id _).symm.trans (Over.w e)
  have hE : ValuativeCriterion.Existence X.hom := by
    have h : UniversallyClosed X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness X.hom := IsSeparated.valuativeCriterion X.hom
  let S : (Over.mk (Geo.Tor.spMap (algebraMap O C)) ⟶ X) → ValuativeCommSq X.hom := fun z =>
    { R := O, K := C, i₁ := z.left, i₂ := 𝟙 _, commSq := ⟨(Over.w z).trans (Category.comp_id _).symm⟩ }
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have h₁ : Geo.Tor.spMap (algebraMap O C) ≫ x.left = (e ≫ x).left := congrArg (· ≫ x.left) he.symm
    have h₂ : Geo.Tor.spMap (algebraMap O C) ≫ y.left = (e ≫ x).left :=
      (congrArg (· ≫ y.left) he.symm).trans (congrArg Over.Hom.left hxy.symm)
    have := (hU (S (e ≫ x))).elim ⟨x.left, h₁, Over.w x⟩ ⟨y.left, h₂, Over.w y⟩
    exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)
  · obtain ⟨⟨l, h1, h2⟩⟩ := hE (S z)
    refine ⟨Over.homMk l h2, Over.OverMorphism.ext ?_⟩
    show e.left ≫ l = z.left
    rw [he]
    exact h1

theorem exists_secHom {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [Algebra O C]
    [IsFractionRing O C] {Q : Out.PolAV (Sp O)}
    {Q' : Out.PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left}
    (H : IsGrpPullback Q'.A Q.A (Geo.Tor.spMap (algebraMap O C)) ψ) (hw' : LBIso Q'.L (Q.L.pull ψ)) :
    ∃ ρ : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (𝟙_ (Over (Sp C)) ⟶ Q'.A), Function.Bijective ρ ∧
      ∀ (n : ℕ) x y (u : Oˣ), x ^ n = 1 → y ^ n = 1 →
        Out.WeilIs Q'.A Q'.L n (ρ x) (ρ y) (unitOn (Units.map (algebraMap O C).toMonoidHom u)) →
        Out.WeilIs Q.A Q.L n x y (unitOn u) := by
  have := Q.isAb.comm
  have := Q.isAb.proper
  have hG : Out.GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let β := algebraMap O C
  obtain ⟨b, hb⟩ := UnifPoint.exists_pointEquiv H
  let e : Over.mk (Geo.Tor.spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (Geo.Tor.spMap β) (Category.comp_id _)
  let r : (𝟙_ (Over (Sp O)) ⟶ Q.A) →* (Over.mk (Geo.Tor.spMap β) ⟶ Q.A) :=
    MonoidHom.mk' (fun x => e ≫ x) fun x y => MonObj.comp_mul _ _ _
  have hρ : ∀ x, (b.symm (r x)).left ≫ ψ = Geo.Tor.spMap β ≫ x.left := fun x => by
    rw [← hb, b.apply_symm_apply]; rfl
  refine ⟨b.symm.toMonoidHom.comp r, b.symm.bijective.comp (sec_bijective Q.A e), fun n x y u hx hy hw => ?_⟩
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hw' _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : Out.WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (hρ x) (hρ y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (IsFractionRing.injective O C h₅)
  exact hc

theorem exists_level {O C : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field C] [IsAlgClosed C] [Algebra O C]
    [IsFractionRing O C] (P : Out.PolAV (Sp O)) (h M : ℕ) (ze : Oˣ) (hg : P.g = h) (hM : IsUnit (M : O))
    (hz : IsPrimitiveRoot (algebraMap O C ze) M) :
    ∃ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp O)) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
      (∀ x, lev x ^ M = 1) ∧ ∀ x y, Out.WeilIs P.A P.L M (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  subst hg
  have hM' : (M : C) ≠ 0 := by
    have := (hM.map (algebraMap O C)).ne_zero
    rwa [map_natCast] at this
  haveI : NeZero M := ⟨fun h0 => hM' (by rw [h0, Nat.cast_zero])⟩
  obtain ⟨P', g, hg, hgg, hmul, tw, htw⟩ :=
    GlobalTheory.laws_without_cohomology.2.2.1 _ _ (Geo.Tor.spMap (algebraMap O C)) P
  have hp : IsGrpPullback P'.A P.A (Geo.Tor.spMap (algebraMap O C)) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [show x₀ = Out.toBase hg.w x from Over.OverMorphism.ext hx,
      show y₀ = Out.toBase hg.w y from Over.OverMorphism.ext hy, ← hmul]
    rfl⟩
  obtain ⟨ρ, hρ, hw⟩ := exists_secHom hp (Geo.Tor.LBIso.symm ⟨tw, htw⟩)
  obtain ⟨lev⟩ := nonempty_level_of_isAlgClosed C P' M (Units.map (algebraMap O C).toMonoidHom ze) hM'
    (IsPrimitiveRoot.coe_units_iff.1 hz)
  rw [← hgg]
  have := P'.isAb.comm
  choose t ht using fun a : Fin P'.g ⊕ Fin P'.g → ℤ =>
    hρ.2 (LevelCompare.homOfBasis lev (Multiplicative.ofAdd (fun j => (a j : ZMod M))))
  have tors : ∀ a, t a ^ M = 1 := fun a => hρ.1 (by rw [map_pow, ht, map_one, LevelCompare.hom_pow])
  refine ⟨t, fun a b => hρ.1 ?_, tors, fun a b => hw M _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, ← map_mul, ← ofAdd_add]
    exact congrArg _ (congrArg _ (funext fun j => Int.cast_add _ _))
  · rw [ht, ht, map_zpow]
    have w := LevelCompare.pairing_of_basis lev a b
    unfold unitOn at w ⊢
    rw [map_zpow]
    exact w

end Level

section Main

open CategoryTheory AlgebraicGeometry _root_.CategoryTheory.Limits NumberField IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

end Main

end GlobalTheory.SiegPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbFractionRingOfDominant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

theorem spMap_fractionRing_specializes (V : Type) [CommRing V] [IsDomain V] (w : Sp V) (p : Sp (FractionRing V)) :
    (spMap (algebraMap V (FractionRing V))) p ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
  show Ideal.comap (algebraMap V (FractionRing V)) p.asIdeal ≤ w.asIdeal
  have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal (PrimeSpectrum.isPrime p)
  rw [hp]
  intro x hx
  have hx' : algebraMap V (FractionRing V) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
  rw [(injective_iff_map_eq_zero _).1 (IsFractionRing.injective V (FractionRing V)) x hx']
  exact w.asIdeal.zero_mem

theorem exists_emb_fractionRing_of_dominant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∃ emb : Ω →+* FractionRing V, ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U → emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f) := by
  intro o Ω _ _ _ M V _ _ _ ξ ⟨w, hw⟩
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  let g0 : M.O z →+* V :=
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom.comp (M.stalkEquiv z).symm.toRingHom
  have hg0 : ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)) (hz : z ∈ U),
      g0 ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = valR ξ U f := by
    intro U f hz
    have h : ⊤ ≤ ξ ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff ξ U).2 hz
    have e1 : (M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f := by
      rw [RingEquiv.symm_apply_eq, RatModel.stalkEquiv_germ]
    have e2 := congrArg (fun φ => φ.hom f) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap ξ U h)
    change (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom ((M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩) = _
    rw [e1]
    rw [GlobalTheory.Points.valR_eq ξ U h]
    exact e2
  have hinj0 : Function.Injective g0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    obtain ⟨U, f, hz, rfl⟩ := RatModel.mem_O.1 hx
    rw [hg0 U f hz] at h0
    have hU : (U : Set M.Z).Nonempty := ⟨z, hz⟩
    by_cases hf : f = 0
    · subst hf
      apply Subtype.ext
      show valF M.pt U 0 = 0
      rw [← M.res_apply U hU, map_zero]
    · exfalso
      have hb : M.Z.basicOpen f ≠ ⊥ := fun hb => hf ((basicOpen_eq_bot_iff f).1 hb)
      obtain ⟨y, hy⟩ : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        exact fun h => hb (SetLike.coe_injective h)
      have hgen : genericPoint M.Z ∈ M.Z.basicOpen f :=
        (genericPoint_specializes y).mem_open (M.Z.basicOpen f).isOpen hy
      let eta : Sp (FractionRing V) ⟶ M.Z := spMap (algebraMap V (FractionRing V)) ≫ ξ
      have heta : ⊤ ≤ eta ⁻¹ᵁ M.Z.basicOpen f := by
        intro p _
        have hs : eta p ⤳ genericPoint M.Z := by
          rw [← hw]
          exact (spMap_fractionRing_specializes V w p).map ξ.continuous
        exact hs.mem_open (M.Z.basicOpen f).isOpen hgen
      have hetaU : ⊤ ≤ eta ⁻¹ᵁ U := heta.trans (eta.preimage_mono (M.Z.basicOpen_le f))
      have hu := (GlobalTheory.Points.le_preimage_basicOpen_iff eta hetaU f).1 heta
      rw [GlobalTheory.Points.valR_spMap_comp _ ξ U ((GlobalTheory.Points.le_preimage_iff ξ U).2 hz), h0, map_zero] at hu
      exact not_isUnit_zero hu
  let g : M.O z →+* FractionRing V := (algebraMap V (FractionRing V)).comp g0
  have hinj : Function.Injective g := (IsFractionRing.injective V (FractionRing V)).comp hinj0
  refine ⟨IsFractionRing.lift hinj, fun U f hz => ?_⟩
  have e : valF M.pt U f = algebraMap (M.O z) Ω ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ := rfl
  rw [e, IsFractionRing.lift_algebraMap]
  show algebraMap V (FractionRing V) (g0 _) = _
  rw [hg0 U f hz]

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapEqOfGroupInvariantStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionFieldMap_eq_of_groupInvariant : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ u : X.functionFieldˣ,
    (∀ γ, fnAct ρ γ u = u) → ∃ b : W.functionFieldˣ, Units.map (functionFieldMap q).toMonoidHom b = u := by
  first | exact @GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | exact GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant | (intros; apply GlobalTheory.OrbitSep.exists_functionFieldMap_eq_of_invariant <;> assumption)
end

