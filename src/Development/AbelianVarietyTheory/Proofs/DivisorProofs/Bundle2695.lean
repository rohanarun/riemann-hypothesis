module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mix.cycInt_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  intro k K _ _ _ _ X G _ p q j hp τ e hX L f x hx
  obtain ⟨hGi, hGn, hGproj, hGdim, hgen, hinj, hstalk, hcoh, hempty⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) hX
  obtain ⟨hZi, hZgen, hZdim, hZuniv⟩ := GlobalTheory.ClosFacts.clos_facts X (j x)
  obtain ⟨hxi, hxgen, -, hxuniv⟩ := GlobalTheory.ClosFacts.clos_facts G x

  have hK : CharZero K := by
    have := hX.charZero_base
    exact (RingHom.charZero_iff (IsFractionRing.injective k K)).1 inferInstance
  have hc : CharZero Γ(clos (j x), ⊤) := by
    obtain ⟨g0, hg0, -, -, -⟩ := hZuniv (clos x) (closι x ≫ j) (by
      simp only [Scheme.Hom.comp_apply, hxgen])
    have : IsDomain Γ(clos x, ⊤) := inferInstance
    let φ : K →+* Γ(clos x, ⊤) :=
      ((closι x ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have : CharZero Γ(clos x, ⊤) := (RingHom.charZero_iff φ.injective).1 hK
    exact g0.appTop.hom.charZero
  have hdim : topologicalKrullDim (clos (j x)) = (e + 1 : ℕ) := by
    rw [hZdim]
    have h1 := (GlobalTheory.MixHt.dimOne k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) (e + 1) hX.dim_eq).1 (j x)
    exact h1.1 ((hcoh x).trans hx)
  have hZ : IsArithVar (closι (j x) ≫ p) e := hX.of_isClosedImmersion (closι (j x)) hc hdim
  haveI := hZi
  let G' := Limits.pullback (closι (j x) ≫ p) (spMap (algebraMap k K))
  let j' : G' ⟶ clos (j x) := Limits.pullback.fst _ _
  let q' : G' ⟶ Sp K := Limits.pullback.snd _ _
  have hp' : IsPullback j' q' (closι (j x) ≫ p) (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hG'i, -, hG'proj, -, hG'gen, -, -, -, -⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K (clos (j x)) G' (closι (j x) ≫ p) q' j' hp' e hZ
  have hw : (j' ≫ closι (j x)) ≫ p = q' ≫ spMap (algebraMap k K) := by
    rw [Category.assoc]; exact hp'.w
  let g : G' ⟶ G := hp.lift (j' ≫ closι (j x)) q' hw
  have hg1 : g ≫ j = j' ≫ closι (j x) := hp.lift_fst _ _ hw
  have hg2 : g ≫ q = q' := hp.lift_snd _ _ hw
  have hp'' : IsPullback j' (g ≫ q) (closι (j x) ≫ p) (spMap (algebraMap k K)) := by rw [hg2]; exact hp'
  have hsq : IsPullback g j' j (closι (j x)) := IsPullback.of_right hp''.flip hg1 hp.flip
  have : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have hgx : g (genericPoint G') = x := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply, hG'gen, hZgen]
  have hproj'' : IsProjOver (g ≫ q) := by rw [hg2]; exact hG'proj
  obtain ⟨-, h1⟩ := _root_.GlobalTheory.Mix.cycInt_of_closedImmersion K G G' q (g ≫ q) τ hGproj g rfl e (fun i => (L i).bc hp.w τ)
    (fun y => f (bcPt hp.w τ y))
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.MixGen.part_int_generic k K (clos (j x)) G' (closι (j x) ≫ p) (g ≫ q) j' hp'' τ e hZ
    (fun i => (L i).pull (closι (j x)) rfl)
  have h3 := fun i => GlobalTheory.Mix.BcPull.bc_pull_isom k K (algebraMap k K) X G (clos (j x)) G' p q j hp.w (closι (j x)) j' g hg1
    hp''.w τ (L i)
  have h4 := _root_.GlobalTheory.Mix.part_eq_of_isom K G' (g ≫ q) τ hproj'' e _ _ h3
  conv_lhs => rw [← hgx]
  rw [h1]
  have h5 := (h2 (fun y => f (ptMap (closι (j x)) rfl _ y))).2
  change _ = Mix.int _ _
  rw [← h5]
  unfold Mix.int
  rw [h4 1, h4 (-1)]
  congr 2 <;> (funext y; exact congrArg f (Subtype.ext (by
    simp only [bcPt_val, PtsOver.map_val, ptMap, Category.assoc, hg1])))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDvdOfEqNatMulIntegralAdeleAwayFromP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LKGeo.IntDvd

open IsDedekindDomain HeightOneSpectrum

theorem int_dvd_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) (c : ℤ)
    (h : ∀ v : AwayP p, ∃ y ∈ v.1.adicCompletionIntegers ℚ,
      algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ) = algebraMap ℚ (v.1.adicCompletion ℚ) ((n : ℤ) : ℚ) * y) :
    (n : ℤ) ∣ c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    simp
  · obtain ⟨ℓ, hℓ, n₁, hn₁⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n₁, n = ℓ * n₁ :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hℓp : ℓ ≠ p := by
      intro he
      have h3 : ℓ.Coprime p := Nat.Coprime.coprime_dvd_left ⟨n₁, hn₁⟩ hc
      rw [he, Nat.coprime_self] at h3
      exact (Fact.out : p.Prime).one_lt.ne' h3
    let w : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)},
      (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ),
      by simp [hℓ.ne_zero]⟩
    have hw : w.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro he
      rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at he
      simp only [Int.natAbs_natCast] at he
      exact hℓp he
    let v : AwayP p := ⟨w, hw⟩
    have hval : ∀ c : ℤ, Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (c : ℚ)) = v.1.intValuation c := by
      intro c
      rw [← valuation_of_algebraMap (K := ℚ), ← valuedAdicCompletion_eq_valuation]
      rfl
    have hℓc : (ℓ : ℤ) ∣ c := by
      obtain ⟨y, hy, e⟩ := h v
      have hy' : Valued.v y ≤ 1 := (mem_adicCompletionIntegers ℤ ℚ v.1).1 hy
      have h1 : v.1.intValuation c ≤ v.1.intValuation (n : ℤ) := by
        rw [← hval, ← hval, e, map_mul]
        exact mul_le_of_le_one_right' hy'
      have h2 : v.1.intValuation (n : ℤ) < 1 :=
        (intValuation_lt_one_iff_mem _ _).2 (Ideal.mem_span_singleton.2 ⟨n₁, by rw [hn₁]; push_cast; ring⟩)
      exact Ideal.mem_span_singleton.1 ((intValuation_lt_one_iff_mem _ _).1 (lt_of_le_of_lt h1 h2))
    obtain ⟨c₁, rfl⟩ := hℓc
    have hn₁pos : 0 < n₁ := by
      rcases Nat.eq_zero_or_pos n₁ with h0 | h0
      · rw [h0, mul_zero] at hn₁; omega
      · exact h0
    have hlt : n₁ < n := by
      rw [hn₁]; exact lt_mul_left hn₁pos hℓ.one_lt
    have hc₁ : n₁.Coprime p := Nat.Coprime.coprime_dvd_left ⟨ℓ, by rw [hn₁, Nat.mul_comm]⟩ hc
    have hd : (n₁ : ℤ) ∣ c₁ := ih n₁ hlt hn₁pos hc₁ c₁ fun v' => by
      obtain ⟨y, hy, e⟩ := h v'
      refine ⟨y, hy, ?_⟩
      have hne : algebraMap ℚ (v'.1.adicCompletion ℚ) ((ℓ : ℤ) : ℚ) ≠ 0 :=
        (map_ne_zero _).2 (by exact_mod_cast hℓ.ne_zero)
      apply mul_left_cancel₀ hne
      rw [← map_mul, ← _root_.mul_assoc, ← map_mul, ← Int.cast_mul, ← Int.cast_mul, e, hn₁]
      push_cast
      ring
    rw [hn₁]
    push_cast
    exact mul_dvd_mul_left _ hd

theorem int_dvd_of_eq_mul_isIntAf : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p),
    IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  intro p _ n hn hc c a ha e
  refine int_dvd_of_local p n hn hc c fun v => ⟨AfP.eval v a, ha v, ?_⟩
  have e' := congrArg (AfP.eval v) e
  rw [(AfP.eval v).commutes, map_mul, map_natCast] at e'
  rw [e']
  simp

end GlobalTheory.LKGeo.IntDvd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.OmegaCoord

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_eq_zero_of_mem_sq {g : MvPowerSeries (Fin d) k}
    (hg : g ∈ RingHom.ker (constantCoeff (R := k) (σ := Fin d)) ^ 2) (α : Fin d →₀ ℕ)
    (hα : α.degree < 2) : coeff α g = 0 := by
  rw [pow_two] at hg
  refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg : q.1.degree + q.2.degree < 2 := by rw [← map_add (f := _), hq]; exact hα
    rw [RingHom.mem_ker] at ha hb
    rcases Nat.lt_or_ge q.1.degree 1 with h | h
    · have : q.1 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, ha, zero_mul]
    · have : q.2 = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      rw [this, coeff_zero_eq_constantCoeff_apply, hb, mul_zero]
  · rw [map_add (f := _), ha, hb, add_zero]

variable {A : Type} [CommRing A] [Bialgebra k A] (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i))
  (haug : ∀ i, Coalgebra.counit (R := k) (x i) = 0)


include haug in
theorem exists_eq_sum (hsurj : Function.Surjective (evA k x hx)) (u : Cot k A) :
    ∃ w : Fin d → k, u = ∑ i, w i • dUnit (R := k) (x i) := by
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ u
  obtain ⟨f, rfl⟩ := hsurj a
  exact ⟨lin f, (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f).2⟩


include haug in
theorem eq_zero_of_sum (hsurj : Function.Surjective (evA k x hx))
    (hker : ∀ f, evA k x hx f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0)
    (w : Fin d → k) (hw : ∑ i, w i • dUnit (R := k) (x i) = 0) : w = 0 := by
  set f : MvPowerSeries (Fin d) k := ∑ i, w i • X i with hf
  have hlin : lin f = w := by
    funext i
    simp [f, lin, coeff_X, Finsupp.single_eq_single_iff]
  have hcc : constantCoeff f = 0 := by simp [f]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug f
  have hd : dUnit (R := k) (evA k x hx f) = 0 := by rw [h2, hlin, hw]
  have hε : ∀ g, Bialgebra.counitAlgHom k A (evA k x hx g) = constantCoeff g := fun g =>
    (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k d A x hx haug g).1
  rw [dUnit, AugCot.d_eq_zero_iff, hε, hcc, map_zero, sub_zero] at hd
  have hK : RingHom.ker (Bialgebra.counitAlgHom k A) =
      Ideal.map (evA k x hx) (RingHom.ker (constantCoeff (R := k) (σ := Fin d))) := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective _ hsurj]
    constructor
    · intro ha
      obtain ⟨g, rfl⟩ := hsurj a
      refine ⟨g, ?_, rfl⟩
      rw [RingHom.mem_ker] at ha ⊢
      rw [← hε]; exact ha
    · rintro ⟨g, hg, rfl⟩
      rw [RingHom.mem_ker] at hg ⊢
      rw [hε]; exact hg
  rw [hK, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hsurj] at hd
  obtain ⟨g, hg, hgf⟩ := hd
  have hfg : evA k x hx (f - g) = 0 := by rw [map_sub, hgf, sub_self]
  funext i
  have hdeg : (Finsupp.single i 1 : Fin d →₀ ℕ).degree < 2 := by simp
  have e1 := hker _ hfg (Finsupp.single i 1) hdeg
  rw [map_sub, coeff_eq_zero_of_mem_sq hg _ hdeg, sub_zero] at e1
  rw [← hlin]; exact e1

end GlobalTheory.OmegaCoord

namespace GlobalTheory.OmegaCoord

theorem omega_coord : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub) ∧
      ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
  intro p k _ d G c
  have hres : ∀ n (w : Fin d → k), cotMap (G.res n) (∑ i, w i • dUnit (R := k) (c.x (n + 1) i)) =
      ∑ i, w i • dUnit (R := k) (c.x n i) := by
    intro n w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, cotMap_d, c.res]
  refine ⟨fun w n => hres n w, fun u => ?_⟩
  have hu : ∀ n, cotMap (G.res n) (u.1 (n + 1)) = u.1 n := u.2
  obtain ⟨n0, hn0⟩ := c.presents.2 2
  have hone := (_root_.GlobalTheory.Katz.Chart.functions_are_series p k d G c).1
  have hker : ∀ j f, c.ev (n0 + j) f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < 2 → coeff α f = 0 := by
    intro j
    induction j with
    | zero => exact hn0
    | succ j ih =>
      intro f hf
      refine ih f ?_
      rw [← hone (n0 + j) f]
      exact (congrArg (G.res (n0 + j)) hf).trans (map_zero _)
  have hind : ∀ j (v w : Fin d → k), ∑ i, v i • dUnit (R := k) (c.x (n0 + j) i) =
      ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) → v = w := by
    intro j v w h
    have := eq_zero_of_sum (c.x (n0 + j)) (c.nil _) (c.aug _) (c.presents.1 _) (hker j) (v - w)
      (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    exact sub_eq_zero.1 this
  have hspan : ∀ n, ∃ w : Fin d → k, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := fun n =>
    exists_eq_sum (c.x n) (c.nil n) (c.aug n) (c.presents.1 n) (u.1 n)
  obtain ⟨w, hw⟩ := hspan n0
  have hup : ∀ j, u.1 (n0 + j) = ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) := by
    intro j
    induction j with
    | zero => exact hw
    | succ j ih =>
      obtain ⟨v, hv⟩ := hspan (n0 + j + 1)
      have h1 : ∑ i, v i • dUnit (R := k) (c.x (n0 + j) i) = ∑ i, w i • dUnit (R := k) (c.x (n0 + j) i) := by
        rw [← hres, ← hv, hu, ih]
      rw [← hind j v w h1]
      exact hv
  have hdown : ∀ n j, u.1 (n + j) = ∑ i, w i • dUnit (R := k) (c.x (n + j) i) →
      u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
    intro n j
    induction j with
    | zero => exact id
    | succ j ih =>
      intro h
      refine ih ?_
      rw [← hu, ← hres]
      exact congrArg (cotMap (G.res (n + j))) h
  refine ⟨w, fun n => hdown n n0 (by rw [Nat.add_comm]; exact hup n), fun w' hw' => ?_⟩
  exact hind 0 w' w ((hw' n0).symm.trans (hup 0))

end GlobalTheory.OmegaCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
namespace GlobalTheory.ClosedLev

theorem exists_nhd (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
    (p : Z ⟶ Spec (CommRingCat.of R)) (hφ : IsProper φ)
    (hc : IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ)) (z : Z)
    (hz : I ≤ (p z).asIdeal) : ∃ U : Z.Opens, z ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
  have hfin : (⇑φ ⁻¹' {z}).Finite := (_root_.GlobalTheory.FormalAlg.fibre_subsingleton_of_isClosedImmersion_restrict R I X Z φ p hc z hz).finite
  obtain ⟨V₀, hzV₀, hV₀⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ z hfin
  obtain ⟨V, hV, hzV, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hzV₀
  have hVf : IsFinite (φ ∣_ V) := GlobalTheory.PushFinite.isFinite_restrict_of_le φ hle
  obtain ⟨haff, hfr⟩ := _root_.GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict X Z φ V hV hVf
  obtain ⟨r, hr1, hr⟩ := _root_.GlobalTheory.finite_surj_mod_ideal_exists_congr_one_mul_mem_range _ _ (φ.app V).hom hfr _ (_root_.GlobalTheory.FormalAlg.surj_mod_baseIdeal_of_isClosedImmersion R I X Z φ p hc V hV haff)
  exact ⟨Z.basicOpen r, GlobalTheory.T.mem_basicOpen_of_sub_one_mem_baseIdealSheaf R I Z p V hV r z hzV hz hr1, _root_.GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range X Z φ V hV haff r hr⟩

theorem isClosedImmersion_of_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  intro R _ I hI X Z φ p hφ hp hc
  let O : Z.Opens := ⨆ U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)}, U.1
  have hO : O = ⊤ := by
    have h0 := _root_.GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson R I hI Z p hp ((O : Set Z)ᶜ) O.isOpen.isClosed_compl fun z hz hIz => by
      obtain ⟨U, hzU, hU⟩ := exists_nhd R I X Z φ p hφ hc z hIz
      exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU⟩, hzU⟩)
    exact TopologicalSpace.Opens.ext (by simpa [Set.compl_empty_iff] using h0)
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun U : {U : Z.Opens // IsClosedImmersion (φ ∣_ U)} => U.1) hO fun U => U.2

end GlobalTheory.ClosedLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairGramLowerTriangularFactorStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (fun y z => ldPart (gramAt E H τ y z)) := by
  first | exact @GlobalTheory.ChernCalc.isGramPair_ldPart | exact GlobalTheory.ChernCalc.isGramPair_ldPart | (intros; apply GlobalTheory.ChernCalc.isGramPair_ldPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem isOpen_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ hU n S K' hK
  have hT : {w : Pl E | ¬ K' w = KL n w}.Finite := Filter.eventually_cofinite.1 hK.2
  let f : ∀ w : Pl E, finU (E := E) (n := n) → UL n w := fun w x => ⟨cLoc w x.1, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w x.1⟩
  have hf : ∀ w, Continuous (f w) := fun w =>
    Continuous.subtype_mk ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val) _
  have h1 : ∀ w, f w 1 = 1 := fun w => Subtype.ext (by simp [f])
  have hA : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w : Pl E, cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [(UpperTheory.unitaryAdelic_localComponents_continuous_levels_open E n).2.2] with k hk w
    exact (SetLike.ext_iff.1 (GlobalTheory.SmGL.SphCompletion.KO_completion w n) _).1 (hk w)
  have hB : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w ∈ {w : Pl E | ¬ K' w = KL n w}, f w k ∈ K' w := by
    refine (Filter.eventually_all_finite hT).2 fun w _ => ?_
    have ho : IsOpen ((f w) ⁻¹' (K' w : Set (UL n w))) := ((hK.1 w).1).preimage (hf w)
    exact ho.mem_nhds (by simp [h1])
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hA, hB] with x hxA hxB
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun _ => ?_
  refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨f w x, ?_, rfl⟩)
  by_cases hw : K' w = KL n w
  · rw [hw]
    exact Subgroup.mem_subgroupOf.2 (hxA w)
  · exact hxB w hw

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslA
section
noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsTranslA (f : D.La →+ D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) ∧ (∀ x, o'.eta x = o.eta (f x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSubA o f N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerVacuumEigenvalueEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  first | exact @GlobalTheory.DblVac.eigen_eq_one | exact GlobalTheory.DblVac.eigen_eq_one | (intros; apply GlobalTheory.DblVac.eigen_eq_one <;> assumption)
end

