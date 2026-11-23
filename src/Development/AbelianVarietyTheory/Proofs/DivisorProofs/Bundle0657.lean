module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

private lemma twist_estimate_first (a b e M : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 2 ≤ e) (hb : 0 < b)
    (hM : 0 ≤ M) (h : e + a ^ 2 / b ≤ 8 * (1 + M)) :
    0 ≤ a / e ∧ a / e ≤ 1 ∧ 0 < (b * e + a ^ 2) / e ^ 2 ∧ (a / e) ^ 2 ≤ (b * e + a ^ 2) / e ^ 2 ∧
      1 / (1 + M) / 8 ≤ (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one he0]; linarith
  · rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < b * e := by positivity
    linarith
  · have e1 : (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ = 1 / (e + a ^ 2 / b) := by
      field_simp
      ring
    have e2 : 1 / (1 + M) / 8 = 1 / (8 * (1 + M)) := by
      field_simp
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) h

private lemma twist_estimate_second (a b e m : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 300 ≤ e) (hb : 3 / 16 ≤ b)
    (h : e ≤ 2 + 2 * m) :
    e⁻¹ / ((b * e + a ^ 2) / e ^ 2) ≤ 16 / 3 ∧
      1 / (1 + m ^ 2) / 8 ≤ (1 - 5 * ((a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2))) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hb0 : 0 < b := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  have hbe : 3 / 16 * e ≤ b * e := mul_le_mul_of_nonneg_right hb he0.le
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have ha0 : 0 ≤ a ^ 2 := by positivity
  constructor
  · have e1 : e⁻¹ / ((b * e + a ^ 2) / e ^ 2) = e / (b * e + a ^ 2) := by
      field_simp
    rw [e1, div_le_iff₀ hD]
    linarith
  · have e1 : (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2) = a ^ 2 / (b * e + a ^ 2) := by
      field_simp
    have h1 : a ^ 2 / (b * e + a ^ 2) ≤ 1 / 10 := by
      rw [div_le_iff₀ hD]; linarith
    have e2 : 1 / (1 + m ^ 2) / 8 = 1 / 2 * (4 * (1 + m ^ 2))⁻¹ := by
      field_simp
      norm_num
    have h2 : (4 * (1 + m ^ 2))⁻¹ ≤ e⁻¹ := by
      apply inv_anti₀ he0
      nlinarith [sq_nonneg (m - 1 / 4)]
    rw [e1, e2]
    apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)

theorem exists_log_twist : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  intro T hT
  obtain ⟨η, η1, η2, hs, hd, hp, hw⟩ := _root_.GlobalTheory.concave_twist_exists T hT
  set κ : ℝ → ℝ := fun x => Real.smoothTransition (2 - 16 * x) * (-Real.log (η (-x))) with hκ
  have hloc : ∀ x : ℝ, x < 1 / 16 → κ x = -Real.log (η (-x)) := by
    intro x hx
    simp only [hκ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have hη : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η (-x)) (-η1 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.1
    have h' := HasDerivAt.comp x (h₂ := η) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hη1 : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η1 (-x)) (-η2 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.2
    have h' := HasDerivAt.comp x (h₂ := η1) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hd1 : ∀ x : ℝ, x < 1 / 16 → deriv κ x = η1 (-x) / η (-x) := by
    intro x hx
    have hev : κ =ᶠ[𝓝 x] fun x => -Real.log (η (-x)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hloc y hy
    rw [hev.deriv_eq]
    have h := ((hη x hx).log (hd (-x) (by linarith)).1.ne').neg
    have h2 : HasDerivAt (fun x => -Real.log (η (-x))) (-(-η1 (-x) / η (-x))) x := h
    rw [h2.deriv]; ring
  have hd2 : ∀ x : ℝ, x < 1 / 16 →
      deriv (deriv κ) x = ((-η2 (-x)) * η (-x) + η1 (-x) ^ 2) / η (-x) ^ 2 := by
    intro x hx
    have hev : deriv κ =ᶠ[𝓝 x] fun x => η1 (-x) / η (-x) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hd1 y hy
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun x => η1 (-x) / η (-x)) _ x :=
      (hη1 x hx).div (hη x hx) (hd (-x) (by linarith)).1.ne'
    rw [h2.deriv]; ring
  have hexp : ∀ x : ℝ, x < 1 / 16 → Real.exp (κ x) = (η (-x))⁻¹ := by
    intro x hx
    rw [hloc x hx, Real.exp_neg, Real.exp_log (hd (-x) (by linarith)).1]
  have hwT : ∀ x : ℝ, x ≤ 0 → wT T x = 1 / (1 + (min (-x) (T + 1)) ^ 2) := by
    intro x hx
    unfold wT
    congr 2
    rcases le_total (-x) (T + 1) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  refine ⟨κ, ?_, ⟨Real.log (2 * T + 4), ?_⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 4
    · have h1 : ContDiffAt ℝ ∞ η (-x) :=
        hs.contDiffAt (Ioi_mem_nhds (by linarith))
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => η (-x)) x :=
        ContDiffAt.comp x (g := η) (f := fun x : ℝ => -x) h1 contDiff_neg.contDiffAt
      have h3 := (h2.log (hd (-x) (by linarith)).1.ne').neg
      have h4 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (2 - 16 * x)) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact h4.contDiffAt.mul h3
    · have hev : κ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (1 / 8 : ℝ) < x by linarith)] with y hy
        have hy' : (1 / 8 : ℝ) < y := hy
        simp only [hκ]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    obtain ⟨-, -, h2, -, h3, -⟩ := hp (-x) (by linarith)
    rw [hloc x (by linarith), abs_neg, abs_of_nonneg (Real.log_nonneg (by linarith))]
    apply Real.log_le_log (by linarith)
    have := min_le_right (-x) (T + 1)
    linarith
  · intro x hx
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, h2, h3, -, h5⟩ := hp (-x) (by linarith)
    rw [hd1 x hx', hd2 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_first _ _ _ _ h0 h1 h2 (by linarith) (sq_nonneg _) h5
  · intro x hx1 hx2
    have hx : x ≤ 0 := by linarith
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, -, -, h4, -⟩ := hp (-x) (by linarith)
    obtain ⟨h6, h7⟩ := hw (-x) (by linarith) (by linarith)
    rw [hd2 x hx', hd1 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_second _ _ _ _ h0 h1 (by linarith) h6 h4

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPoint
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfIsAdicColimit
section
open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AdicColimit

namespace GlobalTheory.FinitePointLimit

theorem existsUnique_of_isAdicColimit {B : Type} [CommRing B] (J : Ideal B)
    (h : IsAdicColimit J (Over.mk (𝟙 (Sp B)))) (X : Scheme.{0}) (z : ∀ e : ℕ, Sp (B ⧸ J ^ (e + 1)) ⟶ X)
    (hz : ∀ e : ℕ, Out.thickTrans B J e ≫ z (e + 1) = z e) :
    ∃! x : Sp B ⟶ X, ∀ e : ℕ, Out.thick B J e ≫ x = z e := by
  have hι : ∀ e : ℕ, thickι J e (Over.mk (𝟙 (Sp B))) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thick B J e := by
    intro e
    have hc := pullback.condition (f := (Over.mk (𝟙 (Sp B))).hom) (g := Out.thick B J e)
    show pullback.fst _ _ = _
    simpa using hc
  have hiso : ∀ e : ℕ, IsIso (pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e)) := by
    intro e
    have : IsIso (Over.mk (𝟙 (Sp B))).hom := by
      show IsIso (𝟙 _)
      infer_instance
    infer_instance
  have hmap : ∀ e : ℕ, Out.thickMap B J e (Over.mk (𝟙 (Sp B))) ≫
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J (e + 1)) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thickTrans B J e := by
    intro e
    rw [← cancel_mono (Out.thick B J (e + 1)), Category.assoc, Category.assoc,
      Out.thickTrans_comp, ← hι, ← hι, thickMap_ι]
  obtain ⟨g, hg, hu⟩ := h X
    (fun e => pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ z e) (by
      intro e
      rw [← Category.assoc, hmap, Category.assoc, hz])
  refine ⟨g, fun e => ?_, fun x hx => hu x fun e => ?_⟩
  · have he := hg e
    rw [hι, Category.assoc] at he
    have := hiso e
    exact (cancel_epi _).mp he
  · rw [hι, Category.assoc, hx]

end GlobalTheory.FinitePointLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivEqFderivZeroOfConstDifferences
section
open Filter Topology

namespace GlobalTheory

theorem fderiv_eq_fderiv_zero_of_const_differences {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ)
    (hG : Differentiable ℂ G) (hp : ∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l)
    (v : Fin g → ℂ) : fderiv ℂ G v = fderiv ℂ G 0 := by
  have hd : Differentiable ℂ (fun w => G (w + v) - G w) :=
    (hG.comp (differentiable_id.add_const v)).sub hG
  have hc : ∀ w, G (w + v) - G w = G (0 + v) - G 0 := fun w =>
    entire_apply_eq_of_periodic_of_span_real hd hΛ (fun x l hl => by
      have h1 := hp ⟨l, hl⟩ (x + v)
      have h2 := hp ⟨l, hl⟩ x
      simp only at h1 h2
      show G (x + l + v) - G (x + l) = G (x + v) - G x
      rw [add_right_comm, h1, h2]
      ring) w 0
  have he : (fun w => G (w + v)) = fun w => G w + (G (0 + v) - G 0) := by
    funext w
    rw [← hc w]
    ring
  have h1 : fderiv ℂ (fun w => G (w + v)) 0 = fderiv ℂ G (0 + v) := fderiv_comp_add_right v
  rw [he, fderiv_add_const, zero_add v] at h1
  exact h1.symm

theorem fderiv_zero_eq_of_const_differences :
    ∀ {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (G : (Fin g → ℂ) → ℂ) (p : Λ → ℂ), Differentiable ℂ G →
        (∀ (l : Λ) (w : Fin g → ℂ), G (w + l) = G w + p l) →
        ∀ l : Λ, fderiv ℂ G 0 l = p l := by
  intro g Λ hΛ G p hG hp l
  have hk := fderiv_eq_fderiv_zero_of_const_differences Λ hΛ G p hG hp
  have hd : Differentiable ℂ (fun w => G w - fderiv ℂ G 0 w) :=
    hG.sub (fderiv ℂ G 0).differentiable
  have hz : ∀ w, fderiv ℂ (fun w => G w - fderiv ℂ G 0 w) w = 0 := fun w => by
    have := ((hG w).hasFDerivAt.sub (fderiv ℂ G 0).hasFDerivAt).fderiv
    rw [hk w, sub_self] at this
    exact this
  have h := is_const_of_fderiv_eq_zero hd hz (l : Fin g → ℂ) 0
  have h2 := hp l 0
  rw [zero_add] at h2
  simp only [map_zero, sub_zero] at h
  rw [h2] at h
  linear_combination -h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLeStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSum_smoothSection_dbarEnergy_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ), (∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) → A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧ n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  first | exact @GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | exact GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | (intros; apply GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFirstDeRhamHomologyHodgeFiltrationOfField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_HdR_Fil_of_field (HF : GlobalTheory.Published.AbelianDeRham.Free)
    (HH : GlobalTheory.Published.AbelianDeRham.Hodge) (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    FiniteDimensional k (HdR A) ∧ Module.finrank k (HdR A) = 2 * g ∧
      Module.finrank k (Fil A) = g := by
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim HF hA hg
  obtain ⟨-, -, hfin1, -, hrk1⟩ := HH k A g hA hg
  have p : PrimeSpectrum k := IsLocalRing.closedPoint k
  have h1 : Module.finrank k (primDR A) = 2 * g := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (PrimitiveSubmodule A) = g := by
    have := hrk1 p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hd : Module.finrank k (HdR A) = 2 * g := by
    change Module.finrank k (Module.Dual k (primDR A)) = 2 * g
    rw [Subspace.dual_finrank_eq, h1]
  refine ⟨?_, hd, ?_⟩
  · change FiniteDimensional k (Module.Dual k (primDR A))
    infer_instance
  · have := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
    rw [h2, h1] at this
    change Module.finrank k (PrimitiveSubmodule A).dualAnnihilator = g
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsAffineOpenOfFlatSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_sections_affineOpen_of_flat_scheme : ∀ (R' : Type) [CommRing R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R'), Flat s' → ∀ U : X'.affineOpens, Module.Flat R' (Sec s' U.1) := by
  first | exact @GlobalTheory.CechDR.flat_sec | exact GlobalTheory.CechDR.flat_sec | (intros; apply GlobalTheory.CechDR.flat_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryMultiplicationDefectMul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem cob1_defect_and_defect_mul_of_isLaw : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (f : MvPowerSeries (Fin d) E) (m n : ℕ),
    cob1 (up E μ) (defect μ n f) = (n : E) • cob1 (up E μ) f - pull2 (up E (nmul μ n)) (cob1 (up E μ) f) ∧
    defect μ (m * n) f = (m : E) • defect μ n f + subst (up E (nmul μ n)) (defect μ m f) := by
  intro O E _ _ _ d μ hμ f m n
  obtain ⟨hL, hmap⟩ := _root_.GlobalTheory.isLaw_map_nmul O d μ hμ E (algebraMap O E)
  have hup : ∀ k, up E (nmul μ k) = nmul (up E μ) k := fun k =>
    funext fun i => (hmap k i).2
  have hc : ∀ i, constantCoeff (up E μ i) = 0 := hL.const
  have hk : ∀ k, HasSubst (up E (nmul μ k)) := fun k =>
    hasSubst_of_constantCoeff_zero fun i => by
      rw [hup k]; exact ((_root_.GlobalTheory.NMul.nmul_laws E d (up E μ) hL 0 k).1 i)
  have hsub : ∀ a b : MvPowerSeries (Fin d) E, cob1 (up E μ) (a - b) = cob1 (up E μ) a - cob1 (up E μ) b :=
    fun a b => by rw [eq_sub_iff_add_eq, ← formalCoboundary_add hc, sub_add_cancel]
  refine ⟨?_, ?_⟩
  · unfold defect
    rw [hsub, formalCoboundary_smul hc, hup n]
    rw [_root_.GlobalTheory.Katz.CobPull.cob1_subst_eq_pull2_of_isHom_formal E d (up E μ) (up E μ) (nmul (up E μ) n) hc hc (_root_.GlobalTheory.NMulHom.isHom_nmul E d (up E μ) hL n) f]
  · have hcomp : subst (up E (nmul μ n)) (subst (up E (nmul μ m)) f) = subst (up E (nmul μ (m * n))) f := by
      rw [subst_comp_subst_apply (hk m) (hk n)]
      congr 1
      funext i
      rw [hup, hup, hup, (_root_.GlobalTheory.NMul.nmul_laws E d (up E μ) hL m n).2.2.1 i]
    unfold defect
    rw [subst_sub (hk n), subst_smul (hk n), hcomp, smul_sub, Nat.cast_mul, mul_smul]
    abel

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRamifiedFinite
section
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HCharRam

theorem ram_finite : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K),
    {w : HeightOneSpectrum (𝓞 K) | ¬ χ.UnrAt w}.Finite := by
  intro K _ _ χ
  exact Filter.eventually_cofinite.1 (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)

end GlobalTheory.HCharRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDotProductMulVecStarSwap
section
open Filter Topology

namespace GlobalTheory

theorem hermitian_dotProduct_mulVec_star_swap {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ H.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ H.mulVec (star y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hH.apply j i
  simp only [Complex.star_def, Complex.conj_conj] at h ⊢
  rw [h]
  ring

theorem pi_mul_hermitian_alternation {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) =
      (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
        ((x ⬝ᵥ H.mulVec (star y)).im : ℂ) := by
  rw [hermitian_dotProduct_mulVec_star_swap H hH x y]
  set a := x ⬝ᵥ H.mulVec (star y)
  have h := Complex.sub_conj a
  push_cast at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  linear_combination (-(Real.pi : ℂ)) * h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_strictHenselian_acyclic_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], SH A → AcycF R (sp B) F := by
  first | (exact @GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (exact GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral) | (intros; apply GlobalTheory.EtC.IntAcyc.acycF_of_isIntegral  <;> assumption)
end

