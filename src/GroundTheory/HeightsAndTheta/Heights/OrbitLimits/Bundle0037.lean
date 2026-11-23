module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0046

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveCountLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

theorem CurveCountLower.proof (hD : CurveDegreeVert.Statement) (hV : CurveVertIndex.Statement)
    (hL : CurveIndexLinear.Statement) (hN : CurveBoxCount.Statement) : CurveCountLower.Statement := by
  intro K _ ι _ Ω _ y A II hII hP hB hS hC
  obtain ⟨c, hcX, hc⟩ := exists_chart hP
  obtain ⟨R, hRP, hRu, -⟩ := regularityPointsSum_holds.proof K ι _ hP
  set b : K → ℕ := fun k => (A.a k).natAbs with hb
  set d : K → ℕ := fun k => (A.a k + b k).toNat with hd'
  have hd : ∀ k, (d k : ℤ) = A.a k + b k := fun k =>
    Int.toNat_of_nonneg (by simp only [hb]; omega)
  have h1 := hD K ι _ A II c R b d hII hP hS hcX hRP hRu hd
  have h2 := hV K ι Ω y _ d hP (isMultiHomog_curveChartMono c d) (curveChartMono_notMem hc d)
  have h3 := hV K ι Ω y _ b hP (isMultiHomog_curveChartMono c b) (curveChartMono_notMem hc b)
  rw [aeval_curveChartMono] at h2 h3
  obtain ⟨hadd, hpow⟩ := hL K ι Ω y c hP hc
  have h4 := hadd A.a (fun k => (b k : ℤ))
  rw [show A.a + (fun k => (b k : ℤ)) = fun k => (d k : ℤ) from funext fun k => (hd k).symm] at h4
  have hI : II K ι (mCoordIdeal y) 1 (fun _ => A) =
      chartIndexLog y c A.a 1 + ∑ t ∈ R, Real.log (chartRadius A c t) := by
    have e2 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) =
        chartIndexLog y c (fun k => (d k : ℤ)) 1 := h2
    have e3 : vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) =
        chartIndexLog y c (fun k => (b k : ℤ)) 1 := h3
    rw [h1, e2, e3, h4]
    ring
  obtain ⟨C, hCC⟩ := hN K ι Ω y A c R hP hB hC hc hRP hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have h5 := hCC τ hτ
  rw [hpow A.a τ] at h5
  rw [hI]
  linarith [mul_add (τ : ℝ) (chartIndexLog y c A.a 1) (∑ t ∈ R, Real.log (chartRadius A c t))]

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveDegreeVert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveDegreeVert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def fsLine (b : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (b k : ℤ))

theorem isSmoothHerm_fsLine (b : K → ℕ) : IsSmoothHerm (fsLine b : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
  have hfun : (fsLine b : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι).h =
      fun z => ∏ k, Real.sqrt (∑ i : ι k, ‖z ⟨k, i⟩‖ ^ 2) ^ b k := by
    funext z
    simp only [fsLine, HermLine.ofMetrics, fsMetric, zpow_natCast, EuclideanSpace.norm_eq]
  unfold IsSmoothHerm
  rw [hfun]
  refine contDiffOn_prod fun k _ => (ContDiffOn.sqrt ?_ fun z hz => ?_).pow (b k)
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by funext p; simp⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), by funext p; simp [mul_assoc]⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem sum_eq_of_transversal {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by
  refine Finset.sum_bij (fun t ht => (hR'u t (hRP t ht)).exists.choose)
    (fun t ht => (hR'u t (hRP t ht)).exists.choose_spec.1) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have e1 := (hR'u t₁ (hRP t₁ h₁)).exists.choose_spec.2
    have e2 := (hR'u t₂ (hRP t₂ h₂)).exists.choose_spec.2
    rw [he] at e1
    exact (hRu t₂ (hRP t₂ h₂)).unique ⟨h₁, sameOrbit_trans e2 (sameOrbit_symm e1)⟩ ⟨h₂, sameOrbit_refl t₂⟩
  · intro t' ht'
    obtain ⟨t, ⟨htR, hto⟩, -⟩ := hRu t' (hR'P t' ht')
    exact ⟨t, htR, (hR'u t (hRP t htR)).unique (hR'u t (hRP t htR)).exists.choose_spec
      ⟨ht', sameOrbit_symm hto⟩⟩
  · intro t ht
    exact hh _ _ (hRP t ht) (hR'u t (hRP t ht)).exists.choose_spec.2

theorem logNorm_sameOrbit {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {s : MRing ι} {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    logNorm A s z = logNorm A s z' := by
  obtain ⟨c, hc, rfl⟩ := h
  unfold logNorm
  have hn : ∏ k, ‖c k‖ ^ A.a k = ‖∏ k, c k ^ a k‖ := by
    simp [ha, norm_prod, norm_pow]
  have h0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog s a hs c z', A.smul c z' hc, norm_mul, hn, mul_div_mul_left _ _ h0]

omit [∀ k, Fintype (ι k)] in
theorem norm_eval_curveChartMono (c : ∀ k, ι k) (e : K → ℕ) (z : (Σ k, ι k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (curveChartMono c e))‖ = ∏ k, ‖z ⟨k, c k⟩‖ ^ e k := by
  simp [curveChartMono, map_prod, norm_prod]

theorem proof : CurveDegreeVert.Statement := by
  intro K _ ι _ P A II c R b d hII hP hA hc hRP hRu hd
  have hI := hII K ι
  have hpr : P.IsPrime := hP.2.1.1
  have hL : ∀ j, IsSmoothHerm ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j) := fun j => j.elim0
  have hsnoc : ∀ C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
      (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) C : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = fun _ => C :=
    fun C => funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
  have hmono : ∀ e : K → ℕ, curveChartMono c e ∉ P := by
    intro e h
    rw [curveChartMono, hpr.prod_mem_iff] at h
    obtain ⟨k, _, hk⟩ := h
    exact hc k (hpr.mem_of_pow_mem _ hk)
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLine b with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_fsLine b
  have hBa : ∀ k, B.a k = b k := fun k => rfl
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    show A.a k + B.a k = d k
    rw [hBa, hd k]
  have hsd : IsSectionOn P (A.tensor B) (curveChartMono c d) :=
    ⟨d, hABa, isMultiHomog_curveChartMono c d, hmono d⟩
  have hsb : IsSectionOn P B (curveChartMono c b) := ⟨b, hBa, isMultiHomog_curveChartMono c b, hmono b⟩

  have hnz : ∀ z ∈ mcPts P, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k
    have hs1 : IsSectionOn P (fsLine (fun _ => 1) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c fun _ => 1) :=
      ⟨fun _ => 1, fun _ => rfl, isMultiHomog_curveChartMono c _, hmono _⟩
    have h1 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne arithVarZero hP hs1 hz)
    rw [norm_eval_curveChartMono] at h1
    have h2 := Finset.prod_ne_zero_iff.mp h1 k (Finset.mem_univ k)
    simpa using h2

  have hadd := hI.2.1 P 0 Fin.elim0 A B hP hL hA hB
  have hRd := hI.2.2 P 0 Fin.elim0 (A.tensor B) (curveChartMono c d) d hP hL
    (hA.mul hB) hABa (isMultiHomog_curveChartMono c d) (hmono d)
  have hRb := hI.2.2 P 0 Fin.elim0 B (curveChartMono c b) b hP hL hB hBa
    (isMultiHomog_curveChartMono c b) (hmono b)
  rw [hsnoc, hsnoc, hsnoc] at hadd
  rw [hsnoc] at hRd hRb
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsd] at hRd
  rw [recR_eq, cycR_eq_vertR_of_dimOne arithVarZero _ hP hsb] at hRb

  obtain ⟨R', hR'P, hR'u, hsum⟩ := regularityPointsSum_holds.proof K ι P hP
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hint : ∀ (C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (e : K → ℕ), (∀ k, C.a k = e k) → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s e →
      arInt P s C (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ∑ t ∈ R, logNorm C s t := by
    intro C s e hCe hse
    have hinv : ∀ z z', z ∈ mcPts P → SameOrbit z z' → logNorm C s z = logNorm C s z' :=
      fun z z' _ h => logNorm_sameOrbit hCe hse h
    rw [arInt, hφ, hsum _ hinv]
    exact (sum_eq_of_transversal hRP hRu hR'P hR'u _ hinv).symm
  rw [hint _ _ d hABa (isMultiHomog_curveChartMono c d)] at hRd
  rw [hint _ _ b hBa (isMultiHomog_curveChartMono c b)] at hRb

  have hpt : ∀ t ∈ R, logNorm B (curveChartMono c b) t - logNorm (A.tensor B) (curveChartMono c d) t =
      Real.log (chartRadius A c t) := by
    intro t ht
    have hz := hRP t ht
    have hk := hnz t hz
    have hApos := A.pos t hz.1
    have hBpos := B.pos t hz.1
    have hpos : ∀ e : K → ℕ, 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ e k := fun e =>
      Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hk k)) _
    have hsplit : ∏ k, ‖t ⟨k, c k⟩‖ ^ d k =
        (∏ k, ‖t ⟨k, c k⟩‖ ^ b k) * ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (norm_ne_zero_iff.mpr (hk k)), hd k, add_comm]
    unfold logNorm chartRadius
    rw [norm_eval_curveChartMono, norm_eval_curveChartMono, show (A.tensor B).h t = A.h t * B.h t from rfl,
      ← Real.log_div (div_pos (hpos b) hBpos).ne' (div_pos (hpos d) (mul_pos hApos hBpos)).ne', hsplit]
    congr 1
    have := hpos b
    have hq : 0 < ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hk k)) _
    field_simp
  rw [← Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
  linarith

end CurveDegreeVert

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveRingFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain

noncomputable section

namespace CurveRingFiniteAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_integer_of_mem_chartRingZ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (z : (Σ k, ι k) → F) (c : ∀ k, ι k)
    (hc : ∀ p : Σ k, ι k, v.valuation F (z p) ≤ v.valuation F (z ⟨p.1, c p.1⟩)) {b : F}
    (hb : b ∈ chartRingZ z c) : b ∈ (v.valuation F).integer := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    rw [Valuation.mem_integer_iff, map_div₀]
    rcases eq_or_ne (v.valuation F (z ⟨p.1, c p.1⟩)) 0 with h0 | h0
    · simp [h0]
    · exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hc p)
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x w _ _ hx hw => exact add_mem hx hw
  | mul x w _ _ hx hw => exact mul_mem hx hw


omit [Fintype K] in
theorem mem_integralClosure {F : Type} [Field F] [NumberField F] (z : (Σ k, ι k) → F) (c0 : ∀ k, ι k)
    (hc0 : ∀ k, z ⟨k, c0 k⟩ ≠ 0) {b : F}
    (hb : ∀ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) → b ∈ chartRingZ z c) :
    b ∈ integralClosure ℤ F := by
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F b ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F b hv
    rw [← hr]
    exact r.2
  intro v
  have hmax : ∀ k, ∃ i, ∀ j, v.valuation F (z ⟨k, j⟩) ≤ v.valuation F (z ⟨k, i⟩) := fun k => by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v.valuation F (z ⟨k, j⟩))
      ⟨c0 k, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hcz : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    have h1 := hc k (c0 k)
    rw [h0, map_zero] at h1
    exact hc0 k ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  exact mem_integer_of_mem_chartRingZ v z c (fun p => hc p.1 p.2) (hb c hcz)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem charZero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) ((injective_iff_map_eq_zero _).mpr fun m hm => ?_)
  have h : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, hm, C_0]
  rwa [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hy, Ideal.mem_bot] at h

end CurveRingFiniteAlt


open CurveRingFiniteAlt IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem CurveRingFinite.proof : CurveRingFinite.Statement := by
  intro K _ ι _ Ω _ y hy
  classical
  have := CurveRingFiniteAlt.charZero y hy.2.2.1
  choose c0 hc0 using hy.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h => hc0 k (X_mem_of_eq_zero h)
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c0 p.1⟩
  let κ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (Set.range r)
  have : FiniteDimensional ℚ κ := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨p, rfl⟩ := hx
    exact (isAlgebraic_ratio hy c0 hy0 p).isIntegral
  have : NumberField κ :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective
      to_finiteDimensional := inferInstance }
  let z : (Σ k, ι k) → κ := fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q := by
    rintro ⟨k, i⟩ ⟨k', j⟩ h
    simp only at h
    subst h
    exact div_div_div_cancel_right₀ (hy0 k) _ _
  have hyz : ∀ p, z p ≠ 0 → y p ≠ 0 := fun p h hp => h (Subtype.ext (by
    show y p / y ⟨p.1, c0 p.1⟩ = 0
    rw [hp, zero_div]))
  let φ : κ →ₐ[ℤ] Ω := (IntermediateField.val κ).toRingHom.toIntAlgHom
  have hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ := fun c => by
    rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext p
    exact (hzy p ⟨p.1, c p.1⟩ rfl).symm
  have hκ : ∀ b ∈ curveRing y, b ∈ κ := fun b hb => by
    have h := mem_curveRing.mp hb c0 hy0
    rw [hmap, Subalgebra.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    exact x.2
  have hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ := fun b hb => by
    refine mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_
    · have h1 := congrArg (fun x : κ => (x : Ω)) h
      have h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0 := h1
      exact one_ne_zero ((div_self (hy0 k)).symm.trans h2)
    · have h := mem_curveRing.mp hb c (fun k => hyz _ (hc k))
      rw [hmap, Subalgebra.mem_map] at h
      obtain ⟨x, hx, hxb⟩ := h
      have e : x = ⟨b, hκ b hb⟩ := Subtype.ext hxb
      exact e ▸ hx
  have : Module.Finite ℤ (integralClosure ℤ κ) := inferInstanceAs (Module.Finite ℤ (𝓞 κ))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ κ :=
    { toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h =>
    Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def segre (y : (Σ k, ι k) → Ω) : (Σ _ : Unit, ∀ k, ι k) → Ω :=
  fun q ↦ ∏ k, y ⟨k, q.2 k⟩

omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero_iff (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) :
    segre y ⟨(), f⟩ ≠ 0 ↔ ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  simp [segre, Finset.prod_ne_zero_iff]


omit [∀ k, Fintype (ι k)] in
theorem segre_ratio (y : (Σ k, ι k) → Ω) (f g : ∀ k, ι k) :
    segre y ⟨(), g⟩ / segre y ⟨(), f⟩ = ∏ k, y ⟨k, g k⟩ / y ⟨k, f k⟩ := by
  simp [segre, Finset.prod_div_distrib]


omit [∀ k, Fintype (ι k)] in
theorem prod_ratio_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0)
    (p : Σ k, ι k) :
    ∏ k, y ⟨k, Function.update f p.1 p.2 k⟩ / y ⟨k, f k⟩ = y p / y ⟨p.1, f p.1⟩ := by
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, div_self (hf k)]
  · simp


omit [∀ k, Fintype (ι k)] in
theorem chartRingZ_segre (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    chartRingZ (segre y) (fun _ ↦ f) = chartRingZ y f := by
  classical
  apply le_antisymm
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    change segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f
    rw [segre_ratio]
    exact prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    change y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)
    rw [← prod_ratio_update y f hf p, ← segre_ratio]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]
    rw [eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem exists_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∃ f : ∀ k, ι k, ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
  choose f hf using h
  exact ⟨f, hf⟩

theorem isAlgebraic_segre_ratio [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    IsAlgebraic ℚ (segre y ⟨(), g⟩ / segre y ⟨(), f⟩) := by
  rw [segre_ratio]
  refine (IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic
  exact (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral

theorem isArithVar_segre [DecidableEq K] [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : IsArithVar (mCoordIdeal (segre y)) 1 := by
  refine CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩
    (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_
  rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
  exact IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)

end SegreChart

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveBoxLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxLattice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar (mCoordIdeal y) 1 → Birational y → IsConjInvariantH A → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    (∀ t ∈ R, t ∈ mcPts (mCoordIdeal y)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      (τ : ℝ) * ∑ t ∈ R, Real.log (chartRadius A c t) + chartIndexLog y c A.a τ - C ≤
        Real.log (Nat.card {s : chartLat y A.a τ //
          ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ})

end GroundTheory.Heights₂.Heights.Targets
end

