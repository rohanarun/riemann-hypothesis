module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinDivCycle
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinIntNum
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.CroftonFormulaFibreSum
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DifferentIdealEqTopOfUnramified
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitian
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial

open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem rootPolyNum : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous d := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h3
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ]
    exact Finsupp.hasFiniteSupport _
  have hcast : Fin.append x L ∘ Fin.castAdd q = x := by
    funext i
    simp [Fin.append_left]
  have hnat : Fin.append x L ∘ Fin.natAdd N = L := by
    funext j
    simp [Fin.append_right]
  have key : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
      (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) (Equiv.refl _) (Fin.append x L) rfl hH W]
    simp only [Equiv.coe_refl, rename_id_apply]
    rw [plainPolynomialPairNumber.classNum_mul_tail _ L _ hnat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [plainPairNumber.classNum_rename _ (Fin.castAdd_injective _ _), hcast]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [key, cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem main : ChernClassOnFlagPair.Statement :=
  ChernClassOnFlagPair.proof
    (JoinPointFlagModel.proof FlagPairCharacterisation.proof JoinPointModel.proof
      JoinPointVerticalDivisor.proof)
    (JoinPointNumbers.proof JoinPointIdeal.proof JoinDivCycle.proof JoinVariety.proof
      JoinIntNum.proof PairNumberJoinLeft.verticalComponentFibre)
    _root_.GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main _root_.GlobalTheory.CompanionTheory.Ar.RootIndep.main plainPolynomialPairNumber.proof rootPolyNum
    (PairNumberExpansionIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute) dividedDifferenceExpansion.proof

end GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  intro n e δ h W f hW hf hδ φ hφ hlev
  have hcnt : ∀ s : ℝ≥0∞, Measurable fun π : Fin (e + 1) → Fin n → ℂ =>
      cntOver (coneSet h W ∩ {y | s < φ y}) π (firstCoordVec (e + 1)) := fun s =>
    ModelDimension.FnCrofton.measurable_cntOver_first (isSigmaCompact_cone_inter h W (hlev s).1)
  obtain ⟨hm, hi⟩ := GlobalTheory.T.random_set_sum_expectation (planeMass n e • gaussM (e + 1) n)
    ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W))
    (fun π => fibrePts (coneSet h W) π) φ (gaussM (e + 1) n Set.univ) hφ
    (fun s => by
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      exact hcnt s)
    (fun s => by
      have hA := (hlev s).1
      have T := _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton n e δ h W f hW hf hδ {y | s < φ y} hA (hlev s).2
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      rw [lintegral_smul_measure, smul_eq_mul, Measure.restrict_apply hA.measurableSet, gaussM,
        lintegral_withDensity_eq_lintegral_mul _ (ModelDimension.FnCrofton.measurable_matrix_gaussian _ _) (hcnt s)]
      have hset : {y | s < φ y} ∩ coneBall h W =
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ {y | s < φ y}} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h3, h1, h2⟩
      rw [hset]
      simpa only [Pi.mul_apply, gaussM] using T)
  refine ⟨hm, ?_⟩
  rw [lintegral_smul_measure, smul_eq_mul] at hi
  exact hi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentTwistedGeneratorExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.RelDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq_field (H : Host E) : ((H.rt : E)) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at h
  exact h

theorem rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq_field H
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h1
  exact H.d_prime.ne_zero h1

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero] at hre him
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  rw [← map_pow, rt_sq_field, map_neg, map_natCast]
  simp

theorem exists_local_generator (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) :
    ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ],
      Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧
      Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  obtain ⟨δ₀, -, hδ₀, hconj, hlog⟩ := _root_.PositivityTheory.Xgf.exists_real_different_generator E H.unram ℓ
  have hrt : (H.rt : E) ≠ 0 := rt_ne_zero H
  have hδ₀E : (δ₀ : E) ≠ 0 := by exact_mod_cast hδ₀
  refine ⟨(δ₀ : E) / (H.rt : E), div_ne_zero hδ₀E hrt, fun j => ⟨?_, ?_⟩⟩
  · rw [map_div₀, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hδ₀E))
        (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hrt)), hlog]
  · rw [map_div₀, hconj, conj_rt H, div_neg, map_neg, norm_neg]

end GlobalTheory.CompanionTheory.Ar.Fl.RelDiff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDeterminantLogDifferent
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.GramDet

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix _root_.GlobalTheory _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem norm_coe_le_one {E : Type} [Field E] [NumberField E] {ℓ : Nat.Primes} (j : E →+* ℂ_[ℓ]) (b : 𝓞 E) :
    ‖j (b : E)‖ ≤ 1 :=
  ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral_int _
    (map_isIntegral_int j (RingOfIntegers.isIntegral_coe b))

theorem norm_natCast_eq_one {ℓ : Nat.Primes} {n : ℕ} (h : ¬ (ℓ : ℕ) ∣ n) : ‖(n : ℂ_[ℓ])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' (ℓ : ℕ) (n : ℚ_[ℓ])
  have h2 : ‖(n : ℚ_[ℓ])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd ℓ.2).2 h)
  rw [h2] at h1
  simpa using h1

theorem norm_det_le_one {E : Type} [Field E] [NumberField E] {ℓ : Nat.Primes} (j : E →+* ℂ_[ℓ])
    {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I E) (h : ∀ a b, ∃ t : 𝓞 E, M a b = t) :
    ‖j M.det‖ ≤ 1 := by
  rw [RingHom.map_det]
  have := _root_.GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric ℂ_[ℓ] I (j.mapMatrix M) 1 zero_le_one (fun a b => by
    obtain ⟨t, ht⟩ := h a b
    simpa [ht] using norm_coe_le_one j t)
  simpa using this

theorem exists_inverse {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    {I : Type} [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : ℕ) (hx : IsLocBasis (𝓞 E) ℓ x)
    (δ : 𝓞 E) (hδ0 : δ ≠ 0) (n₁ : ℕ)
    (hgen : ∀ a ∈ differentIdeal ℤ (𝓞 E), (n₁ : 𝓞 E) * a ∈ Ideal.span {δ}) :
    ∃ (C : Matrix I I E) (N : ℕ), (∀ a b, ∃ t : 𝓞 E, C a b = t) ∧
      ((δ : E) • gramE D x) * C = (N : E) • (1 : Matrix I I E) ∧ ∃ n₀ : ℕ, ¬ ℓ ∣ n₀ ∧ N = n₀ * n₀ * n₁ := by
  obtain ⟨hli, n₀, hn₀, hspan⟩ := hx
  obtain ⟨-, hadd1, hadd2, hsm1, hsm2, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum E H D
  obtain ⟨-, hdual⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.unimodularity_sesq E H D
  have hδE : (δ : E) ≠ 0 := by simpa using hδ0
  let S := Submodule.span (𝓞 E) (Set.range x)
  let b : Module.Basis I (𝓞 E) S := Module.Basis.span hli
  have hb : ∀ i, ((b i : S) : D.La) = x i := fun i => congrArg Subtype.val (Module.Basis.span_apply hli i)
  let g : D.La →ₗ[𝓞 E] S := LinearMap.codRestrict S ((n₀ : 𝓞 E) • LinearMap.id) (fun y => by
    simpa [Nat.cast_smul_eq_nsmul] using hspan y)
  have hg : ∀ y, ((g y : S) : D.La) = (n₀ : 𝓞 E) • y := fun y => by simp [g]
  let c : I → D.La →ₗ[𝓞 E] 𝓞 E := fun k => (b.coord k).comp g
  have hc : ∀ y, (n₀ : 𝓞 E) • y = ∑ m, c m y • x m := fun y => by
    calc (n₀ : 𝓞 E) • y = ((g y : S) : D.La) := (hg y).symm
      _ = ((∑ i, b.repr (g y) i • b i : S) : D.La) := by rw [b.sum_repr]
      _ = _ := by
        rw [AddSubmonoidClass.coe_finsetSum]
        exact Finset.sum_congr rfl fun m _ => by rw [Submodule.coe_smul, hb]; rfl
  have hcx : ∀ k a, c k (x a) = if a = k then (n₀ : 𝓞 E) else 0 := fun k a => by
    have : g (x a) = (n₀ : 𝓞 E) • b a := Subtype.ext (by simp [hg, hb])
    simp [c, this, Module.Basis.coord_apply, Finsupp.single_apply]
  let f : I → D.La →ₗ[𝓞 E] E := fun k =>
    (LinearMap.mulLeft (𝓞 E) ((n₁ : E) * (δ : E)⁻¹)).comp ((Algebra.linearMap (𝓞 E) E).comp (c k))
  have hf : ∀ k y, f k y = (n₁ : E) * (δ : E)⁻¹ * (c k y : E) := fun k y => rfl
  have hex : ∀ k, ∃ y, ∀ z, f k z = sesq D z y := fun k => by
    refine hdual (f k) fun δ' hδ' z => ?_
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hgen δ' hδ')
    refine ⟨t * c k z, ?_⟩
    have ht' : (t : E) * (δ : E) = (n₁ : E) * (δ' : E) := by
      have := congrArg (fun u : 𝓞 E => (u : E)) ht
      simpa using this
    rw [hf]
    push_cast
    field_simp
    linear_combination (-(c k z : E)) * ht'
  choose y hy using hex
  let sA : D.La → D.La →+ E := fun z => AddMonoidHom.mk' (fun w => sesq D z w) (hadd2 z)
  refine ⟨Matrix.of fun m k => ((H.bar (c m (y k)) : 𝓞 E) : E), n₀ * n₀ * n₁, fun a b' => ⟨_, rfl⟩, ?_,
    n₀, hn₀, rfl⟩
  ext a k
  have key : sesq D (x a) ((n₀ : 𝓞 E) • y k) =
      ∑ m, IsCMField.complexConj E ((c m (y k) : 𝓞 E) : E) * sesq D (x a) (x m) := by
    rw [hc (y k)]
    calc sesq D (x a) (∑ m, c m (y k) • x m) = sA (x a) (∑ m, c m (y k) • x m) := rfl
      _ = ∑ m, sA (x a) (c m (y k) • x m) := map_sum _ _ _
      _ = _ := Finset.sum_congr rfl fun m _ => hsm2 _ _ _
  have h2 : sesq D (x a) ((n₀ : 𝓞 E) • y k) = (n₀ : E) * f k (x a) := by
    rw [hsm2, hy]
    simp
  rw [h2] at key
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, gramE, smul_eq_mul, H.bar_eq, Matrix.one_apply]
  have h3 : ∑ m, (δ : E) * sesq D (x a) (x m) * IsCMField.complexConj E ((c m (y k) : 𝓞 E) : E)
      = (δ : E) * ((n₀ : E) * f k (x a)) := by
    rw [key, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [h3, hf, hcx]
  by_cases hak : a = k
  · simp [hak]; field_simp
  · simp [hak]

theorem log_norm_det_gramE : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x : I → D.La) (ℓ : Nat.Primes), IsLocBasis (𝓞 E) ℓ x → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x).det‖ = -(Fintype.card I : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
  intro E _ _ _ H D I _ _ x ℓ hx j
  obtain ⟨δ, hδ, hδ0, ⟨n₁, hn₁, hgen⟩, hnorm⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fl.ideal_local_generator E (differentIdeal ℤ (𝓞 E)) ℓ differentIdeal_ne_bot
  obtain ⟨C, N, hC, hmul, n₀, hn₀, rfl⟩ := exists_inverse H D x ℓ hx δ hδ0 n₁ hgen
  obtain ⟨-, -, -, -, -, -, hint⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum E H D
  have hM : ‖j ((δ : E) • gramE D x).det‖ ≤ 1 := norm_det_le_one j _ fun a b => by
    obtain ⟨t, ht⟩ := hint δ hδ (x a) (x b)
    exact ⟨t, by simpa [gramE] using ht⟩
  have hCn : ‖j C.det‖ ≤ 1 := norm_det_le_one j C hC
  have hprod : ‖j ((δ : E) • gramE D x).det‖ * ‖j C.det‖ = 1 := by
    have hN : Matrix.det (((n₀ * n₀ * n₁ : ℕ) : E) • (1 : Matrix I I E)) = ((n₀ * n₀ * n₁ : ℕ) : E) ^ Fintype.card I := by
      rw [Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    rw [← norm_mul, ← map_mul, ← Matrix.det_mul, hmul, hN, map_pow, norm_pow, map_natCast, Nat.cast_mul, Nat.cast_mul,
      norm_mul, norm_mul, norm_natCast_eq_one hn₀, norm_natCast_eq_one hn₁]
    simp
  have hu : ‖j ((δ : E) • gramE D x).det‖ = 1 := by
    refine le_antisymm hM ?_
    calc (1 : ℝ) = ‖j ((δ : E) • gramE D x).det‖ * ‖j C.det‖ := hprod.symm
      _ ≤ ‖j ((δ : E) • gramE D x).det‖ * 1 := by gcongr
      _ = _ := _root_.mul_one _
  rw [Matrix.det_smul, map_mul, norm_mul, map_pow, norm_pow] at hu
  have hj : ‖j (δ : E)‖ ≠ 0 := by
    simpa using hδ0
  have hd : ‖j (gramE D x).det‖ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hu
    exact zero_ne_one hu
  have hl := congrArg Real.log hu
  rw [Real.log_mul (pow_ne_zero _ hj) hd, Real.log_pow, Real.log_one] at hl
  rw [← hnorm j]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.GramDet
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifference
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_eq_pairNum_on_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
    w w' b b' f g hfp
  have hprime : (mcIdeal O x).IsPrime := hW.2.1.1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  haveI hprimeB : (pointIdeal O (joinCoord x z)).IsPrime := hm.2.1.1
  have hI := IntNumIsFieldIntersection.full (IsLocalRing.ResidueField O) (K ⊕ K') (Sum.elim ι ι')
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨φ, -, -, hd, hd', hf, hg⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB E'B ϖ hϖ
        hB'.multiProj).1 w w' b b' f g).mp hfp
    let F₀ : FlagModel O x d N E E' :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (FlagModel O x d N E E') := ⟨F₀⟩
    have hv : F₀.value O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O (joinCoord x z)) d
          (Fin.append b fun l => pullDeg (K' := K') (L l))
          (Fin.append b' fun l => pullDeg (K' := K') (L l))
          (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _)
        (Fin.append φ.deg' _) (Fin.append φ.f fun _ => rename (liftVar ι') (1 : MRing ι O))
        (Fin.append φ.g fun _ => rename (liftVar ι') (1 : MRing ι O)) _ = _
      rw [hd, hd', hf, hg, map_one]
      rfl
    unfold ck
    rw [dite_eq_left hne]
    refine (_root_.GlobalTheory.CompanionTheory.CommAlg.FlagModelValue.main O Ω K ι x d N V E E' hW hEE'
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => ChernClassOnFlagPair.isVertDiv_one hprime _ (sub_self _)) k Q hk2
      (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((plainPolynomialPairNumber.proof O (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d N b b' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q _ Q hQ).trans ?_)
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList (fun j => pullDeg (K' := K') (L j)) μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [ChernClassOnFlagPair.length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [PairNumberExpansionIndependence.proof _root_.GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute O ϖ hϖ (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d hB' N b b' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ (psumExpansion N k)
      (dividedDifferenceExpansion.proof N k _ (isHomogeneous_psum N k)) (isPairExpansion_psum N k)
      _ hlen]
  · have hsame : SameGeneric O x E E := fun s _ =>
      ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    obtain ⟨φ, -, -, hd, -, -, -⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB EB ϖ hϖ
        hB'.multiProj).1 w w b b _ _).mp (ChernClassOnFlagPair.isFlagPair_self hfp.flag)
    let F₀ : FlagModel O x d N E E :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := EB,
        pull := hp, pull' := hp, flag := φ }
    have hne : Nonempty (FlagModel O x d N E E) := ⟨F₀⟩
    unfold rootNum
    rw [dite_eq_left hne]
    refine (_root_.GlobalTheory.CompanionTheory.Ar.RootIndep.main O Ω K ι x d N V E E hW hsame
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI c G hsym hG hc q L Q hQ a
      ha).trans ?_
    have h6 := RootPolynomialNumber.proof O (K ⊕ K') (Sum.elim ι ι') (pointIdeal O (joinCoord x z)) d N b
      c G hG hc q (fun j => pullDeg (K' := K') (L j)) Q hQ a
    rw [← hd] at h6 ⊢
    exact h6

end GlobalTheory.CompanionTheory.Ar.Num
end

