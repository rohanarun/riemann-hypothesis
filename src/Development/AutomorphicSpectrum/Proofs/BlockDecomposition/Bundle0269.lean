module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0133
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeLocalizationCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerAnnihilatesSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem cst_thick_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {r : R}
    (hr : r ∈ I ^ (e + 1)) : AbLaw.cst (p ≫ thick R I e) V r = 0 := by
  have key : AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V =
      (AbLaw.cst p V).comp (Ideal.Quotient.mk (I ^ (e + 1))) := by
    ext a
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [this]
  have h0 : AbLaw.cst (p ≫ thick R I e) V r =
      AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V r := rfl
  rw [h0, key, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

theorem pow_smul_top_secOnR (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left)
    (V : (Y e).left.Opens) :
    I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr s _
  rw [Submodule.mem_bot, SecOnR.smul_def, cst_thick_eq_zero I e (Y e).hom V hr, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableAbsFibreSumOfIsCxVar
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxAbs

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter _root_.Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (absLogNorm)

theorem absFibreSum_eq_sum_components_ae {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → HermLine ι} {A : HermLine ι}
    {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) (logNorm A s) y w| =
      ∑ᶠ Q ∈ (cxIdeal P).minimalPrimes, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w| := by
  classical
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hmeet := GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentsMeetNull.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDimLt.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.ChartRatioImageNull.proof K ι P e Ψ hfin.toFinset hP hΨ
    (fun W hW => hfin.mem_toFinset.1 hW)
  filter_upwards [compl_mem_ae_iff.mpr hmeet, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hone : ∀ Q ∈ (cxIdeal P).minimalPrimes, ∀ Q' ∈ (cxIdeal P).minimalPrimes, ∀ z, z ∈ conePts Q →
      z ∈ conePts Q' → Ψ (segre z) = Fin.cons 1 y → Q' = Q := by
    intro Q hQ Q' hQ' z hz hz' hΨz
    by_contra hne
    refine hyN ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hΨz, Q, hfin.mem_toFinset.2 hQ, Q',
      hfin.mem_toFinset.2 hQ', fun h => hne h.symm, ?_, ?_⟩
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf
    · intro f hf
      simpa [MvPolynomial.coe_aeval_eq_eval] using hz'.2 f hf
  have hunion : fibre P Ψ y = ⋃ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y := by
    ext w
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨z, hz, hzw, hΨw⟩
      obtain ⟨Q, hQ, hzQ⟩ := exists_minimal_of_mem_mcPts hz
      exact ⟨Q, hQ, z, hzQ, hzw, hΨw⟩
    · rintro ⟨Q, hQ, z, hz, hzw, hΨw⟩
      exact ⟨z, conePts_subset_mcPts_of_minimal hQ hz, hzw, hΨw⟩
  have hsub : ∀ Q ∈ (cxIdeal P).minimalPrimes, setFibre (conePts Q) Ψ y ⊆ fibre P Ψ y := by
    intro Q hQ w hw
    rw [hunion]
    exact Set.mem_biUnion hQ hw
  have hdisj : ((cxIdeal P).minimalPrimes).PairwiseDisjoint fun Q => setFibre (conePts Q) Ψ y := by
    intro Q hQ Q' hQ' hne
    refine Set.disjoint_left.2 ?_
    rintro w ⟨z, hz, hzw, hΨw⟩ ⟨z', hz', hzw', -⟩
    have hzQ' : z ∈ conePts Q' := mem_conePts_of_segre_eq hP hQ' hz' hz.1 (hzw'.trans hzw.symm)
    exact hne (hone Q hQ Q' hQ' z hz hzQ' (by rw [hzw]; exact hΨw)).symm
  rw [hunion, finsum_mem_biUnion hdisj hfin
    (fun Q hQ => (fibreFinite K ι P e Ψ hP hΨ y).subset (hsub Q hQ))]
  refine finsum_mem_congr rfl fun Q hQ => finsum_mem_congr rfl fun w hw => ?_
  refine congrArg abs ?_
  have hiff : (∃ γ, IsSheet P Ψ y w γ) ↔ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ :=
    ⟨fun ⟨γ, h⟩ => ⟨γ, isSetSheet_of_isSheet hP hQ (hone Q hQ) hw h⟩,
      fun ⟨γ, h⟩ => ⟨γ, isSheet_of_isSetSheet hQ h⟩⟩
  rw [sheetDensity_eq_setSheetDensity]
  unfold setSheetDensity
  by_cases hex : ∃ γ, IsSheet P Ψ y w γ
  · have hexQ := hiff.1 hex
    have hexP : ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_left hexP, dite_eq_left hexQ]
    exact hind w _ _ hexP.choose_spec (isSheet_of_isSetSheet hQ hexQ.choose_spec)
  · have hexQ : ¬ ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := fun h => hex (hiff.2 h)
    have hexP : ¬ ∃ γ, IsSetSheet (mcPts P) Ψ y w γ := hex
    rw [dite_eq_right hexP, dite_eq_right hexQ]

theorem abs_setSheetDensity_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} (hS : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (A : HermLine ι) (s : MRingOver ℂ ι) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    |setSheetDensity S Ψ φ (logNormC A s) y w| =
      max (setSheetDensity S Ψ φ (absLogNorm A s) y w) 0 +
        max (setSheetDensity S Ψ φ (fun z => -absLogNorm A s z) y w) 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · have hz := hS _ hγ.choose_spec.2.self_of_nhds.2.1
    have ha : absLogNorm A s (hγ.choose y) = |logNormC A s (hγ.choose y)| := by
      simp only [absLogNorm, if_pos hz]
    beta_reduce
    rw [ha, abs_mul]
    generalize maDensity (fun j y' => φ j (hγ.choose y')) y = m
    generalize logNormC A s (hγ.choose y) = g
    have hg := abs_nonneg g
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, max_eq_left (mul_nonneg hg hm),
        max_eq_right (by nlinarith : -|g| * m ≤ 0), add_zero]
    · rw [abs_of_nonpos hm, max_eq_right (by nlinarith : |g| * m ≤ 0),
        max_eq_left (by nlinarith : 0 ≤ -|g| * m), zero_add]
      ring
  · simp

theorem integrable_absFibreSum_of_isCxVar {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k) (hs : IsMultiHomog s a) (hsQ : s ∉ Q) :
    Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) := by
  classical
  have hS : ∀ z ∈ conePts Q, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz => hz.1
  have hfin := GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ hQ hΨ
  have hm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.measurable_absLogNorm A hA s
  have hdeg := fun (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) =>
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.absLogNorm_blockScale A hAa hs hc z
  have h1 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm hdeg
  have h2 := GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable_of_finite hS hfin hL hm.neg
    (g := fun z => -absLogNorm A s z) (fun c z hc => by simp only [hdeg c z hc])
  have heq : (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) =
      fun y => cxPosDens (conePts Q) Ψ (pot L) (absLogNorm A s) y +
        cxPosDens (conePts Q) Ψ (pot L) (fun z => -absLogNorm A s z) y := by
    funext y
    unfold cxPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y), finsum_mem_eq_finite_toFinset_sum _ (hfin y),
      finsum_mem_eq_finite_toFinset_sum _ (hfin y), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => abs_setSheetDensity_eq hS Ψ (pot L) A s y w
  refine ⟨?_, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => abs_nonneg _)).2
    (_root_.GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top K ι Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ)⟩
  rw [heq]
  exact (h1.add h2).aestronglyMeasurable

theorem ptsAbsIntegrable : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hae := absFibreSum_eq_sum_components_ae hP hΨ hL hA hs
  obtain ⟨a, hAa, hsa, hsP⟩ := hs
  have hfin : (cxIdeal P).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hsa' : IsMultiHomog (map (Int.castRingHom ℂ) s : MRingOver ℂ ι) a := fun m hm k =>
    hsa m (support_map_subset _ _ hm) k
  have hcomp : ∀ Q ∈ (cxIdeal P).minimalPrimes, Integrable (fun y => ∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A (map (Int.castRingHom ℂ) s)) y w|) := by
    intro Q hQ
    obtain ⟨hQv, hc⟩ := isCxVar_of_mem_minimalPrimes_cxIdeal K ι P e hP Q hQ
    refine integrable_absFibreSum_of_isCxVar hQv
      (fun z hz => hΨ z (conePts_subset_mcPts_of_minimal hQ hz)) hL hA hAa hsa' fun hmem => hsP ?_
    rw [← hc]
    exact hmem
  refine (integrable_finsetSum hfin.toFinset fun Q hQ => hcomp Q (hfin.mem_toFinset.1 hQ)).congr ?_
  filter_upwards [hae] with y hy
  rw [hy]
  exact (finsum_mem_eq_finite_toFinset_sum _ hfin).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxAbs
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfEquiv
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHyp

theorem isAdicComplete_of_equiv {Q R : Type*} [CommRing Q] [CommRing R] (e : Q ≃+* R) (a : Q)
    (h : IsAdicComplete (Ideal.span {e a}) R) : IsAdicComplete (Ideal.span {a}) Q := by
  have hmem : ∀ (n : ℕ) (x y : Q),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule Q Q)] ↔
        e x ≡ e y [SMOD (Ideal.span {e a} ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, smul_eq_mul, smul_eq_mul, Ideal.mul_top, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, ← map_pow, ← map_sub]
    exact (map_dvd_iff e).symm
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e x = 0 := by
      refine h.toIsHausdorff.haus' (e x) fun n => ?_
      have := (hmem n x 0).1 (hx n)
      rwa [map_zero] at this
    exact (map_eq_zero_iff e e.injective).1 h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e (f n))
      (fun {m n} hmn => (hmem m _ _).1 (hf hmn))
    refine ⟨e.symm L, fun n => (hmem n _ _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact hL n

variable (l : ℕ) [Fact l.Prime]

def eQ : (Ainf l ⧸ Ideal.span {xi0 l}) ≃+* OC l :=
  (Ideal.quotEquivOfEq (ker_theta0 (l := l)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l))

theorem eQ_natCast (n : ℕ) : eQ l (n : Ainf l ⧸ Ideal.span {xi0 l}) = (n : OC l) := map_natCast _ n

theorem norm_l_lt_one : ‖((l : OC l) : ℂ_[l])‖ < 1 :=
  IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l

theorem l_ne_zero : (l : OC l) ≠ 0 := by
  intro h
  have h1 : ((l : OC l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [h] at h1
  exact (Nat.cast_ne_zero (R := ℂ_[l])).2 (Fact.out : l.Prime).ne_zero (by simpa using h1.symm)

theorem dvd_pow_l {x : OC l} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : OC l) ^ n := by
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxp : 0 < ‖(x : ℂ_[l])‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hxp (norm_l_lt_one l)
  refine ⟨n, ⟨((l : OC l) : ℂ_[l]) ^ n / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hn.le hxp.le
  · simp [mul_div_cancel₀ _ hx0]

theorem dvd_total_OC (x y : OC l) : x ∣ y ∨ y ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inr (dvd_zero y)
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  rcases le_total ‖(y : ℂ_[l])‖ ‖(x : ℂ_[l])‖ with h | h
  · refine Or.inl ⟨⟨(y : ℂ_[l]) / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hx0]
  · have hy : y ≠ 0 := by
      rintro rfl
      exact hx0 (norm_eq_zero.1 (le_antisymm (by simpa using h) (norm_nonneg _)))
    have hy0 : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    refine Or.inr ⟨⟨(x : ℂ_[l]) / y, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hy0]

theorem unit_ainf (n : ℕ) (hn : n ≠ 0) : ∃ (k : ℕ) (u : Ainf l), (n : Ainf l) * u = (l : Ainf l) ^ k := by
  have h0 : (n : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  refine ⟨(n : ℤ_[l]).valuation, IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l
    (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]), ?_⟩
  have h1 : (n : ℤ_[l]) * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ (n : ℤ_[l]).valuation := by
    have e2 := congrArg (· * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) (PadicInt.unitCoeff_spec h0)
    refine e2.trans ?_
    change ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]) * _ * _ = _
    rw [mul_comm ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]), mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) h1
  simpa only [map_mul, map_pow, map_natCast] using h2

abbrev xiB : BdRp l := wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)

theorem span_xiB : Ideal.span {xiB l} = Ideal.span {tBdR l} := by
  rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
  exact maximalIdeal_eq_span_tBdR

theorem xi_dvd_fontaine_t : xiB l ∣ tBdR l :=
  Ideal.mem_span_singleton.1 ((span_xiB l).symm ▸ Ideal.mem_span_singleton_self _)

theorem t_dvd_xiB : tBdR l ∣ xiB l :=
  Ideal.mem_span_singleton.1 ((span_xiB l) ▸ Ideal.mem_span_singleton_self _)

theorem xiB_ne_zero : xiB l ≠ 0 :=
  (IsPerfectoidField.irreducible_wittToBDeRhamPlus (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))).ne_zero

theorem nil_k (k : ℕ) : fk l k (xi0 l) ^ k = 0 := by
  change Ideal.Quotient.mk _ (xiB l) ^ k = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (t_dvd_xiB l) k))

theorem dvd_of_witt_mem {a : Ainf l} (h : xiB l ∣ wittToBDeRhamPlus (normInteger ℂ_[l]) l a) : xi0 l ∣ a := by
  have h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
    exact Ideal.mem_span_singleton.2 h
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l), RingHom.mem_ker,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h1
  have h2 : a ∈ RingHom.ker (theta0 l) := Subtype.ext h1
  rw [ker_theta0] at h2
  exact Ideal.mem_span_singleton.1 h2

theorem gr_k (k i : ℕ) (hi : i < k) (a : Ainf l) (b : Bk l k)
    (h : fk l k a * fk l k (xi0 l) ^ i = fk l k (xi0 l) ^ (i + 1) * b) : xi0 l ∣ a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply dvd_of_witt_mem
  set w := wittToBDeRhamPlus (normInteger ℂ_[l]) l a with hw
  have h1 : Ideal.Quotient.mk (Ideal.span {tBdR l ^ k}) (w * xiB l ^ i) =
      Ideal.Quotient.mk _ (xiB l ^ (i + 1) * b) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  have h3 : xiB l ^ (i + 1) ∣ tBdR l ^ k :=
    (pow_dvd_pow _ hi).trans (pow_dvd_pow_of_dvd (xi_dvd_fontaine_t l) k)
  have h4 : xiB l ^ (i + 1) ∣ w * xiB l ^ i := by
    obtain ⟨c, hc⟩ := h3.trans h2
    exact ⟨c + b, by linear_combination hc⟩
  rw [pow_succ', mul_comm w, mul_comm (xiB l)] at h4
  exact (mul_dvd_mul_iff_left (pow_ne_zero i (xiB_ne_zero l))).1 h4

theorem hyp_k (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) : Lat.Hyp (Lat.fk l k) (xi0 l) l k := by
  have hl : eQ l (l : Ainf l ⧸ Ideal.span {xi0 l}) = (l : OC l) := eQ_natCast l l
  refine
    { one_le := hk
      nil := nil_k l k
      gr := fun i hi a b h => gr_k l k i hi a b h
      dom := (eQ l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := fun h => ?_
      cpl := ?_
      unit := unit_ainf l }
  · rcases dvd_total_OC l (eQ l x) (eQ l y) with h | h
    · exact Or.inl ((map_dvd_iff (eQ l)).1 h)
    · exact Or.inr ((map_dvd_iff (eQ l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_l l (x := eQ l x) ((map_ne_zero_iff _ (eQ l).injective).2 hx)
    refine ⟨n, (map_dvd_iff (eQ l)).1 ?_⟩
    rwa [map_pow, hl]
  · apply l_ne_zero l
    rw [← hl, h, map_zero]
  · refine isAdicComplete_of_equiv (eQ l) _ ?_
    rw [hl]
    exact IsPerfectoidField.isAdicComplete (K := ℂ_[l]) l

end GlobalTheory.CompanionTheory.LatCHyp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.PbKer

theorem isPullback_of_ker_eq_sup {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)]
    (h : f ≫ a = g ≫ b)
    (hk : Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b) :
    IsPullback f g a b := by
  have hle : ∀ {W : Scheme.{0}} (u : W ⟶ A) (v : W ⟶ B), u ≫ a = v ≫ b →
      Scheme.Hom.ker (f ≫ a) ≤ Scheme.Hom.ker (u ≫ a) := by
    intro W u v huv
    rw [hk]
    refine sup_le (Scheme.Hom.le_ker_comp u a) ?_
    rw [huv]
    exact Scheme.Hom.le_ker_comp v b
  refine IsPullback.of_isLimit' ⟨h⟩ ?_
  refine PullbackCone.IsLimit.mk h
    (fun s => IsClosedImmersion.lift (f ≫ a) (s.fst ≫ a) (hle s.fst s.snd s.condition)) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono a, Category.assoc]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono b, Category.assoc, ← h, ← s.condition]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s m hm1 _
    rw [← cancel_mono (f ≫ a), IsClosedImmersion.lift_fac, ← Category.assoc, hm1]

end GlobalTheory.CompanionTheory.GE.PbKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModule
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem fPow_torsion_of_chartIn : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  intro X J Z ψ hψ V hV _ I R _ _ _ M _ _ _ _ _ hIR hJM f hiso y hy
  by_contra hne
  push_neg at hne
  let A : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M y)
  have hA : ∀ a : R, a ∈ A ↔ a • y = 0 := fun a => by
    simp [A, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint (A : Set R) (Submonoid.powers (algebraMap Γ(X, V) R f) : Set R) := by
    refine Set.disjoint_left.2 fun x hxA hxS => ?_
    obtain ⟨k, rfl⟩ := hxS
    apply hne k
    have h1 := (hA _).1 hxA
    simp only at h1
    rwa [← map_pow, algebraMap_smul] at h1
  obtain ⟨p, hp, hAp, hpS⟩ := Ideal.exists_le_prime_disjoint A _ hdisj
  have hfp : algebraMap Γ(X, V) R f ∉ p := fun h =>
    Set.disjoint_left.1 hpS h (Submonoid.mem_powers _)
  have hJp : (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => hAp ((hA _).2 ?_)
    rw [algebraMap_smul]
    exact hJM a ha y
  obtain ⟨U, hU, h, Q₀, Q₁, hQ₀, hQ₁, hle, hQ₀p, hQ₁m⟩ := GlobalTheory.T.proper_birational_prime_exists J ψ hψ V hV f hiso p hp hJp hfp
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  haveI : IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := GlobalTheory.T.tensor_noetherian_affine_open J ψ hψ V hV U hU h R
  have hy' : ∀ n : ℕ, y ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range
      ((I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M).subtype.rTensor Γ(Z, U)) := fun n => hy n U hU h
  have hIQ : I.map (algebraMap Γ(X, V) R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) :=
    hIR.trans (sInf_le ⟨bot_le, hQ₁m⟩)
  obtain ⟨w, hw, hwy⟩ := GlobalTheory.T.tensor_prime_over_ideal_completion I y hy' Q₁ hQ₁ hIQ
  have hw0 : w ∉ Q₀ := fun h' => hw (hle h')
  have hfq : f ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : Γ(Z, U) →ₐ[Γ(X, V)] R ⊗[Γ(X, V)] Γ(Z, U))).comap
      (algebraMap Γ(X, V) Γ(Z, U)) := by
    intro hf
    apply hfp
    rw [← hQ₀p]
    simp only [Ideal.mem_comap] at hf ⊢
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply] at hf
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using hf
  obtain ⟨hloc1, hloc2⟩ := GlobalTheory.T.proper_birational_prime_criterion J ψ V hV f hiso U hU h _ (Ideal.comap_isPrime _ _) hfq
  obtain ⟨u, hu, huy⟩ := _root_.GlobalTheory.CompanionTheory.KrullLocal.smul_eq_zero_of_smul_one_tmul_eq_zero (J.ideal ⟨V, hV⟩) hJM Q₀ hQ₀ hloc1 hloc2 y w hw0 hwy
  rw [hQ₀p] at hu
  exact hu (hAp ((hA u).2 huy))

end GlobalTheory.CompanionTheory.GE.Krull
end

