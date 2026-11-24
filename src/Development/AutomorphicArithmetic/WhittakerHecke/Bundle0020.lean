module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.PlaceAe
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IdeleEmbeddingUniformizerOfSplitPlacePair
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H

private theorem e_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F)
    (x y : PlacesOver E v) (h : x ≠ y) : x.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  have hfin : Module.finrank F E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  rw [hfin] at hs
  have hpos : ∀ x : PlacesOver E v, 1 ≤ x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have h1 := Finset.sum_le_sum_of_subset (f := fun x : PlacesOver E v => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F))
    (Finset.subset_univ {x, y})
  rw [Finset.sum_pair h, hs] at h1
  have h2 := hpos x
  have h3 := hpos y
  exact Nat.eq_one_of_mul_eq_one_right (show x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) = 1 by omega)

private theorem map_sg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : P F) (w w' : P E)
    [hl : w.asIdeal.LiesOver v.asIdeal] [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) ∧
      ∀ a b, sg w a * sg w' b = 0 := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc₁, -, -, -, -, hs₁, -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc₂, -, -, -, -, hs₂, -, -⟩ := sgLaws E w'
  refine ⟨Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_), fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)⟩
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs₁ _).1, (hs₂ _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs₂ _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc₁ _).symm
    by_cases h' : u = w'
    · subst h'
      have hb : below F u = v := (below_eq_iff _ _).2 hl'
      subst hb
      rw [(hs₁ _).2 _ h, zero_add]
      exact (congrArg _ (hc x)).trans (hc₂ _).symm
    · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
      rw [(hs x).2 _ hb, map_zero, (hs₁ _).2 _ h, (hs₂ _).2 _ h', add_zero]
  · change (sg w a).1 * (sg w' b).1 = 0
    rw [(hs₁ _).1, zero_mul]
  · change (sg w a).2 u * (sg w' b).2 u = 0
    by_cases h : u = w
    · subst h
      rw [(hs₂ _).2 _ hne, mul_zero]
    · rw [(hs₁ _).2 _ h, zero_mul]

theorem UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∀ ϖ : (H.Kv v)ˣ, H.IsU ϖ → ∃ (ϖ₁ : (H.Kv w)ˣ) (ϖ₂ : (H.Kv w')ˣ), H.IsU ϖ₁ ∧ H.IsU ϖ₂ ∧
            ideleEmbedding ℚ E (H.idl v ϖ) = H.idl w ϖ₁ * H.idl w' ϖ₂ := by
  intro E _ _ D v w w' hne hw hw' _ _ hall ϖ hϖ
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hn : (⟨w, hl⟩ : PlacesOver E v) ≠ ⟨w', hl'⟩ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨-, -, -, hi, -, -, -, -, -, -⟩ := sgLaws ℚ v
  obtain ⟨-, -, -, hi₁, -, -, -, -, -, -⟩ := sgLaws E w
  obtain ⟨-, -, -, hi₂, -, -, -, -, -, -⟩ := sgLaws E w'
  refine ⟨Units.map (completionMap v w : Kv v →* Kv w) ϖ, Units.map (completionMap v w' : Kv v →* Kv w') ϖ, ?_, ?_, Units.ext ?_⟩
  · change Valued.v (completionMap v w (ϖ : Kv v)) = _
    rw [valued_completionMap, e_one D v _ _ hn, pow_one]
    exact hϖ
  · change Valued.v (completionMap v w' (ϖ : Kv v)) = _
    rw [valued_completionMap, e_one D v _ _ hn.symm, pow_one]
    exact hϖ
  · obtain ⟨h1, h2⟩ := map_sg v w w' hne (fun u hu => hall u (HeightOneSpectrum.ext hu.over.symm)) ((ϖ : Kv v) - 1)
    change adeleMap ℚ E ((idl v ϖ : (A ℚ)ˣ) : A ℚ) = _
    rw [Units.val_mul, hi, hi₁, hi₂, map_add (f := _), map_one, h1, map_sub, map_sub, map_one, map_one, add_mul, mul_add, mul_add, h2]
    simp only [one_mul, mul_one, add_zero, Units.coe_map, MonoidHom.coe_coe]
    abel
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralEvenPowerGaussianMulAbsRpow
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def gg (a : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (2 * a - 1) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ))

private theorem gg_int {a : ℂ} (ha : 0 < a.re) : IntegrableOn (gg a) (Set.Ioi 0) ∧
    ∫ r in Set.Ioi (0 : ℝ), gg a r = (Real.pi : ℂ) ^ (-a) * Complex.Gamma a / 2 := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * Complex.exp (-((Real.pi : ℝ) * t))
  have key : ∀ x ∈ Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • F (x ^ (2 : ℝ)) = 2 * gg a x := fun x hx => by
    have hx' : (0 : ℝ) < x := hx
    have h0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx'.ne'
    have h1 : ((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (a - 1) = (x : ℂ) ^ (2 * (a - 1)) := by
      rw [Real.rpow_two, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx'.le hx'.le, ← Complex.cpow_add _ _ h0]
      congr 1
      ring
    have h2 : (x : ℂ) ^ (2 * a - 1) = x * (x : ℂ) ^ (2 * (a - 1)) := by
      rw [show 2 * a - 1 = 1 + 2 * (a - 1) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
    simp only [F, gg, h1, h2, Complex.real_smul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two]
    push_cast
    ring_nf
  have hF : IntegrableOn F (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1)) 0 Real.pi_pos).2
      (by simpa using Complex.GammaIntegral_convergent ha)
    refine (h.const_mul ((Real.pi : ℂ) ^ (a - 1))⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : (Real.pi : ℂ) ^ (a - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
    simp only [F]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (le_of_lt ht)]
    push_cast
    field_simp
  have h1 := (integrableOn_Ioi_comp_rpow_iff F (p := 2) two_ne_zero).2 hF
  have h2 := integral_comp_rpow_Ioi F (p := 2) two_ne_zero
  refine ⟨?_, ?_⟩
  · refine ((h1.congr_fun key measurableSet_Ioi).const_mul (2 : ℂ)⁻¹).congr (ae_of_all _ fun x => ?_)
    simp
  · rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi ha Real.pi_pos] at h2
    rw [eq_div_iff two_ne_zero, mul_comm, h2, Complex.cpow_neg, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)]

theorem UpperTheory.integral_even_power_gaussian_mul_abs_rpow :
    ∀ (e : ℕ) (s : ℂ), 0 < s.re → Integrable (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) ∧ ∫ r : ℝ, (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) = (Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e) := by
  intro e s hs
  have ha : 0 < (s + e).re := by simp; positivity
  have hf : ∀ r : ℝ, r ≠ 0 → (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) =
      gg (s + e) |r| := fun r hr => by
    have h1 : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
    have h2 : (r : ℂ) ^ (2 * e) = ((|r| : ℝ) : ℂ) ^ ((2 * e : ℕ) : ℂ) := by
      rw [Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_pow, pow_mul, pow_mul, sq_abs]
    rw [h2, gg, mul_right_comm, ← Complex.cpow_add _ _ h1, sq_abs]
    congr 2
    push_cast
    ring
  have hae : (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) =ᵐ[volume]
      fun r => gg (s + e) |r| := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with r hr using hf r hr
  obtain ⟨hi, hv⟩ := gg_int ha
  have hp : IntegrableOn (fun r => gg (s + e) |r|) (Set.Ioi 0) :=
    hi.congr_fun (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  have hn : IntegrableOn (fun r => gg (s + e) |r|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  have hall : Integrable fun r => gg (s + e) |r| := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hn.union hp
  refine ⟨hall.congr hae.symm, ?_⟩
  have e1 : ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) r :=
    setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [abs_of_pos hr]
  have e2 : ∫ r in Set.Iic (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| := by
    rw [← neg_zero, ← integral_comp_neg_Iic]
    simp
  rw [integral_congr_ae hae, ← intervalIntegral.integral_Iic_add_Ioi hn hp, e2, e1, hv]
  ring
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnfoldedIntegrandEqZetaIntegral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem fub3 {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z) [SFinite μ] [SFinite ν] [SFinite κ]
    (f : X → Z → ℂ) (g : Y → Z → ℂ)
    (h : Integrable (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2) (μ.prod (ν.prod κ))) :
    ∫ q : X × Y × Z, f q.1 q.2.2 * g q.2.1 q.2.2 ∂(μ.prod (ν.prod κ)) =
      ∫ k, ∫ y, f y k * ∫ z, g z k ∂ν ∂μ ∂κ := by
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : (X × Y) × Z ≃ᵐ X × Y × Z)
      ((μ.prod ν).prod κ) (μ.prod (ν.prod κ)) := measurePreserving_prodAssoc μ ν κ
  have h2 := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h
  rw [← hp.integral_comp' (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2)]
  refine (integral_prod_symm _ h2).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  change ∫ x : X × Y, f x.1 k * g x.2 k ∂(μ.prod ν) = ∫ y, f y k * ∫ z, g z k ∂ν ∂μ
  rw [integral_prod_mul (fun y => f y k) (fun z => g z k), integral_mul_const]

theorem UpperTheory.integral_unfoldedIntegrand_eq_zetaIntegral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (M₀ : Meas ℚ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ),
        Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) →
        ∫ q, Un.Hh D χ φ Φ s q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) = Zu D M₀ χ φ Φ s := by
  intro E _ _ D χ φ M₀ Φ s h
  haveI := M₀.prob
  haveI : SFinite (ideleMeasure ℚ) := inferInstance
  exact fub3 (ideleMeasure ℚ) (ideleMeasure ℚ) M₀.κ
    (fun y k => Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1))
    (fun z k => (Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) h
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.IntegralUnipotentCoordinatesEqZeroOfCuspidal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical


open GroundTheory.Automorphic.FourierWhittaker in
private noncomputable def latE' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.integral_unipotentCoordinates_eq_zero_of_cuspidal :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f →
        (∀ g, ∫ b in fundamentalSet E, f (gl (nU b) * g) ∂(adeleMeasure E) = 0) →
        ∀ h, ∫ u in FS2 ℚ, f (nE D u * h) ∂(adeleMeasurePi ℚ) = 0 := by
  intro E _ _ D Φ hL h0 h
  have hl := hL.2
  let β : (Fin 2 → A ℚ) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi ℚ (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure ℚ).IsAddHaarMeasure
  haveI : ((adeleMeasurePi ℚ (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi ℚ)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) ((adeleMeasurePi ℚ (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := ℚ) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE' D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add (f := _)]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 ℚ) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE' D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  have h2 : ∫ x in fundamentalSet E, Φ (gl (nU x) * h) ∂(adeleMeasure E) = 0 := h0 h
  have hc := (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m)).ne'
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi ℚ (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  exact (smul_eq_zero.1 h2).resolve_left hc
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.KAtDiagIdeleOfNatMulRotationOfNotDvd
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_iy (v : H.P ℚ) (r : ℝ) : H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold iy
  split_ifs
  · simp
  · change pLoc ℚ v ((1 : Af ℚ) - 0 + 0) = 1
    rw [sub_zero, add_zero, map_one]

private theorem cp_pin (v : H.P ℚ) (n : ℕ) (h : ¬ normV v ∣ n) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold pin
  refine finprod_induction (fun x : (A ℚ)ˣ => H.cp v (x : A ℚ) = 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [Units.val_mul, map_mul, hx, hy, one_mul]
  · intro v'
    by_cases hv : v = v'
    · subst hv
      rw [Nat.factorization_eq_zero_of_not_dvd h]
      simp
    · have : H.cp v ((UpperTheory.ConvolutionTheory.RankTwoDescent.pv v' : (A ℚ)ˣ) : A ℚ) = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne hv _
      rw [Units.val_pow_eq_pow_val, map_pow, this, one_pow]

private theorem cp_rot (v : H.P ℚ) (t : ℝ) :
    Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrArg (fun y : GL (Fin 2) (Af ℚ) => pLoc ℚ v (y.val i j)) (TR.pFin_infGL (E := ℚ) (a := 2) _ :
    Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1)
  refine h.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem cp_aE (v : H.P ℚ) (a : (A ℚ)ˣ) (h : H.cp v (a : A ℚ) = 1) :
    Matrix.GeneralLinearGroup.map (H.cp v) (aE a) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change H.cp v ((aE a).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd :
    ∀ (E : Type) [Field E] [NumberField E] (v : H.P ℚ) (n : ℕ) (r t : ℝ), 0 < n → ¬ normV v ∣ n → ∀ w : H.P E, w.under (𝓞 ℚ) = v →
          H.KAt w (em E (aE (iy r * pin n) * rot t)) := by
  intro E _ _ v n r t _ h w hw
  have hx : Matrix.GeneralLinearGroup.map (H.cp v) (aE (iy r * pin n) * rot t) = 1 := by
    rw [map_mul, cp_rot, cp_aE v _ (by rw [Units.val_mul, map_mul, cp_iy, cp_pin v n h, one_mul]), one_mul]
  generalize aE (iy r * pin n) * rot t = x at hx
  subst hw
  have : Matrix.GeneralLinearGroup.map (H.cp w) (em E x) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have e : H.cp (w.under (𝓞 ℚ)) (x.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j :=
      congrArg (fun y : GL (Fin 2) _ => y.val i j) hx
    change GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w (H.cp (w.under (𝓞 ℚ)) (x.val i j)) = (1 : Matrix (Fin 2) (Fin 2) _) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
    · exact map_zero (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
  unfold H.KAt
  rw [this]
  exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesRightInvarianceFiniteAdelic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_right_invariance_finite_adelic :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : GL (Fin 2) (A ℚ)), (∀ i j, (k.val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).1) → ∀ (f : Sm E 2) (X : Lie E 2), (∀ g, f.1 (g * em E k) = f.1 g) → ∀ g, (lie E 2 X f).1 (g * em E k) = (lie E 2 X f).1 g := by
  intro E _ _ _ k hk f X hf g
  have hfst : ∀ i j, ((em E k).val i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j).1 := by
    intro i j
    have e : (em E k).val i j = AdeleBaseChange.adeleMap ℚ E (k.val i j) := rfl
    have e1 : (1 : Matrix (Fin 2) (Fin 2) (A E)) i j =
        AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
      by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [e, e1, AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, hk i j]
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) = 1 := by
    have h2 : Matrix.GeneralLinearGroup.map (pInf E) (em E k) =
        Matrix.GeneralLinearGroup.map (pInf E) (1 : GL (Fin 2) (A E)) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      exact congrArg (fun x => (infEq E).symm x) (hfst i j)
    rw [h2, map_one]
  have hm : finGL E 2 (Matrix.GeneralLinearGroup.map (pFin E) (em E k)) = em E k := by
    have h3 := infGL_mul_finGL (em E k)
    rwa [h1, map_one, one_mul] at h3
  have hr : GlobalTheory.CuspRep.rt E 2 (em E k) f = f := Subtype.ext (funext hf)
  have h4 := LinearMap.congr_fun (lie_rt_fin X (Matrix.GeneralLinearGroup.map (pFin E) (em E k))) f
  rw [hm, Module.End.mul_apply, Module.End.mul_apply, hr] at h4
  exact (congrArg (fun φ : Sm E 2 => φ.1 g) h4).symm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesSatakeEigenAtPlace
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_satake_eigen_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (B : Multiset ℂˣ) (f : Sm E 2) (X : Lie E 2), UpperTheory.V.Af.Smo.EigAt w B f.1 → UpperTheory.V.Af.Smo.EigAt w B (lie E 2 X f).1 := by
  intro E _ _ _ w B f X hf g
  have hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2),
      (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x := by
    intro k φ x
    have h := LinearMap.congr_fun (lie_rt_fin X k) φ
    exact (congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm
  have hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k) :=
    fun _ _ _ => rfl
  refine ⟨(hf 1).card, ?_, ?_⟩
  · intro y k hk
    have hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f := by
      refine Subtype.ext (funext fun x => ?_)
      have h := (hf x).inv 1 k hk
      simp only [one_mul, map_one, mul_one] at h
      rw [hev]
      exact h
    have e1 : g * finGL E 2 (locGL E 2 w (y * k)) =
        g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k) := by
      simp only [map_mul, mul_assoc]
    show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))
    rw [e1, hc, hfix]
  · intro ϖ hϖ j hj x
    have hfin := (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1
    have hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c =
          ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c := by
      intro W
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hc' (by simp [h0])
    have key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out •
          GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f := by
      refine Subtype.ext (funext fun z => ?_)
      have h := (hf z).eig ϖ hϖ j hj 1
      simp only [one_mul, map_one, mul_one] at h
      rw [hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))] at h
      simpa [Submodule.coe_sum, Finset.sum_apply, hev] using h
    have h2 := congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, ← mul_assoc, hc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.MeasurableWhittakerIdeleDiagTorusMul
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem cont_aE {K : Type} [Field K] [NumberField K] : Continuous (aE : (A K)ˣ → GL (Fin 2) (A K)) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_val, continuous_const, continuous_const, continuous_const]
  · fin_cases i <;> fin_cases j
    exacts [Units.continuous_coe_inv, continuous_const, continuous_const, continuous_const]

theorem UpperTheory.measurable_whittaker_idele_diagTorus_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ →
        Measurable (fun p : IdeleGroup ℚ × G1 ℚ => Wo D φ (em E (aE p.1 * gl p.2))) := by
  intro E _ _ D ω φ h
  have hem : Continuous (em E) := Continuous.units_map _
    (continuous_matrix fun i j => AdeleBaseChange.continuous_adeleMap.comp (continuous_id.matrix_elem i j))
  have h1 : Continuous fun p : IdeleGroup ℚ × G1 ℚ => em E (aE p.1 * gl p.2) :=
    hem.comp ((cont_aE.comp continuous_fst).mul (M.continuous_gl.comp continuous_snd))
  have hn : Continuous (nE D) :=
    M.continuous_gl.comp (M.continuous_nU.comp
      ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
        ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have h2 : Continuous fun q : (IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ) => φ (nE D q.2 * em E (aE q.1.1 * gl q.1.2)) * ψ (q.2 1) :=
    (h.cont.comp ((hn.comp continuous_snd).mul (h1.comp continuous_fst))).mul
      (hψ.comp ((continuous_apply 1).comp continuous_snd))
  have : BorelSpace ((IdeleGroup ℚ × G1 ℚ) × (Fin 2 → A ℚ)) := inferInstance
  exact (h2.measurable.stronglyMeasurable.integral_prod_right' (ν := (adeleMeasurePi ℚ).restrict (FS2 ℚ))).measurable
end

