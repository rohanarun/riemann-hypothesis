module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeClosedPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial Vertical Vertical.NormFormIrreducible

theorem aeval_smul_of_isHomogeneous {F K : Type*} [Field F] [Field K] [Algebra F K] {n d : ℕ}
    {g : MvPolynomial (Fin n) F} (hg : g.IsHomogeneous d) (c : K) (y : Fin n → K) :
    aeval (fun j => c * y j) g = c ^ d * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have := hg (mem_support_iff.mp hm)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  rw [aeval_monomial, aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem ChowDegreeClosedPoint.proof (hField : ClosedPointChartField.Statement)
    (hCone : ClosedPointConeCoord.Statement) : ChowDegreeClosedPoint.Statement := by
  classical
  intro F _ _ n I i hI hdim hXi
  obtain ⟨hfield, hfin⟩ := hField F n I i hI hdim hXi
  set J : Ideal (MvPolynomial (Fin n) F) := I ⊔ Ideal.span {X i - 1} with hJ
  let _ : Field (MvPolynomial (Fin n) F ⧸ J) := hfield.toField
  let L := MvPolynomial (Fin n) F ⧸ J
  have _ : FiniteDimensional F L := hfin
  have _ : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.of_finite F L
  let K := AlgebraicClosure F
  let ξ : Fin n → L := fun j => Ideal.Quotient.mk J (X j)
  have hξ : ∀ g : MvPolynomial (Fin n) F, aeval ξ g = Ideal.Quotient.mk J g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp; rfl
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X]
  have hξi : ξ i = 1 := by
    have : X i - 1 ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  set t : Fin n → F := Pi.single i 1 with ht_def
  have ht : ∑ j, algebraMap F L (t j) * ξ j = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [ht_def, hj])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [ht_def, hξi]
  have hgen : Algebra.adjoin F (Set.range ξ) = ⊤ := by
    have hr : Set.range ξ = Ideal.Quotient.mkₐ F J '' Set.range X := by
      rw [← Set.range_comp]; rfl
    rw [hr, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective F J

  obtain ⟨f, hf⟩ := chowFormExists F n 1 I hI hdim
  have hhom : IsMultiHomog (chowDegree I 1) f := chowFormHomog F n 1 I f hf
  have hfH : f.IsHomogeneous (chowDegree I 1) := by
    intro m hm
    have h := congrFun (hhom hm) 0
    rw [← h, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq0 : q.1 = 0 := Subsingleton.elim _ _
    simp [groupWeight, hq0]
  let ι : Fin n → Fin 1 × Fin n := fun j => (0, j)
  have hsnd : ∀ p : MvPolynomial (Fin 1 × Fin n) F, rename ι (rename Prod.snd p) = p := by
    intro p
    rw [rename_rename]
    convert rename_id_apply p
    funext q
    exact Prod.ext (Subsingleton.elim _ _) rfl
  set f₀ := rename Prod.snd f with hf₀
  set N : MvPolynomial (Fin n) F := _root_.GroundTheory.Heights₂.Heights.Vertical.normForm (R := F) L ξ with hN
  have hprod : N.map (algebraMap F K) = ∏ σ : L →ₐ[F] K, embForm σ ξ := normForm_map_eq_prod ξ

  have hdvd1 : f ∣ rename ι N := by
    refine (hf.2 _).1 fun u hu => ?_
    obtain ⟨y, hy0, hyI, hyu⟩ := hu
    have hyi : y i ≠ 0 := hCone F n I i hI hdim hXi K y hy0 hyI
    let ys : Fin n → K := fun j => (y i)⁻¹ * y j
    have hker : J ≤ RingHom.ker (aeval (R := F) ys).toRingHom := by
      refine sup_le (fun g hg => ?_) ((Ideal.span_le).mpr ?_)
      · set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          ← sum_homogeneousComponent g, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d g),
          hyI _ (hI.isHomog g hg d), mul_zero]
      · rintro _ rfl
        simp [ys, hyi]
    let σ : L →ₐ[F] K := Ideal.Quotient.liftₐ J (aeval ys) fun g hg => hker hg
    have hσ : ∀ j, σ (ξ j) = ys j := fun j =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp [ys])
    rw [aeval_rename, aeval_def, ← eval_map, hprod, eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
    rw [eval_embForm]
    simp only [hσ, ys, Function.comp_apply, ι]
    have := hyu 0
    calc ∑ j, u (0, j) * ((y i)⁻¹ * y j) = (y i)⁻¹ * ∑ j, u (0, j) * y j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]

  have hdvd2 : ∀ σ : L →ₐ[F] K, embForm σ ξ ∣ f₀.map (algebraMap F K) := by
    intro σ
    have hprime : Prime (embForm σ ξ) := (irreducible_embForm σ ht).prime
    have hspan : (Ideal.span {embForm σ ξ}).IsPrime :=
      (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
    rw [← Ideal.mem_span_singleton, ← hspan.radical,
      ← vanishingIdeal_zeroLocus_eq_radical (K := K), mem_vanishingIdeal_iff]
    intro u hu
    have hu0 : ∑ j, u j * σ (ξ j) = 0 := by
      have := hu _ (Ideal.mem_span_singleton_self _)
      rwa [aeval_eq_eval, eval_embForm] at this
    rw [aeval_eq_eval, eval_map, ← aeval_def, hf₀, aeval_rename]
    refine (hf.2 f).2 dvd_rfl _ ⟨fun j => σ (ξ j), fun h => ?_, fun g hg => ?_, fun k => ?_⟩
    · have := congrFun h i
      simp [hξi] at this
    · rw [← comp_aeval_apply, hξ, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg),
        map_zero]
    · rw [Subsingleton.elim k 0]
      simpa using hu0
  have hdvd3 : N.map (algebraMap F K) ∣ f₀.map (algebraMap F K) := by
    rw [hprod]; exact prod_embForm_dvd hgen ht hdvd2
  have hdvd4 : f₀ ∣ N := by
    have := map_dvd (rename Prod.snd) hdvd1
    rwa [rename_rename, show Prod.snd ∘ ι = id from rfl, rename_id_apply] at this

  have hf0 : f₀ ≠ 0 := fun h => hf.1 (by rw [← hsnd f, ← hf₀, h, map_zero])
  have hmap0 : f₀.map (algebraMap F K) ≠ 0 :=
    fun h => hf0 (map_injective _ (algebraMap F K).injective (by rw [h, map_zero]))
  obtain ⟨h, hh⟩ := hdvd4
  obtain ⟨q, hq⟩ := hdvd3
  have hq1 : q * h.map (algebraMap F K) = 1 := by
    apply mul_left_cancel₀ hmap0
    calc f₀.map (algebraMap F K) * (q * h.map (algebraMap F K))
        = (f₀.map (algebraMap F K) * h.map (algebraMap F K)) * q := by ring
      _ = N.map (algebraMap F K) * q := by rw [hh, map_mul]
      _ = f₀.map (algebraMap F K) * 1 := by rw [← hq, mul_one]
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.mp (isUnit_iff_exists_inv.mpr ⟨_, hq1⟩)
  have hlin : ∀ σ : L →ₐ[F] K, (embForm σ ξ).IsHomogeneous 1 := fun σ =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X K j).mul (isHomogeneous_C _ (σ (ξ j)))
  have h1 : (f₀.map (algebraMap F K)).IsHomogeneous (∑ _σ : L →ₐ[F] K, 1 + 0) := by
    rw [hq, hprod, hc]
    exact (IsHomogeneous.prod _ _ _ fun σ _ => hlin σ).mul (isHomogeneous_C _ c)
  have h2 : (f₀.map (algebraMap F K)).IsHomogeneous (chowDegree I 1) :=
    hfH.rename_isHomogeneous.map _
  rw [h2.inj_right h1 hmap0]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, add_zero]
  exact AlgHom.card F L K

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowDegreeSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous' {R : Type*} [CommSemiring R] {k n : ℕ} (u : Fin n → R)
    (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X R (groupWeight k n) (i', j)

theorem isMultiHomog_specFirst {R : Type*} [CommSemiring R] {k n δ : ℕ}
    {f : MvPolynomial (Fin (k + 1) × Fin n) R} (u : Fin n → R) (hf : IsMultiHomog δ f) :
    IsMultiHomog δ (specFirst f u) := by
  unfold IsMultiHomog specFirst
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous' u ij).pow _

theorem ChowDegreeSection.proof (h : ChowFormSectionPerfect.Statement) : ChowDegreeSection.Statement := by
  intro F _ _ n e I u hI hdim hu
  obtain ⟨f, hf⟩ := chowFormExists F n (e + 2) I hI hdim
  have hfδ : IsMultiHomog (chowDegree I (e + 2)) f := Vertical.ChowFormHomog.proof F n (e + 2) I f hf
  obtain ⟨c, hc, g, hg, hfu⟩ := h F n (e + 1) I f u hI hf hu
  have hsδ : IsMultiHomog (chowDegree I (e + 2)) (specFirst f u) := isMultiHomog_specFirst u hfδ
  have hne : C c * ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W ≠ 0 := by
    refine mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => ?_)
    exact pow_ne_zero _ (hg W hW).1
  rw [hfu] at hsδ
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) (divCycle I u) c g hg hsδ hne
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_congr rfl fun W hW => ?_
  congr 1
  exact Vertical.chowForm_degree_unique (Nat.succ_pos e) (hg W hW) (hg W hW) (hδW W hW)
    (Vertical.ChowFormHomog.proof F n (e + 1) W (g W) (hg W hW))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem real_smul_mem_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) (t : ℝ) :
    t • y ∈ coneSet h J := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  intro q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy (t : ℂ) q hq

theorem coneFibreAverage_of_lt {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      1 * Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have hlt : (finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) < ((2 * m : ℕ) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 2 * n < 2 * m)
  rw [Real.hausdorffMeasure_of_finrank_lt hlt, Measure.coe_zero, Pi.zero_apply, mul_zero]
  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) = 0 := by
    intro π
    rw [lintegral_congr_ae (g := fun _ => 0) (ae_restrict_of_ae (by
        filter_upwards [ae_fibreCount_eq_zero hnm h J π] with w hw
        simp [hw])), lintegral_zero]
  simp [hin]

theorem coneFibreAverage_zero {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J)
    (hfib : ∀ᵐ π : Fin 0 → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 0), fibreCount h J π w ≠ ⊤) :
    ∫⁻ π : Fin 0 → Fin n → ℂ, matGauss π *
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1, (fibreCount h J π w : ℝ≥0∞) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1) *
        Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} := by
  have : (volume : Measure (Fin 0 → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin 0 → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin 0)))).NeBot := ae_neBot.2 (NeZero.ne _)
  have hcount : ∀ (π : Fin 0 → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin 0)),
      fibreCount h J π w = (coneSet h J).encard := by
    intro π w
    rw [fibreCount]
    congr 1
    ext y
    simp [Subsingleton.elim (linProj π y) w]
  obtain ⟨π₀, hπ₀⟩ := hfib.exists
  obtain ⟨w₀, hw₀⟩ := hπ₀.exists
  rw [hcount] at hw₀
  have hsub : coneSet h J ⊆ {0} := by
    intro y hy
    by_contra hy0
    rw [Set.mem_singleton_iff] at hy0
    have hinf : (Set.range fun t : ℂ => t • y).Infinite :=
      Set.infinite_range_of_injective (smul_left_injective ℂ hy0)
    have hsub' : (Set.range fun t : ℂ => t • y) ⊆ coneSet h J := by
      rintro _ ⟨t, rfl⟩ q hq
      rw [HermNorm.pointOf_smul']
      exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq
    exact hw₀ (hinf.mono hsub').encard_eq
  have hset : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J} = coneSet h J := by
    ext y
    refine ⟨fun hy => hy.2, fun hy => ⟨?_, hy⟩⟩
    rw [Set.mem_singleton_iff.1 (hsub hy)]
    simp
  have hmass : Measure.hausdorffMeasure ((2 * 0 : ℕ) : ℝ) (coneSet h J) =
      ((coneSet h J).encard : ℝ≥0∞) := by
    rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h0
    · rw [h0]
      simp
    · rw [h0, Nat.mul_zero, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton,
        Set.encard_singleton]
      simp
  have hgauss : ∀ π : Fin 0 → Fin n → ℂ, matGauss π = 1 := by
    intro π
    simp [matGauss]
  have huniv : (volume : Measure (Fin 0 → Fin n → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp_rw [hgauss, hcount, one_mul, setLIntegral_const]
  rw [lintegral_const, huniv, mul_one, hset, hmass, mul_comm]

theorem ConeFibreAverage.proof (hA : ConeAreaFormula.Statement) (hT : ConeTangentAverage.Statement)
    (hR : ConeRadialIntegral.Statement) (hG : TangentGaussMoment.Statement) :
    ConeFibreAverage.Statement := by
  intro n m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨volume (Metric.ball (0 : EuclideanSpace ℂ (Fin 0)) 1), Metric.measure_ball_pos _ _ one_pos,
      measure_ball_lt_top, fun h J hJ hfib => coneFibreAverage_zero h J hJ hfib⟩
  by_cases hmn : m ≤ n
  swap
  · exact ⟨1, one_pos, ENNReal.one_lt_top, fun h J _ _ => coneFibreAverage_of_lt (by omega) h J⟩
  obtain ⟨hkm, hkanti, hkpos, hM0, hMtop⟩ := hG n m hm hmn
  set μ := Measure.hausdorffMeasure (X := EuclideanSpace ℂ (Fin n)) ((2 * m : ℕ) : ℝ) with hμ
  set k := tangentGaussProfile n m with hk
  set M := ∫⁻ r in Set.Ioi (0 : ℝ), k r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hM
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨H, hHdef⟩ : ∃ H, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = H := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = V := ⟨_, rfl⟩
  have hH0 : H ≠ 0 := by
    rw [← hHdef, hd]
    exact (Metric.measure_ball_pos _ _ one_pos).ne'
  have hHtop : H ≠ ⊤ := by
    rw [← hHdef, hd]
    exact measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := hVdef ▸ (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ⊤ := hVdef ▸ measure_ball_lt_top.ne
  have hc0 : H⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hHtop) hV0
  have hctop : H⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hH0) hVtop
  refine ⟨H⁻¹ * V * M, ENNReal.mul_pos hc0 hM0.ne', ENNReal.mul_lt_top hctop.lt_top hMtop, ?_⟩
  intro h J hJ hfib

  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
        H⁻¹ * V * ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y) ∂μ := by
    intro π
    have harea := hA n m h J hJ hm hmn hfib π ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet)
    have hind : ∫⁻ w, (fibreCount h J π w : ℝ≥0∞) * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 w = ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
      congr 1
      funext w
      by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1 <;> simp [hw]
    rw [hind, hVdef, hHdef] at harea
    rw [mul_assoc, harea, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHtop, one_mul]
  have hlhs : ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, (fibreCount h J π w : ℝ≥0∞) =
      H⁻¹ * V * ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
    rw [← hT n m h J hJ hm hmn hfib, ← lintegral_const_mul' _ _ hctop]
    refine lintegral_congr fun π => ?_
    rw [hin π]
    ring
  rw [hlhs]
  by_cases hfin : μ {y | ‖y‖ < 1 ∧ y ∈ coneSet h J} < ⊤
  · rw [hR n m hm (coneSet h J) (fun y hy t _ => real_smul_mem_coneSet h hJ hy t) hfin k hkm]
    ring
  · rw [not_lt, top_le_iff] at hfin
    rw [hfin, ENNReal.mul_top (ENNReal.mul_pos hc0 hM0.ne').ne']
    have hball : MeasurableSet {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} :=
      measurableSet_lt measurable_norm measurable_const
    have hge : k 1 * ⊤ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
      calc k 1 * ⊤ = ∫⁻ y in coneSet h J, {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1}.indicator
              (fun _ => k 1) y ∂μ := by
            rw [lintegral_indicator_const hball, Measure.restrict_apply hball]
            congr 1
            exact hfin.symm
        _ ≤ ∫⁻ y in coneSet h J, k ‖y‖ ∂μ := by
            refine lintegral_mono fun y => ?_
            by_cases hy : ‖y‖ < 1
            · rw [Set.indicator_of_mem (show y ∈ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact hkanti (Set.mem_Ici.2 (norm_nonneg y)) (Set.mem_Ici.2 zero_le_one) hy.le
            · rw [Set.indicator_of_notMem (show y ∉ {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1} from hy)]
              exact bot_le
    rw [ENNReal.mul_top (hkpos 1).ne', top_le_iff] at hge
    rw [hge, ENNReal.mul_top hc0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal ComplexOrder

theorem gramVol_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

section Abstract

variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

variable [MeasurableSpace X]

end Abstract

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsLeadPlaneJac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LeadPlaneJac.Statement : Prop :=
  ∀ (m k : ℕ) (π : Fin m → Fin (m + k) → ℂ),
    tangentJac π (leadCoordPlane (m + k) m) = ‖(coordPlaneBlock π).det‖ ^ 2

end

end GroundTheory.Heights₂.Heights
end

