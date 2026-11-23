module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0097
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatTransUpToSqPullback
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CoefUpTo

theorem coef_upTo : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) →
    ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := by
  intro R _ C _ F F' α s h n
  have inj : ∀ k (f : Cn F k), (Mor.ofNatTrans α).pullC k f = 0 → s • f = 0 := fun k f hf =>
    funext fun c => (h _).1 (f c) (congrFun hf c)
  have surj : ∀ k (g : Cn F' k), ∃ f : Cn F k, (Mor.ofNatTrans α).pullC k f = s • g := fun k g => by
    choose f hf using fun c : ComposableArrows C k => (h (c.obj (Fin.last k))).2 (g c)
    exact ⟨f, funext hf⟩
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F) n).1 x
    have hz : (cx F').d n ((Mor.ofNatTrans α).pullC n a) = 0 := by
      have ha' : d F n a = 0 := ha
      change d F' n _ = 0
      rw [Mor.d_pullC, ha', map_zero]
    have hx' : (cx F').cls ((Mor.ofNatTrans α).pullC n a) hz = 0 := hx
    rw [(CrystallineSemistableComparison.P.cls_surj (cx F') n).2.1] at hx'
    have hd : (cx F).d n ((s ^ 2) • a) = 0 := by rw [map_smul, ha, smul_zero]
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.2.2.2 (s ^ 2) a ha hd, (CrystallineSemistableComparison.P.cls_surj (cx F) n).2.1]
    cases n with
    | zero =>
      have h0 : (Mor.ofNatTrans α).pullC 0 a = 0 := hx'
      have h1 : (s ^ 2) • a = 0 := by rw [pow_two, mul_smul, inj 0 a h0, smul_zero]
      rw [h1]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g', hg'⟩ := hx'
      have hg'' : d F' n g' = (Mor.ofNatTrans α).pullC (n + 1) a := hg'
      obtain ⟨g, hg⟩ := surj n g'
      have h0 : (Mor.ofNatTrans α).pullC (n + 1) (s • a - d F n g) = 0 := by
        rw [map_sub, ← Mor.d_pullC, hg, map_smul, map_smul, hg'']
        simp
      have h1 := inj _ _ h0
      rw [smul_sub, sub_eq_zero] at h1
      refine ⟨s • g, ?_⟩
      change d F n (s • g) = (s ^ 2) • a
      rw [map_smul, ← h1, pow_two, mul_smul]
  · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx F') n).1 y
    have hb' : d F' n b = 0 := hb
    obtain ⟨f, hf⟩ := surj n b
    have h0 : (Mor.ofNatTrans α).pullC (n + 1) (d F n f) = 0 := by
      rw [← Mor.d_pullC, hf, map_smul, hb', smul_zero]
    have h1 : d F n (s • f) = 0 := by rw [map_smul]; exact inj _ _ h0
    have hd : (cx F').d n ((s ^ 2) • b) = 0 := by rw [map_smul, hb, smul_zero]
    have e : (Mor.ofNatTrans α).pullC n (s • f) = (s ^ 2) • b := by
      rw [map_smul, hf, pow_two, mul_smul]
    refine ⟨(cx F).cls (s • f) h1, ?_⟩
    rw [← (CrystallineSemistableComparison.P.cls_surj (cx F') n).2.2.2.2 (s ^ 2) b hb hd]
    change (cx F').cls ((Mor.ofNatTrans α).pullC n (s • f)) _ = _
    simp only [e]

end GlobalTheory.CompanionTheory.CoefUpTo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationOfDichotomyStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
open Polynomial in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_approximation_of_dichotomy : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S := S ⧸ Ideal.span {ϖ ^ 2}) → Step ϖ := by
  intro S _ ϖ hj hnz hD hA
  have hStep : Step ϖ := by
    intro Q n hQ hd hn
    have hRoots : Roots ϖ := GlobalTheory.T.polynomial_roots_of_closed_quotient ϖ hj hnz hD hA
    have hq0 : Q.coeff 0 = Q.eval 0 := Polynomial.coeff_zero_eq_eval_zero Q
    have hspan : ϖ ^ (n + 1) ∈ Ideal.span {Q.coeff 0, ϖ ^ (n + 1)} :=
      Ideal.subset_span (by simp)
    rcases hD (Q.coeff 0) (ϖ ^ (n + 1)) ⟨n + 1, hspan⟩ with hdiv | hdiv
    · refine ⟨0, ?_, ?_⟩
      · rw [← hq0]; exact hdiv
      · rw [zero_pow hd.ne']; exact dvd_zero _
    ·
      have hpow : ϖ ^ (n + 1) ∈ nonZeroDivisors S := pow_mem hnz _
      have hcancel : ∀ x : S, Q.coeff 0 * x = 0 → x = 0 := by
        intro x hx
        obtain ⟨e, he⟩ := hdiv
        have h0 : ϖ ^ (n + 1) * x = 0 := by
          rw [he]; linear_combination e * hx
        exact (mem_nonZeroDivisors_iff_right.mp hpow) x (by rw [mul_comm]; exact h0)
      obtain ⟨c, hc1, i0, hi1, hi2, hi3⟩ := _root_.GlobalTheory.CompanionTheory.NewtonSlope.first_slope ϖ hD hRoots (fun i => Q.coeff i)
        Q.natDegree (n + 1) hd hQ.coeff_natDegree hdiv
      have hs : ∀ i, ∃ t, (i = 0 → t = 1) ∧
          (i ≤ Q.natDegree → Q.coeff i * c ^ i = Q.coeff 0 * t) := by
        intro i
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact ⟨1, fun _ => rfl, fun _ => by simp⟩
        · by_cases hid : i ≤ Q.natDegree
          · obtain ⟨t, ht⟩ := hc1 i hi hid
            exact ⟨t, fun h => by omega, fun _ => ht⟩
          · exact ⟨0, fun h => by omega, fun h => by omega⟩
      choose s hs0 hsd using hs
      have hunit : IsUnit (s i0) := by
        obtain ⟨t, ht⟩ := hi3
        have h5 : Q.coeff 0 * (s i0 * t - 1) = 0 := by
          have h6 := hsd i0 hi2
          rw [h6] at ht
          linear_combination -ht
        have h7 := hcancel _ h5
        exact IsUnit.of_mul_eq_one t (by linear_combination h7)
      let R : Polynomial S := ∑ i ∈ Finset.range (Q.natDegree + 1),
        Polynomial.C (s i) * Polynomial.X ^ i
      have hRc : ∀ j, j ≤ Q.natDegree → R.coeff j = s j := by
        intro j hj'
        simp only [R, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
        rw [Finset.sum_ite_eq]
        simp [Nat.lt_succ_of_le hj']
      have hRe : ∀ y, R.eval y = ∑ i ∈ Finset.range (Q.natDegree + 1), s i * y ^ i := by
        intro y
        simp [R, Polynomial.eval_finsetSum]
      let P : Polynomial (S ⧸ Ideal.span {ϖ ^ 2}) := R.map (Ideal.Quotient.mk _)
      have hP0 : P.coeff 0 = 1 := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc 0 (Nat.zero_le _), hs0 0 rfl, map_one]
      have hPi : IsUnit (P.coeff i0) := by
        simp only [P, Polynomial.coeff_map]
        rw [hRc i0 hi2]
        exact hunit.map _
      have hroot : ∃ y', P.eval y' = 0 := by
        let T := S ⧸ Ideal.span {ϖ ^ 2}
        rcases subsingleton_or_nontrivial T with hT | hT
        · exact ⟨0, Subsingleton.elim _ _⟩
        have hAdd : ∀ a b : T, IsUnit (a + b) → IsUnit a ∨ IsUnit b :=
          GlobalTheory.CompanionTheory.NewtonStep.isUnit_or_of_add_quot ϖ hj hD
        have unitRoot : ∀ (d : ℕ) (F : Polynomial T), F.Monic → F.natDegree = d →
            ∀ k < d, IsUnit (F.coeff k) → ∃ u : Tˣ, F.eval (u : T) = 0 := by
          intro d
          induction d with
          | zero =>
            intro F hF hdeg k hk
            omega
          | succ d ih =>
            intro F hF hdeg k hk hcoeff
            obtain ⟨x, hx⟩ := hA F hF (by omega)
            by_cases hxu : IsUnit x
            · obtain ⟨u, rfl⟩ := hxu
              exact ⟨u, hx⟩
            let G := F /ₘ (X - C x)
            have hfactor : (X - C x) * G = F := mul_divByMonic_eq_iff_isRoot.mpr hx
            have hG : G.Monic := (monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hF)
            have hGdeg : G.natDegree = d := by
              have h := (monic_X_sub_C x).natDegree_mul hG
              rw [hfactor, hdeg, natDegree_X_sub_C] at h
              omega
            cases k with
            | zero =>
              rw [← hfactor, sub_mul, coeff_sub, coeff_X_mul_zero, coeff_C_mul, zero_sub] at hcoeff
              have hprod : IsUnit (x * G.coeff 0) := by simpa only [neg_neg] using hcoeff.neg
              exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
            | succ k =>
              rw [← hfactor, coeff_X_sub_C_mul, sub_eq_add_neg] at hcoeff
              rcases hAdd _ _ hcoeff with hGu | hneg
              · obtain ⟨u, hu⟩ := ih G hG hGdeg k (by omega) hGu
                exact ⟨u, by rw [← hfactor, eval_mul, hu, mul_zero]⟩
              · have hprod : IsUnit (x * G.coeff (k + 1)) := by
                  simpa only [neg_neg] using hneg.neg
                exact (hxu (isUnit_of_mul_isUnit_left hprod)).elim
        have htd : P.natTrailingDegree = 0 :=
          Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero (by rw [hP0]; exact one_ne_zero))
        have hmon : P.reverse.Monic := by
          rw [Monic, reverse_leadingCoeff, trailingCoeff, htd, hP0]
        have hdeg : P.reverse.natDegree = P.natDegree := by
          rw [reverse_natDegree, htd, Nat.sub_zero]
        have hle : i0 ≤ P.natDegree := le_natDegree_of_ne_zero hPi.ne_zero
        have hcoeff : P.reverse.coeff (P.natDegree - i0) = P.coeff i0 := by
          rw [coeff_reverse, revAt_le (Nat.sub_le _ _)]
          congr 1
          omega
        obtain ⟨u, hu⟩ := unitRoot P.natDegree P.reverse hmon hdeg (P.natDegree - i0)
          (by omega) (hcoeff.symm ▸ hPi)
        refine ⟨↑(u⁻¹), ?_⟩
        let : Invertible ((u⁻¹ : Tˣ) : T) := (u⁻¹).invertible
        have hre := eval₂_reverse_mul_pow (RingHom.id T) ((u⁻¹ : Tˣ) : T) P
        have hinv : ⅟((u⁻¹ : Tˣ) : T) = (u : T) := by simp
        rw [hinv, eval₂_id, eval₂_id, hu, zero_mul] at hre
        exact hre.symm
      obtain ⟨y', hy'⟩ := hroot
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y'
      have hRy : ϖ ^ 2 ∣ R.eval y := by
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
        simp only [P, Polynomial.eval_map] at hy'
        rwa [Polynomial.eval₂_at_apply] at hy'
      have hQz : Q.eval (c * y) = Q.coeff 0 * R.eval y := by
        rw [Polynomial.eval_eq_sum_range, hRe, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h8 := hsd i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        rw [mul_pow]
        linear_combination (y ^ i) * h8
      have hn0 : ϖ ^ n ∣ Q.coeff 0 := by rw [hq0]; exact hn
      refine ⟨c * y, ?_, ?_⟩
      · rw [hQz]
        have h9 : ϖ ^ n * ϖ ^ 2 ∣ Q.coeff 0 * R.eval y := mul_dvd_mul hn0 hRy
        refine dvd_trans ?_ h9
        rw [← pow_add]
        exact pow_dvd_pow _ (by omega)
      · have h10 : Q.coeff 0 ∣ c ^ Q.natDegree := by
          have h11 := hc1 Q.natDegree hd le_rfl
          simpa [hQ.coeff_natDegree] using h11
        rw [mul_pow]
        exact dvd_mul_of_dvd_left (dvd_trans hn0 h10) _
  exact hStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalRiemannExtensionLocal
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Branch

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial _root_.Topology Filter Metric

theorem normalRiemannExtensionLocal (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by
  intro σ _ I h w U f hI hIc hh hw hU hf hb
  classical
  have hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [eval_add]; exact hp.add hq
    | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
  obtain ⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩ := hud σ I h w U f hI hh hw hU hf hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hhg : h * g ∉ I := fun hm => (hI.mem_or_mem hm).elim hh hg
  obtain ⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by
    refine ⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩
    have h1 := hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩
    refine closure_mono (fun y hy => ?_) h1
    exact ⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩
  set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT
  have hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g) := hpoly g

  have hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧
      eval z g * f z = F z := by
    intro z hz
    have hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0 := by
      simpa only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or] using hz.2
    exact ⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2,
      hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩
  have hTf : ∀ z ∈ T, F z / eval z g = f z := fun z hz => by
    obtain ⟨-, hg0, he⟩ := hTS z hz
    rw [← he, mul_div_cancel_left₀ _ hg0]
  have hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆
      Metric.closedBall 0 M := by
    rintro _ ⟨p, hp, rfl⟩
    have hpc : p ∈ closure T := hdense hp.1
    have hcont : ContinuousWithinAt (fun z => F z / eval z g) T p :=
      (((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div
        (hGd p).continuousAt hp.2)).continuousWithinAt
    refine closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F z / eval z g‖ ≤ M
    rw [hTf z hz]
    exact hM _ ⟨z, (hTS z hz).1, rfl⟩
  have hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0) := by
    intro hev
    obtain ⟨z, hzW, hzT⟩ := mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev
    exact (hTS z hzT).2.1 (hzW hzT.1.1)
  obtain ⟨V, hVo, hwV, H, hH, hFGH⟩ := hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB
    (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)
  refine ⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩
  intro p hp
  obtain ⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩ :=
    hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩
  rw [hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]

  set O := V ∩ Up
  have hOo : IsOpen O := hVo.inter hUpo
  have hpO : p ∈ O := ⟨hp.1.2.1, hpUp⟩
  set s := O ∩ T
  have heq : Set.EqOn H Fp s := by
    intro z hz
    obtain ⟨hzS, hg0, he⟩ := hTS z hz.2
    have h1 : eval z g * H z = eval z g * f z := by
      rw [he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]
    rw [mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]
  have hsO : insert p s ⊆ O := Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩
  exact heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO)
    ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s)
    (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩)
    (Set.mem_insert p s)

theorem irreducibleGermCurve
    (hslice : ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
      GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧
        IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧
        ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0)
    (hdisc : ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ)
      (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w →
      (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N)
    (hCv : CentredDiscCoverCurve.Statement) : IrreducibleGermCurve.Statement := by
  intro σ _ X w hX hirr hacc
  obtain ⟨Y, W, A, hW, hYX, hYa, hYi, hiso, hdom⟩ := hslice σ X w hX hirr hacc
  obtain ⟨Y', p, ρ, N, hY'Y, hcov⟩ := hdisc σ Y w A hYa hYi hiso hdom
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγY⟩ := hCv σ Y' w p ρ N hcov
  have hcont : ContinuousAt γ 0 := hγd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rw [hγ0]; exact hW)
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hpre (ball_mem_nhds (0 : ℂ) hr))
  have hle : ball (0 : ℂ) r' ⊆ ball 0 r := fun t ht => (hsub ht).2
  exact ⟨r', hr', γ, hγd.mono hle, hγi.mono hle, hγ0,
    fun t ht => hYX ⟨hY'Y (hγY (hle ht)), (hsub ht).1⟩⟩

end GlobalTheory.CompanionTheory.Ar.Branch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternSetCardColumnStep
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) := by
  refine ⟨fun i h => lt_irrefl _ h.1, ?_⟩
  intro a b c hab hbc
  exact ⟨hab.1.trans hbc.1, hbc.2⟩

def colGeSplit (d j : ℕ) (hj : j < d) :
    Fin j ⊕ {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} →
      {p : Fin d × Fin d // colGe d j p.1 p.2}
  | Sum.inl i => ⟨(⟨i.1, i.2.trans hj⟩, ⟨j, hj⟩), by
      refine ⟨?_, le_refl _⟩
      exact Fin.mk_lt_mk.2 i.2⟩
  | Sum.inr p => ⟨p.1, p.2.1, Nat.le_of_succ_le p.2.2⟩

theorem colGeSplit_bijective (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun x => (x.1.1 : Fin d).1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := b.2.2
      omega
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := a.2.2
      omega
    · have h1 := congrArg (fun x => x.1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inr (Subtype.ext h1)
  · rintro ⟨⟨i, l⟩, hil, hjl⟩
    by_cases e : (l : ℕ) = j
    · have hi : (i : ℕ) < j := by
        have : (i : ℕ) < l := hil
        omega
      refine ⟨Sum.inl ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp only [colGeSplit]
      exact Prod.ext rfl (Fin.ext e.symm)
    · have hl : j + 1 ≤ (l : ℕ) := by
        have : j ≤ (l : ℕ) := hjl
        omega
      exact ⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩

theorem natCard_colGe (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet (K := K) (colGe d j)).ncard =
      Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard := by
  classical
  have card_colGe (k : ℕ) :
      (patSet (K := K) (colGe d k)).ncard =
        Fintype.card K ^ Nat.card {p : Fin d × Fin d // colGe d k p.1 p.2} := by
    let A (f : {p : Fin d × Fin d // colGe d k p.1 p.2} → K) : Matrix (Fin d) (Fin d) K :=
      fun i l => if i = l then 1 else if h : colGe d k i l then f ⟨(i, l), h⟩ else 0
    have hunit (f) : IsUnit (A f).det := by
      have htri : (A f).IsUpperTriangular := by
        intro i l h
        change l < i at h
        have hnot : ¬ colGe d k i l := fun hcol => (not_lt_of_gt h) hcol.1
        simp [A, ne_of_gt h, hnot]
      rw [Matrix.det_of_isUpperTriangular htri]
      simp [A]
    let e : patSet (K := K) (colGe d k) ≃ ({p : Fin d × Fin d // colGe d k p.1 p.2} → K) :=
      { toFun := fun u p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.nonsingInvUnit (A f) (hunit f), by
          intro i l
          change (i = l → A f i l = 1) ∧ (i ≠ l → ¬ colGe d k i l → A f i l = 0)
          exact ⟨fun h => by simp [A, h], fun h hcol => by simp [A, h, hcol]⟩⟩
        left_inv := fun u => by
          apply Subtype.ext
          apply Units.ext
          ext i l
          change A (fun p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2) i l =
            (u.val : Matrix (Fin d) (Fin d) K) i l
          have hu := u.property i l
          by_cases hil : i = l
          · simpa only [A, ite_eq_left hil] using (hu.1 hil).symm
          · by_cases hcol : colGe d k i l
            · simp [A, hil, hcol]
            · simp [A, hil, hcol, hu.2 hil hcol]
        right_inv := fun f => by
          funext p
          change A f p.1.1 p.1.2 = f p
          have hil : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
          simp [A, hil, p.2] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
  rw [card_colGe j, card_colGe (j + 1), natCard_colGe d j hj, pow_add]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNegStatement
section
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_opposite_neg : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ v : ℂ, MulOpposite.unop (Formalism.REAL.qdet (fun i j => MulOpposite.op (-X i j)) v) = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet X ((n : ℂ) - 1 - v) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | exact GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | (intros; apply GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg <;> assumption)
end

