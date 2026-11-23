module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum GlobalTheory.DeformedSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.DerivAtOrigin

theorem series_weightTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (σ : ℂ), 0 < σ.re → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → DifferentiableAt ℝ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z ∧ ∀ i : I, wirt i false (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z = ∑' q : modUnits (lattice c y), eTerm φ (m + Pi.single i 1) σ z q.1.out := by
  intro E _ _ _ I _ _ φ hφ c y hc σ hσ m z hz
  have hz1 : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1
  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(1 + σ.re)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (1 + σ.re) hc (by linarith)
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  choose C hC using fun m : I → ℕ => _root_.GlobalTheory.WeightTwoSum.Bound.eTerm_bound E I φ hφ m σ r hσ.le hr1
  have hsum : ∀ m, ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => eTerm φ m σ w q.1.out) := fun m w hw =>
    Summable.of_norm_bounded (hNs.mul_left (C m)) fun q => hC m w (hUle w hw) _ (hne q)
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℝ] ℂ) := fun q w =>
    ∑ j, (eTerm φ (m + Pi.single j 1) σ w q.1.out • dz j +
      (eTerm φ m σ w q.1.out * (-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j))) • dzbar j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j : I, (C (m + Pi.single j 1) * N q * ‖(dz j : (I → ℂ) →L[ℝ] ℂ)‖ +
    C m * N q * (‖σ‖ / (1 - r)) * ‖(dzbar j : (I → ℂ) →L[ℝ] ℂ)‖) with hu
  have hus : Summable u := summable_sum fun j _ =>
    ((hNs.mul_left _).mul_right _).add (((hNs.mul_left _).mul_right _).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => eTerm φ m σ w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm E I φ m σ q.1.out (hne q) w (hUpd w hw)
  have hrat : ∀ (q : modUnits (lattice c y)) w, w ∈ U → ∀ j,
      ‖-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j)‖ ≤ ‖σ‖ / (1 - r) := by
    intro q w hw j
    have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ w q.1.out j (hUle w hw j)
    have hp : 0 < ‖φ j q.1.out‖ := by simpa using hne q
    have hr' : 0 < 1 - r := by linarith
    have hd : 0 < ‖defCoord φ w q.1.out j‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
    rw [norm_div, norm_mul, norm_neg, Complex.norm_conj, div_le_div_iff₀ hd hr']
    nlinarith [norm_nonneg σ]
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans (add_le_add ?_ ?_))
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC _ w (hUle w hw) _ (hne q)) (norm_nonneg _)
    · rw [norm_smul, norm_mul]
      have h1 := hC m w (hUle w hw) _ (hne q)
      exact mul_le_mul_of_nonneg_right (mul_le_mul h1 (hrat q w hw j) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum m z hzU) hzU
  refine ⟨hF.differentiableAt, fun i => ?_⟩
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hap : ∀ v : I → ℂ, HasSum (fun q => f' q z v) ((∑' q, f' q z) v) := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).hasSum hcs.hasSum
  unfold wirt
  rw [hF.fderiv]
  refine (HasSum.tsum_eq ?_).symm
  refine (((hap _).add ((hap _).mul_left _)).div_const 2).congr_fun ?_
  intro q
  simp only [hf', ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dz_apply,
    dzbar_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
    Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, Complex.conj_I, Bool.false_eq_true, if_false]
  linear_combination (eTerm φ (m + Pi.single i 1) σ z q.1.out / 2 -
    eTerm φ m σ z q.1.out * (-σ * φ i q.1.out / starRingEnd ℂ (defCoord φ z q.1.out i)) / 2) * Complex.I_mul_I

theorem wirtWord_congr {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U) {f g : (I → ℂ) → ℂ}
    (h : ∀ z ∈ U, f z = g z) (w : List (I × Bool)) : ∀ z ∈ U, wirtWord w f z = wirtWord w g z := by
  induction w with
  | nil => exact h
  | cons a w ih =>
    intro z hz
    have hev : wirtWord w f =ᶠ[nhds z] wirtWord w g := by
      filter_upwards [hU.mem_nhds hz] with u hu using ih u hu
    simp only [wirtWord_cons, wirt, hev.fderiv_eq]

theorem wirt_const_mul {I : Type} [Fintype I] (i : I) (bar : Bool) (a : ℂ) {f : (I → ℂ) → ℂ} {z : I → ℂ}
    (hf : DifferentiableAt ℝ f z) : wirt i bar (fun w => a * f w) z = a * wirt i bar f z := by
  simp only [wirt, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem eq_at_zero {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPlane) (hg : DifferentiableOn ℂ g halfPlane)
    (h : ∀ σ : ℂ, 0 < σ.re → f σ = g σ) : f 0 = g 0 := by
  have ho : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hc : IsPreconnected halfPlane := (convex_halfSpace_re_gt _).isPreconnected
  have h1 : (1 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have h0 : (0 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have ho' : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd ho) hc h1 ?_ h0
  filter_upwards [ho'.mem_nhds (show (1 : ℂ) ∈ {s : ℂ | 0 < s.re} by simp)] with s hs using h s hs

theorem isOpen_upperHalf (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply i))

theorem derivFormula_two (hH : HeckeWeightTwo) (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    [DecidableEq I] (φ : I → E →+* ℂ) (hF : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)) (hφ : IsCMType φ)
    (c : Ideal (OF E)) (y : (Af E)ˣ) (hc : c ≠ ⊥) : DerivFormula φ 2 (lattice c y) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield E I φ hφ
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_element_pos_im_under_cmType E I φ hφ
  have hne : Nonempty I := by
    obtain ⟨i, -⟩ := hφ (Classical.arbitrary (E →+* ℂ))
    exact ⟨i⟩
  have hnot : ∀ θ : E, (∀ i, 0 < (φ i θ).im) → θ ∉ maximalRealSubfield E := fun θ h hθ => by
    obtain ⟨i⟩ := hne
    have h1 := h i
    rw [show θ = ((⟨θ, hθ⟩ : maximalRealSubfield E) : E) from rfl, he] at h1
    simp at h1
  obtain ⟨𝔞, 𝔟, a₀, hL⟩ := _root_.GlobalTheory.SteinitzOrder.lattice_eq_steinitz E c y hc θ₀ (hnot θ₀ hθ₀)
  set θ : E := θ₀ + a₀ with hθdef
  have hθ : ∀ i, 0 < (φ i θ).im := fun i => by
    rw [hθdef, map_add (f := _), he]; simpa using hθ₀ i
  obtain ⟨G, ⟨hG1, hG2, hG3⟩, hG0, -⟩ := hH (maximalRealSubfield E) hF 𝔞 𝔟
  have hP := GlobalTheory.WeightTwoSum.isOpen_polydisc I
  have hmaps : Set.MapsTo (modPt φ e θ) (polydisc I) (upperHalf _) := fun z hz τ => modPt_im_pos φ e θ hθ hz τ
  set cw : ℂ := (cWt E 2 : ℂ) with hcw
  set b : (I → ℂ) → ℂ := fun z => (homFac z)⁻¹ ^ 2 with hb
  have hbC : ContDiffOn ℂ ∞ b (polydisc I) :=
    (contDiff_homFac.contDiffOn.inv fun z hz => homFac_ne_zero hz).pow 2
  set K : ℂ → (I → ℂ) → ℂ := fun σ z => b z * Complex.exp (-σ * logFac z) * G σ (modPt φ e θ z) with hK
  have hchain : ∀ (a : ℂ) (w : List (I × Bool)), ∀ z ∈ polydisc I,
      DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => a * K σ z') z) halfPlane := fun a w z hz => by
    have h := GlobalTheory.T.differentiableOn_wirtWord_mul_exp_comp' _ I (polydisc I) (upperHalf _) halfPlane G (modPt φ e θ) (fun z => a * b z) logFac hP
      (isOpen_upperHalf _) hmaps ((contDiffOn_modPt φ e θ).restrict_scalars ℝ)
      ((contDiffOn_const.mul hbC).restrict_scalars ℝ) contDiffOn_logFac hG2 hG3 w z hz
    simpa only [hK, mul_assoc] using h
  have hKd : ∀ z ∈ polydisc I, DifferentiableOn ℂ (fun σ => K σ z) halfPlane := fun z hz => by
    simpa [wirtWord_nil] using hchain 1 [] z hz
  have hKs : ∀ z ∈ polydisc I, ∀ σ : ℂ, 0 < σ.re →
      HasSum (fun q : modUnits (lattice c y) => defTerm φ 2 z σ q.1.out) (K σ z) := fun z hz σ hσ => by
    obtain ⟨h1, h2⟩ := hG1 σ hσ _ (hmaps hz)
    refine _root_.GlobalTheory.WeightTwoCompare.hasSum_defTerm E I φ e he 𝔞 𝔟 θ _ (hnot θ hθ) hL z hz σ _ ?_
    rw [h2]
    exact h1.hasSum
  have hagree : ∀ g, IsDefSum φ 2 (lattice c y) g → ∀ z ∈ polydisc I, g z = cw * K 0 z := by
    intro g hg z hz
    obtain ⟨G', hG', hgz⟩ := hg z hz
    obtain ⟨H, hH1, hH2, rfl⟩ := hG'.2 rfl
    rw [hgz, eq_at_zero hH1 (hKd z hz) fun σ hσ => (hH2 σ hσ).unique (hKs z hz σ hσ)]
  have hK0 : DifferentiableOn ℂ (fun z => cw * K 0 z) (polydisc I) := by
    simp only [hK, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    refine (((hbC.differentiableOn (by simp)).mul (hG0.comp ((contDiffOn_modPt φ e θ).differentiableOn (by simp)) hmaps))).const_mul _
  refine ⟨⟨fun z => cw * K 0 z, fun z hz => ⟨K 0 z, ⟨fun h => absurd rfl h,
    fun _ => ⟨fun σ => K σ z, hKd z hz, hKs z hz, rfl⟩⟩, rfl⟩⟩, fun g hg => ?_⟩
  have hgd : DifferentiableOn ℂ g (polydisc I) := hK0.congr (hagree g hg)
  refine ⟨hgd, fun κ l hl => ⟨fun S hS => ?_, fun h => absurd h (by norm_num)⟩⟩
  have h0 : (0 : I → ℂ) ∈ polydisc I := GlobalTheory.DerivAtOrigin.zero_mem_polydisc I
  have hκ : (fun j => l.count j) = κ := funext hl

  have hser : ∀ σ : ℂ, 0 < σ.re → ∀ l : List I, ∀ z ∈ polydisc I,
      wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') z =
        cw * ∑' q : modUnits (lattice c y), eTerm φ (fun j => l.count j) σ z q.1.out := by
    intro σ hσ l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      simp only [List.map_nil, wirtWord_nil, eTerm_zero]
      rw [(hKs z hz σ hσ).tsum_eq]
    | cons i l ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := series_weightTwo E I φ hφ c y hc σ hσ (fun j => l.count j) z hz
      have h3 := wirtWord_congr hP ih [(i, false)] z hz
      rw [List.map_cons, wirtWord_cons, count_cons_eq, ← h2 i, ← wirt_const_mul i false cw h1]
      exact h3
  rw [_root_.GlobalTheory.HoloWirt.iterD_eq_wirtWord I _ g hP hgd l 0 h0, wirtWord_congr hP (hagree g hg) _ 0 h0, ← risingS_zero]
  refine eq_at_zero (f := fun σ => wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') 0)
    (g := fun σ => cw * risingS σ κ * S σ) (hchain cw _ 0 h0)
    ((((differentiable_risingS κ).const_mul cw).mul hS.1).differentiableOn) fun σ hσ => ?_
  have h4 := hS.2 σ (by push_cast; linarith)
  simp only [hser σ hσ l 0 h0, hκ, eTerm_origin]
  rw [tsum_mul_left, h4.tsum_eq, mul_assoc]

theorem statement (hH : HeckeWeightTwo) : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  intro E _ _ _ I _ _ φ hF hφ
  have hV := GlobalTheory.DualFormOrtho.dualFormValue_of_values E I φ hφ (GlobalTheory.DualFormExists.dualForm_existsUnique E)
    (GlobalTheory.DualFormValues.dualForm_values E)
  refine ⟨fun s hs => ⟨fun c y hc => ⟨?_, GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _⟩,
    GlobalTheory.ClassInv.classInvariance E I φ hφ (GlobalTheory.HomothetyLatSum.homothety E I φ hφ) s⟩, hV,
    GlobalTheory.DualBase.dualFormBase_of_value E I φ hφ hV⟩
  rcases Nat.lt_or_ge s 2 with h | h
  · obtain rfl : s = 1 := by omega
    exact derivFormula_two hH E I φ hF hφ c y hc
  · exact derivFormula_of_series E I φ (2 * s) _ (by omega)
      (fun m z hz => GlobalTheory.DeformedSum.Series.series_differentiable E I φ hφ s h c y hc m z hz)

end GlobalTheory.DerivAtOrigin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedLatticeStabilizerIffBasisIntegral
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatStab

section Core

variable {B : Type} [CommRing B] {n : ℕ}

theorem mulVec_mem_iff (S : Subring B) (y : Matrix (Fin n) (Fin n) B) :
    (∀ v : Fin n → B, (∀ i, v i ∈ S) → ∀ i, y.mulVec v i ∈ S) ↔ ∀ i j, y i j ∈ S := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      rcases eq_or_ne k j with rfl | hk
      · simp
      · simp [hk]) i
    simpa using this
  · intro h v hv i
    show ∑ j, y i j * v j ∈ S
    exact S.sum_mem fun j _ => S.mul_mem (h i j) (hv j)

theorem exists_int_iff (S : Subring B) (y : GL (Fin n) B) :
    (∃ u : GL (Fin n) S, u.val.map S.subtype = y.val) ↔
      (∀ i j, y.val i j ∈ S) ∧ ∀ i j, (y⁻¹).val i j ∈ S := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : Units.map (S.subtype.mapMatrix (m := Fin n)).toMonoidHom u = y := Units.ext hu
    subst h1
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) :=
      Matrix.map_injective S.subtype_injective
    let a : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨_, h2 i j⟩
    have ha : S.subtype.mapMatrix a = y.val := rfl
    have hb : S.subtype.mapMatrix b = (y⁻¹).val := rfl
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, rfl⟩
    · rw [map_mul, ha, hb, map_one, Units.mul_inv]
    · rw [map_mul, ha, hb, map_one, Units.inv_mul]

theorem image_eq_iff {A : Type} [CommRing A] (e : A →+* B) (he : Function.Bijective e) (S : Subring B)
    (β x : GL (Fin n) B) (k : GL (Fin n) A) (hx : x.val = k.val.map e) (L : Set (Fin n → A))
    (hL : ∀ z, z ∈ L ↔ ∀ i, (β⁻¹).val.mulVec (fun a => e (z a)) i ∈ S) :
    k.val.mulVec '' L = L ↔ ∃ u : GL (Fin n) S, u.val.map S.subtype = (β⁻¹ * x * β).val := by
  have key : ∀ (x : GL (Fin n) B) (k : GL (Fin n) A), x.val = k.val.map e →
      ((∀ z ∈ L, k.val.mulVec z ∈ L) ↔ ∀ i j, (β⁻¹ * x * β).val i j ∈ S) := by
    intro x k hx
    have hm : ∀ z : Fin n → A, (β⁻¹).val.mulVec (fun a => e (k.val.mulVec z a)) =
        (β⁻¹ * x * β).val.mulVec ((β⁻¹).val.mulVec (fun a => e (z a))) := by
      intro z
      have : (fun a => e (k.val.mulVec z a)) = x.val.mulVec (fun a => e (z a)) := by
        funext a
        rw [hx, RingHom.map_mulVec]; rfl
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        mul_inv_cancel_right]
    rw [← mulVec_mem_iff]
    constructor
    · intro h v hv
      choose z hz using fun a => he.2 (β.val.mulVec v a)
      have hz' : (β⁻¹).val.mulVec (fun a => e (z a)) = v := by
        rw [show (fun a => e (z a)) = β.val.mulVec v from funext hz, Matrix.mulVec_mulVec, Units.inv_mul,
          Matrix.one_mulVec]
      have := (hL _).1 (h z ((hL z).2 (by rw [hz']; exact hv)))
      rwa [hm, hz'] at this
    · intro h z hz
      rw [hL, hm]
      exact h _ ((hL z).1 hz)
  have hx' : (x⁻¹).val = (k⁻¹).val.map e := by
    have h1 : Units.map (e.mapMatrix (m := Fin n)).toMonoidHom k = x := Units.ext hx.symm
    rw [← h1, ← map_inv]; rfl
  have hi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  rw [exists_int_iff, hi, ← key x k hx, ← key x⁻¹ k⁻¹ hx']
  constructor
  · intro h
    refine ⟨fun z hz => h ▸ ⟨z, hz, rfl⟩, fun z hz => ?_⟩
    rw [← h] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro z hz
      exact ⟨_, h2 z hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩

end Core

theorem mem_St_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.DIV.St β ↔ ∃ u : GL (Fin n) (Formalism.L2.Herm.intAf F E),
      u.val.map (Formalism.L2.Herm.intAf F E).subtype = (β⁻¹ * x * β).val := by
  refine exists_congr fun u => ?_
  show β * Formalism.L2.DIV.intGL F E n u * β⁻¹ = x ↔ (Formalism.L2.DIV.intGL F E n u).val = _
  rw [← Units.ext_iff]
  constructor
  · rintro rfl; group
  · intro h; rw [h]; group

theorem gLat_eq_latHat_iff : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ κ : GA D V, gLat V κ = (latHat V : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) ↔ LatticeBasisLifts.finR V hr κ ∈ Formalism.L2.DIV.St β := by
  intro D V r hr β hβ κ
  subst hr
  rw [mem_St_iff]
  exact image_eq_iff (swapAE D) (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).bijective
    (LatticeBasisLifts.OAf D) β _ (finHom V κ) rfl _ hβ

end GlobalTheory.LatStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfComplexBaseChange
section
noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isHolTo_congr_on {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : ∀ b ∈ B, y b = y' b) : IsHolTo B y ↔ IsHolTo B y' := by
  have hs : ∀ U : X.Opens, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} := fun U =>
    Set.ext fun b => ⟨fun ⟨hb, h'⟩ => ⟨hb, by rw [← h b hb]; exact h'⟩, fun ⟨hb, h'⟩ => ⟨hb, by rw [h b hb]; exact h'⟩⟩
  constructor
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [← hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩

theorem unif_of_isBC : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R]
    (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g),
    IsBC F' F σ → Nonempty (Unif F' (RingHom.id ℂ) ρ N C) → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C F' hbc hU
  obtain ⟨U'⟩ := hU
  obtain ⟨f, φ, hpb, hgp, hact, hL, heta⟩ := hbc
  have hw : φ ≫ F.A.hom = F'.A.hom ≫ f := hgp.1.w
  have hsq : f ≫ F.s = F'.s ≫ spMap σ := hpb.w
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hbase : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' h
    rw [Category.assoc, hsq, ← Category.assoc, h, hid, Category.id_comp]
  have hinj : ∀ y₁ y₂ : Sp ℂ ⟶ F'.X, y₁ ≫ F'.s = spMap (RingHom.id ℂ) → y₂ ≫ F'.s = spMap (RingHom.id ℂ) →
      y₁ ≫ f = y₂ ≫ f → y₁ = y₂ := fun y₁ y₂ h₁ h₂ h => hpb.hom_ext h (by rw [h₁, h₂])
  let exF : ∀ i P, (Fin g → ℂ) → (Over.mk (U'.u i P ≫ f) ⟶ F.A) := fun i P z =>
    Over.homMk ((U'.ex i P z).left ≫ φ) (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
  refine ⟨{
      n := U'.n, Di := U'.Di, t := U'.t, mem := U'.mem, ne := U'.ne, all := U'.all, distinct := U'.distinct
      u := fun i P => U'.u i P ≫ f, ex := exF, unif := ?_, onto := ?_, disj := ?_, fibre := ?_, hol := ?_, lift := ?_ }⟩
  · intro i P hP
    have h := U'.unif i P hP
    obtain ⟨e, he, hee⟩ := (_root_.GlobalTheory.unifAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ hgp hact hL heta (U'.Di i) (U'.t i) P
      (U'.u i P) h.1 (hbase _ h.1)).1 _ h
    have : e = exF i P := funext fun z => Over.OverMorphism.ext (by rw [hee z]; rfl)
    rw [← this]
    exact he
  · intro y hy
    obtain ⟨i, P, hP, hu⟩ := U'.onto (hpb.lift y (spMap (RingHom.id ℂ)) (by rw [hy, hid, Category.id_comp]))
      (IsPullback.lift_snd _ _ _ _)
    refine ⟨i, P, hP, ?_⟩
    show U'.u i P ≫ f = y
    rw [hu, IsPullback.lift_fst]
  · intro i j P P' hP hP' h
    exact U'.disj i j P P' hP hP' (hinj _ _ (U'.unif i P hP).1 (U'.unif j P' hP').1 h)
  · intro i P P' hP hP'
    refine Iff.trans ⟨fun h => hinj _ _ (U'.unif i P hP).1 (U'.unif i P' hP').1 h, fun h => ?_⟩ (U'.fibre i P P' hP hP')
    show U'.u i P ≫ f = U'.u i P' ≫ f
    rw [h]
  · intro i m B P hB hP
    obtain ⟨h1, h2⟩ := U'.hol i m B P hB hP
    refine ⟨(_root_.GlobalTheory.PELU.isHolTo_bc_iff R σ F.X F'.X F.s F'.s f hpb (Fin m → ℂ) B (fun b => U'.u i (P b))
      (fun b hb => (U'.unif i (P b) (hP.1 b hb)).1)).1 h1, ?_⟩
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 φ
  · intro m B y hB hy hhol b₀ hb₀
    classical
    let y' : (Fin m → ℂ) → (Sp ℂ ⟶ F'.X) := fun b =>
      if h : y b ≫ F.s = spMap σ then hpb.lift (y b) (spMap (RingHom.id ℂ)) (by rw [h, hid, Category.id_comp])
      else hpb.lift (y b₀) (spMap (RingHom.id ℂ)) (by rw [hy b₀ hb₀, hid, Category.id_comp])
    have hy'1 : ∀ b ∈ B, y' b ≫ F'.s = spMap (RingHom.id ℂ) := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_snd _ _ _ _
    have hy'2 : ∀ b ∈ B, y' b ≫ f = y b := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_fst _ _ _ _
    have hh : IsHolTo B y' := (_root_.GlobalTheory.PELU.isHolTo_bc_iff R σ F.X F'.X F.s F'.s f hpb _ B y' hy'1).2
      ((isHolTo_congr_on fun b hb => (hy'2 b hb).symm).1 hhol)
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := U'.lift m B y' hB hy'1 hh b₀ hb₀
    refine ⟨B', i, P, hB', hb', hsub, hP, fun b hb => ?_⟩
    show U'.u i (P b) ≫ f = y b
    rw [hu b hb, hy'2 b (hsub hb)]

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjComb

theorem normSq_nonneg (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (La : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    0 ≤ TaylorLogMetric.normSq D T La G := by
  unfold TaylorLogMetric.normSq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg) (MeasureTheory.integral_nonneg fun z => by positivity)

theorem supConst_nonneg (D : D7) (a b : ℕ) : 0 ≤ supConst D a b := by
  have h : 0 ≤ D.host.rdE := by
    exact Real.rpow_nonneg (by positivity) _
  unfold supConst
  positivity

theorem sq_sum_le {k : ℕ} (c f : Fin k → ℂ) (n B : ℝ) (hB : 0 ≤ B) (hc : ∑ i, ‖c i‖ ≤ n) (hf : ∀ i, ‖f i‖ ^ 2 ≤ B) :
    ‖∑ i, c i * f i‖ ^ 2 ≤ n ^ 2 * B := by
  have h1 : ‖∑ i, c i * f i‖ ≤ n * √B := by
    calc ‖∑ i, c i * f i‖ ≤ ∑ i, ‖c i * f i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * √B := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hf i)) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * √B := (Finset.sum_mul _ _ _).symm
      _ ≤ n * √B := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  calc ‖∑ i, c i * f i‖ ^ 2 ≤ (n * √B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = n ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB]

theorem conj_pres : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  intro D cc dl t0 hC ht a b L L' hL hL' hev F₀ F n hF₀ hP ρ
  obtain ⟨k, r, y, hr, hy, hn, rfl⟩ := hP
  have h := fun i => _root_.GlobalTheory.ConjTranslate.conj_translate D cc dl t0 hC ht a b L L' hL hL' hev F₀ hF₀ (y i) (hy i) ρ
  choose h1 h2 F' h3 h4 h5 using h
  have hc : GlobalTheory.ThetaConj.CjF D TaylorLogMetric.Qbar ρ (fun z => ∑ i, r i * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) (y i) F₀ z)
      (fun z => ∑ i, StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i) * F' i z) :=
    GlobalTheory.ThetaConj.CjF.sum Finset.univ fun i _ =>
      GlobalTheory.ThetaConj.CjF.mul ⟨h1 i, h3 i, fun α => ⟨h2 i α, h4 i α⟩⟩ (hr i)
  refine ⟨hc.1, fun α => (hc.2.2 α).1, _, hc.2.1, fun α => (hc.2.2 α).2, fun z => ?_⟩
  exact sq_sum_le _ _ n _
    (mul_nonneg (mul_nonneg (supConst_nonneg D a b) (normSq_nonneg _ _ _ _)) (Real.exp_pos _).le) (hn ρ) fun i => h5 i z

end GlobalTheory.ConjComb
end

