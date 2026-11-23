module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmulMemLocPPerO
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.PeriodTwist

open GlobalTheory.ThetaMove.PeriodComp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem smul_mem_locP_perO (AA : Submodule (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E a)} (hN : N.FG)
    {N' M' : Submodule (𝓞 E) (Sp E b)} (k : E) (h : ∀ y ∈ localization₂ Q.asIdeal N', k • y ∈ localization₂ Q.asIdeal M')
    {x : HomE E a b} (hx : x ∈ localization₂ Q.asIdeal (perO AA N N')) : k • x ∈ localization₂ Q.asIdeal (perO AA N M') := by
  have key : ∀ z ∈ perO AA N N', k • z ∈ localization₂ Q.asIdeal (perO AA N M') := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨r, hr, x, hx, rfl⟩ := hz
      obtain ⟨s, hs, hsx⟩ := exists_common Q.asIdeal.primeCompl hN M' (k • x) fun y hy =>
        h _ (mem_localization_of_mem Q (hx _ hy))
      refine ⟨s, hs, ?_⟩
      rw [smul_comm k r, smul_comm s r]
      exact smul_mem_perO hr hsx
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
  obtain ⟨s, hs, hx⟩ := hx
  rw [← localization_localization₂]
  exact ⟨s, hs, by rw [smul_comm]; exact key _ hx⟩

theorem twO_perO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), N.FG → 0 < c → (∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) → twist₂ (perO AA N N') c e = perO AA N (twist₂ N' c e) := by
  intro E _ _ _ a b AA N N' c e hN hc he
  have hk : ∀ Q, ((c : E) ^ e Q) ≠ 0 := fun Q => zpow_ne_zero _ (by exact_mod_cast hc.ne')
  apply le_antisymm
  · intro x hx
    refine mem_of_locP fun Q => ?_
    have h1 := (mem_localization_twist _ hc he Q x).1 (mem_localization_of_mem Q hx)
    have h2 := smul_mem_locP_perO AA Q hN (M' := twist₂ N' c e) ((c : E) ^ e Q) (fun y hy => by
      rw [mem_localization_twist _ hc he, inv_smul_smul₀ (hk Q)]; exact hy) h1
    rwa [smul_inv_smul₀ (hk Q)] at h2
  · intro x hx
    refine mem_of_locP fun Q => ?_
    rw [mem_localization_twist _ hc he]
    exact smul_mem_locP_perO AA Q hN _ (fun y hy => (mem_localization_twist _ hc he Q y).1 hy) (mem_localization_of_mem Q hx)

end GlobalTheory.ThetaMove.PeriodTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

private theorem szRow_eleven_le_splitBound : SzRow (fun _ D _ => 11 ≤ D.host.splitBound) := by
  intro eps heps _ C _
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨(11 : ℝ) ^ (eps / C.P.Cpde / 5)⁻¹, ?_⟩⟩⟩
  intro D L hε hx hV
  have hH := hV.host
  have hC : (0 : ℝ) < C.P.Cpde := lt_of_lt_of_le one_pos hH.one_le
  have ha : 0 < eps / C.P.Cpde / 5 := by positivity
  have h1 : (11 : ℝ) ≤ L.sc.x ^ (eps / C.P.Cpde / 5) := by
    have h2 := Real.rpow_le_rpow (by positivity) hx ha.le
    rwa [Real.rpow_inv_rpow (by norm_num) ha.ne'] at h2
  have h3 : L.sc.x ^ (eps / C.P.Cpde / 5) ≤ L.sc.x ^ (L.sc.ez / 5) := by
    refine Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_
    have := hH.eps_div_le_ez
    rw [hε] at this
    linarith
  have h4 : 11 ≤ ⌊L.sc.x ^ (L.sc.ez / 5)⌋₊ := Nat.le_floor (by exact_mod_cast h1.trans h3)
  exact h4.trans hH.split_tie

theorem szRow_sizesAt : SzRow (fun _ _ L => SizesAt L) := by
  have h := ((((((((((_root_.GlobalTheory.EX.szRow_rankSizes.and _root_.GlobalTheory.EX.szRow_sizeKRel).and _root_.GlobalTheory.EX.szRow_cond_qd_pde).and _root_.GlobalTheory.EX.szRow_la_rho_bot).and _root_.GlobalTheory.EX.szRow_sizeEta).and
    _root_.GlobalTheory.EX.szRow_sizeNodes).and _root_.GlobalTheory.EX.szRow_sizeLstar).and _root_.GlobalTheory.EX.szRow_sizeDel).and _root_.GlobalTheory.EX.szRow_sizeW_sizeBm_sizeXpp).and _root_.GlobalTheory.EX.szRow_sizeG_sizeWords).and
    szRow_eleven_le_splitBound)
  refine h.imp ?_
  rintro C cD ch D L - - ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN, hM, hK, hT, hTT, hDe, hLw⟩, hKR⟩, hCo, hQD, hP⟩, hLa, hRho, hBot⟩, hEta⟩,
    hNo⟩, hLs⟩, hDel⟩, hW, hBm, hX⟩, hG, hWo⟩, h11⟩
  exact ⟨hN, hM, hK, hKR, hT, hCo, hQD, hTT, hLa, hRho, hBot, hDe, hLw, hEta, hNo, hLs, hDel, hW, hBm, hX, hG,
    hP, hWo, h11⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryExpLieBallComparableEntryGauge
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.ExpBallCompare

variable {P Q : ℕ}

theorem entry_le_l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i j) : ‖Z i j‖ ≤ l1 Z :=
  (Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

theorem l1_add_le (Z W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    l1 (Z + W) ≤ l1 Z + l1 W := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem l1_neg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : l1 (-Z) = l1 Z := by
  simp [l1]

theorem exists_l1_ball {S : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} (hS : S ∈ 𝓝 0) :
    ∃ δ > 0, ∀ Z, l1 Z < δ → Z ∈ S := by
  have hS' : S ∈ 𝓝 (0 : (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) := hS
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hS'
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  exact mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 fun i => (pi_norm_lt_iff hδ).2 fun j =>
    (entry_le_l1 Z i j).trans_lt hZ)

theorem exp_isLittleO (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (fun Z : A => NormedSpace.exp Z - 1 - Z) =o[𝓝 0] fun Z => Z := by
  have h := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)).isLittleO
  simpa using h

theorem eventually_l1_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ in 𝓝 0,
      l1 (NormedSpace.exp Z - 1 - Z) ≤ ε * l1 Z := by
  let : NormedRing (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := FiniteDimensional.complete ℂ _
  have hrow : ∀ (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i, ∑ j, ‖Z i j‖ ≤ ‖Z‖ := by
    intro Z i
    rw [Matrix.linfty_opNorm_def]
    have := Finset.le_sup (f := fun i => ∑ j, ‖Z i j‖₊) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa using h2
  have h1 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z ≤ (P + Q : ℝ) * ‖Z‖ := by
    intro Z
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => ∑ j, ‖Z i j‖) ‖Z‖ fun i _ => hrow Z i
    simpa [l1] using this
  have h2 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, ‖Z‖ ≤ l1 Z := by
    intro Z
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i => ∑ j, ‖Z i j‖₊) ≤ ∑ i, ∑ j, ‖Z i j‖₊ :=
      Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa [l1] using h2
  have hN : (0 : ℝ) < P + Q + 1 := by positivity
  have h3 := (exp_isLittleO (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).def (div_pos hε hN)
  filter_upwards [h3] with Z hZ
  calc l1 (NormedSpace.exp Z - 1 - Z) ≤ (P + Q : ℝ) * ‖NormedSpace.exp Z - 1 - Z‖ := h1 _
    _ ≤ (P + Q + 1 : ℝ) * (ε / (P + Q + 1) * ‖Z‖) :=
      mul_le_mul (by linarith) hZ (norm_nonneg _) hN.le
    _ = ε * ‖Z‖ := by field_simp
    _ ≤ ε * l1 Z := mul_le_mul_of_nonneg_left (h2 Z) hε.le

theorem exists_l1_exp {t : ℝ} (ht : 1 < t) : ∃ δ > 0,
    ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z < δ →
      l1 (NormedSpace.exp Z - 1) ≤ t * l1 Z ∧ l1 Z ≤ t * l1 (NormedSpace.exp Z - 1) := by
  have ht0 : 0 < t := by linarith
  have hε : 0 < 1 - t⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ht)
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball
    ((eventually_l1_exp (P := P) (Q := Q) hε).and (eventually_l1_exp (sub_pos.2 ht)))
  refine ⟨δ, hδ, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := h Z hZ
  constructor
  · have := l1_add_le (NormedSpace.exp Z - 1 - Z) Z
    rw [sub_add_cancel] at this
    linarith
  · have := l1_add_le (NormedSpace.exp Z - 1) (-(NormedSpace.exp Z - 1 - Z))
    rw [l1_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    have h3 : t⁻¹ * l1 Z ≤ l1 (NormedSpace.exp Z - 1) := by linarith
    exact (inv_mul_le_iff₀ ht0).1 h3

theorem exists_gauge_ball {S : Set (UpqT P Q)} (hS : S ∈ 𝓝 (1 : UpqT P Q)) :
    ∃ δ > 0, ∀ g, gauge g < δ → g ∈ S := by
  rw [GlobalTheory.UpqTopology.isClosedEmbedding_mat.isInducing.nhds_eq_comap] at hS
  obtain ⟨T, hT, hTS⟩ := hS
  have h1 : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  have c : Continuous fun Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Z + 1 :=
    continuous_id.add continuous_const
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball (c.continuousAt.preimage_mem_nhds (x := 0) (t := T)
    (by rw [zero_add, ← h1]; exact hT))
  refine ⟨δ, hδ, fun g hg => hTS ?_⟩
  simpa using h _ hg

theorem expBall_compare : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  intro P Q t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδ, h⟩ := exists_l1_exp (P := P) (Q := Q) ht
  obtain ⟨η, hη, h'⟩ := exists_gauge_ball (GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds P Q δ hδ)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hη)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrδ : r < δ := hr1.trans_le (min_le_left _ _)
  have hrη : r < η := hr1.trans_le (min_le_right _ _)
  constructor
  · rintro g ⟨X, hX, hg⟩
    have hX' : l1 (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) < t⁻¹ * r := hX
    have h1 : t⁻¹ * r ≤ r := mul_le_of_le_one_left hr0.le (inv_lt_one_of_one_lt₀ ht).le
    have h2 := (h X (by linarith)).1
    have h3 := (lt_inv_mul_iff₀ ht0).1 hX'
    show l1 (UpqT.mat g - 1) < r
    rw [hg]
    linarith
  · intro g hg
    have hg' : l1 (UpqT.mat g - 1) < r := hg
    obtain ⟨X, hX, hgX⟩ := h' g (lt_trans hg hrη)
    refine ⟨X, ?_, hgX⟩
    have h2 := (h X hX).2
    rw [hgX] at hg'
    exact h2.trans_lt (mul_lt_mul_of_pos_left hg' ht0)

end GlobalTheory.ExpBallCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem natW_alcove_bound (p : ℕ) (N : ℕ) (lam : DomWeight N)
    (hl : ∀ i j : Fin N, i < j → lam.w i - lam.w j + ((j : ℕ) - (i : ℕ) : ℤ) ≤ (p : ℤ)) :
    ∀ h : 0 < N, lam.natW ⟨N - 1, by omega⟩ = 0 ∧ lam.natW ⟨0, h⟩ + (N - 1) ≤ p := by
  intro h
  obtain ⟨_, h2, h3⟩ := factNatW N lam
  refine ⟨h3 h, ?_⟩
  have e0 := h2 ⟨0, h⟩
  have e1 := h2 ⟨N - 1, by omega⟩
  rw [h3 h] at e1
  by_cases hN1 : N = 1
  · subst hN1
    have : (⟨0, h⟩ : Fin 1) = ⟨1 - 1, by omega⟩ := rfl
    rw [this, h3 h]
    omega
  · have hlt : (⟨0, h⟩ : Fin N) < ⟨N - 1, by omega⟩ := Fin.mk_lt_mk.mpr (by omega)
    have := hl _ _ hlt
    simp only at this
    have hc : ((N - 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by omega
    push_cast at this
    omega

theorem inducedSimpleLowestAlcove : GlobalTheory.Published.InducedSimpleLowestAlcove := by
  intro p hp k _ _ N lam hl
  have hN := factNatW N lam
  have hne : nablaSq k N lam ≠ ⊥ := by
    intro h
    have hm : hw k le_rfl lam.natW ∈ nablaSq k N lam := hwMem k N N le_rfl _ hN.1
    rw [h, Submodule.mem_bot] at hm
    exact hwNe k N N le_rfl _ hm
  refine ⟨hne, fun M hM hG => ?_⟩
  by_contra hc
  push_neg at hc
  have key := _root_.GlobalTheory.Alc.hw_mem_of_lt p hp k N lam.natW hN.1 (natW_alcove_bound p N lam hl)
  have good := _root_.GlobalTheory.Alc.good_nablaSq_and_submodules k N lam
  have h1 := (key ⊥ M (good_top_bot k N N).2 (good.2 M hG) (bot_lt_iff_ne_bot.2 hc.1) hM).1
  have h2 := (key M (nablaSq k N lam) (good.2 M hG) good.1 (lt_of_le_of_ne hM hc.2) le_rfl).2
  exact h2 h1

end GlobalTheory.Alc
end

