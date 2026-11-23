module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

namespace GlobalTheory.LevelSupBound

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm GlobalTheory.SupremumSobolevWords GlobalTheory.HeisTaylor
open scoped NNReal Topology

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem word_theta_level (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {u : WO S T} (h0 : u.map (infPart D) = 0) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
      heisO ψ S T u f = f → IsThetaFunO ψ S T (wordAct (heisDer ψ θ) l f) ∧
        heisO ψ S T u (wordAct (heisDer ψ θ) l f) = wordAct (heisDer ψ θ) l f := by
  intro l
  induction l with
  | nil => exact fun hf hu => ⟨hf, hu⟩
  | cons a l ih =>
    intro f hf hu
    obtain ⟨h1, h2⟩ := ih hf hu
    have e : wordAct (heisDer ψ θ) (a :: l) f = dv θ σ S T (letter a) (wordAct (heisDer ψ θ) l f) := by
      rw [dv_letter hc hψ]
      rfl
    rw [e]
    exact ⟨theta_dv hc hψ _ h1, dv_level hc hψ _ h0 h2⟩

theorem sobO_word_le (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (p : ℕ) (f : WO S T → ℂ),
      sobO ψ θ μ 𝓕 p (wordAct (heisDer ψ θ) l f) ≤ sobO ψ θ μ 𝓕 (p + l.length) f := by
  intro l
  induction l with
  | nil => intro p f; simp [wordAct]
  | cons a l ih =>
    intro p f
    refine (sobO_heisDer_le p a).trans ?_
    refine (ih (p + 1) f).trans_eq ?_
    congr 1
    simp only [List.length_cons]
    omega

theorem nsmul_fin {u : WO S T} (hinf : u.map (infPart D) = 0) (n : ℕ) : (n • u).map (infPart D) = 0 := by
  ext i j
  have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
  exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))

theorem pointwise (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T))
    (hK₀ : IsCompact K₀) :
    ∃ C : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ y : WO S T,
        ‖f y‖ₑ ≤ ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ Module.finrank ℝ (RW T S)) *
          sobO ψ θ μ 𝓕 (Module.finrank ℝ (RW T S)) f := by
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  set N := Module.finrank ℝ (RW T S) with hN
  let b : Module.Basis (Fin N) ℝ (RW T S) := Module.finBasis ℝ (RW T S)
  obtain ⟨c, hcube⟩ := cube_dilate_bound_at hψ hc b h0 hK₀
  let card : ℝ≥0 := Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
  let Q : ℝ≥0 := 1 + card * ‖fun i => b i‖₊
  refine ⟨NNReal.sqrt (4 ^ N * c) * Q ^ N, fun μ 𝓕 hm n hn f hf hl y => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, sobO ψ θ μ 𝓕 N f = s :=
    ⟨_, (ENNReal.coe_toNNReal (sobO_ne_top hψ hθ hm.1 hm.2.1 hf N)).symm⟩
  let ρ : ℝ≥0 := (n : ℝ≥0) * ‖fun i => b i‖₊
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ (ρ : ℝ)) ∧ F = (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • n • b i)) A (c * ((1 + card * ρ) ^ N * s : ℝ≥0) ^ 2) y
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ f ⟨[], le_rfl, by simp, rfl⟩
  · have hQ : 1 + card * ρ ≤ Q * n := by
      have h1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast hn
      calc 1 + card * ρ ≤ n + card * ρ := add_le_add h1 le_rfl
        _ = Q * n := by simp only [Q, ρ]; ring
    have key' : (‖f y‖₊ : ℝ≥0) ^ 2 ≤ 4 ^ N * (c * ((1 + card * ρ) ^ N * s) ^ 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      simpa using key
    have hb : (‖f y‖₊ : ℝ≥0) ≤ NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s := by
      rw [← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero]
      refine key'.trans ?_
      have e : (NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N * s) ^ 2 = 4 ^ N * (c * ((Q * n) ^ N * s) ^ 2) := by
        rw [mul_assoc, mul_assoc, mul_pow (NNReal.sqrt _), NNReal.sq_sqrt]
        ring_nf
      rw [e]
      gcongr
    rw [hs, enorm_eq_nnnorm]
    have e2 : ENNReal.ofReal (((NNReal.sqrt (4 ^ N * c) * Q ^ N : ℝ≥0) : ℝ) * (n : ℝ) ^ N) =
        ((NNReal.sqrt (4 ^ N * c) * Q ^ N * (n : ℝ≥0) ^ N : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    rw [e2, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hb
  · rintro p _ ⟨l, h1, h2, rfl⟩
    refine ⟨(wd l).2.cont, fun i => ⟨_, ⟨l ++ [n • b i], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (n • b i) (wd l).2⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        refine norm_nsmul_le.trans ?_
        simp only [ρ, NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => b i) i) (Nat.cast_nonneg n)
    · simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    refine (hcube μ 𝓕 hm n hn _ (wd l).2 (fun u hu hinf => ?_) y).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2) c.coe_nonneg)
    · exact words_level hc hψ (nsmul_fin hinf n) l ⟨f, hf⟩ (hl u hu hinf)
    · refine ENNReal.toReal_le_coe_of_le_coe ((l2O_foldl_dvL_le_pow_mul_sobO hc hψ N l (by simpa using h1) h2 _).trans ?_)
      rw [hs, ← ENNReal.coe_pow, ← ENNReal.coe_mul]

theorem supN_word_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X : HSp D) (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k B : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ f : WO V X → ℂ, IsThetaFunO ψ V X f →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) f = f) →
      ∀ l : List (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool),
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l f) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ B) * GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k + l.length) f := by
  intro D ψ hψ θ hθ V X K₀ h0 hK₀ μ 𝓕 hm
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨C, hC⟩ := pointwise (S := V) (T := X) hψ hθ h0 hK₀
  refine ⟨Module.finrank ℝ (RW X V), Module.finrank ℝ (RW X V), C, C.2, fun n hn f hf hl l => iSup_le fun y => ?_⟩
  have hw := fun u hu hinf => word_theta_level hc hψ (nsmul_fin (S := V) (T := X) hinf n) l hf (hl u hu hinf)
  have ht : IsThetaFunO ψ V X (wordAct (heisDer ψ θ) l f) :=
    (hw 0 (mem_of_mem_nhds h0) (Matrix.map_zero _ (map_zero _))).1
  refine (hC μ 𝓕 hm n hn _ ht (fun u hu hinf => (hw u hu hinf).2) y).trans ?_
  exact mul_le_mul' le_rfl (sobO_word_le μ 𝓕 l _ f)

end GlobalTheory.LevelSupBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointKeepsSphericalPartsOffTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KeptRows
open GlobalTheory.Hk3

section Transfer
open Polynomial GlobalTheory.Hk3.SplitChain
open _root_.Formalism.L2.Col (heckePolyOf blockPoly)

theorem blockPoly_ne_zero (ν : ℂ) (q t : ℕ) : blockPoly ν q t ≠ 0 := by
  intro h
  have h0 : Polynomial.eval 0 (blockPoly ν q t) = 1 := by
    unfold blockPoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro c _
    simp
  rw [h, eval_zero] at h0
  exact zero_ne_one h0


set_option maxHeartbeats 1000000 in
theorem transfer_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hL : GlobalTheory.Chain.LiftInteg D) (hC : Core R F) (hS : SchurAll R) (t : T) (P : Pl D.host.E) (hG : Good R t P)
    (hP : Formalism.DivisionValues.conjPl P ≠ P) :
    ∃ (z : ℕ → ℕ → ℂ) (c : ℂ) (B : ℂ[X]), c ≠ 0 ∧ B ≠ 0 ∧
      (∀ k, k ≤ D.sp.X'.rank → MatchE R t P (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧
      ∀ a : ℕ → ℂ, heckePolyOf D.sp.X'.rank (Ideal.absNorm P.asIdeal)
          (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) =
        (heckePolyOf (Yc D 0).rank (Ideal.absNorm P.asIdeal) a).comp (C c * X) * B := by
  obtain ⟨q, hq⟩ : ∃ q, q = Ideal.absNorm P.asIdeal := ⟨_, rfl⟩
  rw [← hq]
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨-, g2, -, -⟩ := _root_.GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hG' := (g2 t _ hG).2.1
  obtain ⟨u1, u2⟩ := _root_.GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hG
  obtain ⟨v1, v2⟩ := _root_.GlobalTheory.UnrOffLevels.unrPl_of_good R F hC.lev t _ hG'
  have hm := D.R.two_le_m
  have hP' : conjPl (conjPl P) ≠ conjPl P := by rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]; exact hP.symm
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt (conjPl P) (by
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hP' (HeightOneSpectrum.ext h))
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ (conjPl P).asIdeal, ϖ ∉ (conjPl P).asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ (conjPl P).ne_bot (conjPl P).isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) :=
    ⟨Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), by
      rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩
  have hY : ∀ j, j ≤ D.R.m → (Yc D j).rank = D.R.r + j * D.R.t := fun j hj => by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl
  have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
  have hn : ∀ j, D.R.r + (j + 1) * D.R.t = D.R.r + j * D.R.t + D.R.t := fun j => by ring
  let μ := R.toLevCh.mu t
  let ν : ℕ → ℂ := fun i => (((Lift.chrStep μ R.eta (i + 1)).1 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + i * D.R.t))⁻¹
  let s : ℕ → ℂ := fun i => ν i * (((Lift.chrStep μ R.eta (i + 1)).2 x : ℂ) * (Real.sqrt q : ℂ) ^ (D.R.r + (i + 1) * D.R.t))
  obtain ⟨W, w0, w1⟩ := exists_chain D.R.m (fun j => D.R.r + j * D.R.t)
    fun j => stepMat q (D.R.r + j * D.R.t) D.R.t (ν j) (s j)
  have hmm : D.R.m - 1 + 1 = D.R.m := by omega
  have hfix : FixAll R t P := by
    refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
    · have := unrPl_step (u2 (k + 1) (by omega) hk.le) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωY t k hk) hP this.1 this.2).1
    · have := unrPl_step (u2 D.R.m (by omega) le_rfl) u1
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.chain.ωX t) hP this.1 this.2).1
    · have := u2 ((i : ℕ) + 1) (by omega) i.2
      exact (GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace _ _ _ _ _ _ _ (hC.thP.ωP i t) hP this (unrPl_mul_inv this u1)).1
  have hσ : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0)))
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    mul_ne_zero (inv_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ)))
      (mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ hσ))
  refine ⟨W 0, ∏ i ∈ Finset.Ico 0 D.R.m, s i,
    ∏ i ∈ Finset.Ico 0 D.R.m, blockPoly (ν i * (q : ℂ) ^ (D.R.r + i * D.R.t) * ∏ l ∈ Finset.Ico (i + 1) D.R.m, s l) q D.R.t,
    Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Finset.prod_ne_zero_iff.2 fun i _ => blockPoly_ne_zero _ _ _,
    fun k hk => ?_, fun a => ?_⟩
  · rw [hY 0 (Nat.zero_le _)]
    refine _root_.GlobalTheory.Hk3.ChainE.matchE_of_chain R F hL hC hS t _ hG hfix _ (fun j => splitC (D.R.r + j * D.R.t) (W j k)) ?_ fun j hj => ?_
    · have hW := hC.chain.ωX t
      have h3 := step_match (ν := ν (D.R.m - 1)) (s := s (D.R.m - 1)) hW hP (unrPl_step (u2 D.R.m (by omega) le_rfl) u1)
        (unrPl_step (v2 D.R.m (by omega) le_rfl) v1) he h1 h2 hx (hY _ (Nat.sub_le _ _)) hX
        (by rw [← hn, hmm]) hq (by simp only [ν, hmm, μ]) (by simp only [s, hmm, μ]) (W D.R.m k)
      rw [funext (w0 k), ← hX, splitC_delta hk] at h3
      have h4 := funext (w1 (D.R.m - 1) (by omega) k)
      simp only [hmm] at h4
      rw [funext (w0 k), ← hX] at h4
      simp only [h4]
      exact h3
    · have h3 := step_match (ν := ν j) (s := s j) (hC.chain.ωY t j hj) hP (unrPl_step (u2 (j + 1) (by omega) hj.le) u1)
        (unrPl_step (v2 (j + 1) (by omega) hj.le) v1) he h1 h2 hx (hY _ (by omega)) (hY _ hj.le)
        (hn j) hq rfl rfl (W (j + 1) k)
      simp only [funext (w1 j (by omega) k)]
      exact h3
  · have h3 := chain_poly q D.R.t D.R.m (fun j => D.R.r + j * D.R.t) hn ν s W w0 w1 D.R.m 0 (zero_add _) a
    rw [hX, hY 0 (Nat.zero_le _), h3]

end Transfer


set_option maxHeartbeats 1000000 in
theorem kept : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Core R F → (∀ t P, Good R t P → Formalism.DivisionValues.conjPl P = P → FixAll R t P) → Kept R := by
  intro hCR hHU D G _ _ Pl0 T A Ks _ _ _ R F hC hFix t c x hx
  have hS : SchurAll R := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R
  have hLI := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCR D
  have H1 := GlobalTheory.Hk3.OpsRowsTuple.exists_ops_tuple R F hC hS t
  cases H1 with
  | intro h H2 =>
  have hh := H2.1
  have hn := H2.2.1
  have he := H2.2.2.1
  have hin := H2.2.2.2
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, map_zero]
    exact Submodule.zero_mem _
  have hxe : ∀ P, Good R t P → ∀ cc, h P cc x = evC (Yc D 0) P (fun d => c P (dualLab d)) cc • x :=
    fun P hP cc => he c P hP cc x hx
  have hmatch : ∀ P, Good R t P → ∀ cX c0, MatchE R t P cX c0 →
      h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • R.Th t (LinearMap.adjoint (R.Th t) x) :=
    fun P hP cX c0 hM => _root_.GlobalTheory.Hk3.SysE.matched_keeps_eigen R F hC t h hh hn P hP cX c0 hM x _ (hxe P hP c0)
  have evS : ∀ P d, IsLab (Yc D 0) P d →
      evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single d 1) = c P (dualLab d) := by
    intro P d hd
    unfold evC
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]
  have gp := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hsplit : ∀ P, Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank,
      h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) (R.Th t (LinearMap.adjoint (R.Th t) x)) =
        evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) •
          R.Th t (LinearMap.adjoint (R.Th t) x) := by
    intro P hP hs k hk
    have HZ := transfer_good R F hLI hC hS t P hP hs
    cases HZ with
    | intro z Hz =>
    cases Hz with
    | intro c0 Hz =>
    cases Hz with
    | intro B Hz =>
    have hz := Hz.2.2.1
    have hq : Ideal.absNorm P.asIdeal ≠ 0 := fun e => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    have hspan := GlobalTheory.SpanPoly.single_splitLab_mem_span _ _ _ hq c0 Hz.1 B Hz.2.1 z Hz.2.2.2 k hk
    refine GlobalTheory.EigSpan.eig_span R F hC t h hh _ hP _ _ _ ?_ _ hspan
    rintro _ ⟨j, hj, rfl⟩
    exact hmatch _ hP _ _ (hz j hj)
  refine hin c (R.Th t (LinearMap.adjoint (R.Th t) x)) fun P d hP hd => ?_
  by_cases hs : Formalism.DivisionValues.conjPl P = P
  · have HM := (GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hHU R F hLI hC hS t P hP hs (hFix t P hP hs)).1.2
      (Finsupp.single d 1)
    cases HM with
    | intro cX hM =>
    have e1 := hmatch P hP cX _ hM
    exact e1.trans (congrArg (fun z : ℂ => z • R.Th t (LinearMap.adjoint (R.Th t) x)) (evS P d hd))
  · have hcP : Good R t (Formalism.DivisionValues.conjPl P) := (gp.2.1 t P hP).2.1
    have hcs : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) ≠ Formalism.DivisionValues.conjPl P := by
      rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P]
      exact fun e => hs e.symm
    exact GlobalTheory.Hk3.SplitLabels.eq_of_split_vec R F hC t h hh P hP hs c x _ hx0 hxe (fun k hk => ⟨hsplit P hP hs k hk, hsplit _ hcP hcs k hk⟩) d hd

end GlobalTheory.KeptRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.PolMul

open GlobalTheory.HeisDeriv GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def liftInf (z : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z)

theorem evI_liftInf (z : mixedEmbedding.mixedSpace F) : evI F (liftInf F z) = z := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = z
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem mul_liftInf_eq_zero {a : AF F} (ha : evI F a = 0) (z : mixedEmbedding.mixedSpace F) :
    a * liftInf F z = 0 := by
  have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ha)
  refine Prod.ext ?_ ?_
  · show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    rw [mul_zero]

theorem actsD_mult {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (y : Fin n × Fin d → AF F) (hu : M.co.e u = (0, y))
    (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f) := by
  intro r _ x

  have he : ∀ t : ℝ, M.co.e (realAd F t • u) = (0, realAd F t • y) := by
    intro t
    rw [LinearEquiv.map_smul, hu]
    refine Prod.ext ?_ ?_ <;> simp
  set a : AF F := x ⬝ᵥ y with ha
  set K : ℂ := tens (evI F) (⇑f) r x with hK
  set c : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) with hc

  have hT : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) (⇑f) r) x = ψ (realAd F t * a) * K := by
    intro t
    simp only [Model.heisLine, Darboux.rho, he t, schr, zero_dotProduct, mul_zero, add_zero, dotProduct_smul,
      smul_eq_mul, ha, hK]

  have hAt : ∀ t : ℝ, At (evI F) (realAd F t * a) := by
    intro t v hv
    rw [smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero hv, zero_mul]
  have hψt : ∀ t : ℝ, ψ (realAd F t * a) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) := by
    intro t
    rw [hψ.2.2 _ (hAt t), evI_mul, evI_realAd, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hfun : (fun t : ℝ => M.heisLine ψ u t (tens (evI F) (⇑f) r) x) =
      fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (((t * c : ℝ)) : ℂ)) * K := by
    funext t
    rw [hT t, hψt t]
  have h0 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ)) ((1 * c : ℝ) : ℂ) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp
  have h2 := ((h0.const_mul (-(2 * Real.pi * Complex.I))).cexp).mul_const K

  have htr : trForm F y (fun i => evI F (x i)) = c := by
    rw [trForm_apply, hc, ha, dotProduct, evI_sum]
    simp only [evI_mul]
  rw [hfun]
  refine h2.congr_deriv ?_
  simp only [tens, hK, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr, zero_mul,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, smul_eq_mul]
  ring

theorem model_mul {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (F := F) E w)
    (q : Fin n × Fin d → mixedEmbedding.mixedSpace F) (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ τ) :
    ∃ f₁ ∈ M.Pol ψ τ, ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q : ℂ) * f x := by

  set y : Fin n × Fin d → AF F := fun i => liftInf F (q i) with hy
  set u := M.co.e.symm (0, y) with hu
  have hue : M.co.e u = (0, y) := by simp [hu]
  have hat : At (evI F) u := by
    intro v hv
    rw [← LinearEquiv.map_eq_zero_iff M.co.e, LinearEquiv.map_smul, hue]
    refine Prod.ext ?_ ?_
    · simp
    · funext i
      simp [hy, mul_liftInf_eq_zero hv]
  have hmem : SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f ∈ M.Pol ψ τ := by
    rw [Model.Pol, Submodule.mem_sInf] at hf ⊢
    intro N hN
    exact hN.2 u hat f (hf N hN) _ (actsD_mult M ψ hψ u y hue f)
  have hne : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨(-(2 * Real.pi * Complex.I))⁻¹ • SchwartzMap.smulLeftCLM ℂ (⇑(mult F y)) f,
    Submodule.smul_mem _ _ hmem, fun x => ?_⟩
  have htr : trForm F y x = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x q := by
    rw [trForm_apply, GlobalTheory.GaussLine.pairInf_apply]
    simp only [hy, evI_liftInf]
  rw [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (mult F y).hasTemperateGrowth, mult_apply, htr,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end GlobalTheory.PolMul

theorem GlobalTheory.PolMul.pol_mul_pairInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT q f hf
  exact GlobalTheory.PolMul.model_mul G.M B.ψ hT.base.std B.emb q f hf

end
end

