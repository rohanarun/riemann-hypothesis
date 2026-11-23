module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierTransformCosetIndicatorEqFiniteColumnTran
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.TwBridge.TopHat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hat_coset_box [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (c : kˣ) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i * (c : k) ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n c) (Submodule.Quotient.mk y₀)) η =
      ((nabs k c ^ Fintype.card n : ℝ) : ℂ) * ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n c) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => cball c).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n c) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => cball c := by
      simp [Submodule.Quotient.eq, mem_box, cball]
    by_cases h : y ∈ Set.pi Set.univ fun _ => cball c
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := by
        refine mul_mem hε (sum_mem fun i _ => ?_)
        have h1 : valuation k (y i) ≤ valuation k (c : k) := h i trivial
        have h2 := (Valuation.mem_integer_iff _ _).1 (hη i)
        rw [Valuation.mem_integer_iff, map_mul]
        rw [map_mul] at h2
        calc valuation k (η i) * valuation k (y i) ≤ valuation k (η i) * valuation k (c : k) := mul_le_mul' le_rfl h1
          _ ≤ 1 := h2
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_cball c).measurableSet), Measure.real,
    Measure.pi_pi]
  simp only [measure_cball ν c, hν.2, mul_one, Finset.prod_const, Finset.card_univ]
  simp [nabs, ENNReal.toReal_pow]

theorem hat_coset_eq_ftY : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → 2 * cst.M ≤ cst.D P →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e →
    ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)) (y' : Sp X.E (R.N (s + 1))), (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' l)) →
      hat W.ψ ν (-1) (cosetInd (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun a => ι (y' (e' a)))) ((toLoc ι e e' y) (Sum.inr ())) =
        σ₀ (ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y') := by
  classical
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν _ hA hD e' e _ he y y' hy'
  haveI := hν.1
  have hint : ∀ a : X.E, ι a ∈ 𝒪[k] ↔ IntAt P.1 a := hA.compl.int
  have hlast : (e (Sum.inr ())).val = R.N R.m - 1 := he (Sum.inr ())
  have hNpos : R.N R.m - 1 < R.N R.m := by have := (e (Sum.inr ())).isLt; omega
  set η' := atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y with hη'
  have hη'v : ∀ v, η' v = y v (e (Sum.inr ())) := fun v => by
    simp only [hη', LinearMap.comp_apply, atNL, dif_pos hNpos, LinearMap.proj_apply]
    rw [show (⟨R.N R.m - 1, hNpos⟩ : Fin (R.N R.m)) = e (Sum.inr ()) from Fin.ext hlast.symm]
  have hrow : (toLoc ι e e' y) (Sum.inr ()) = fun a => ι (η' (Pi.single (e' a) 1)) := by
    funext a; simp [toLoc, hη'v]
  have hsum : η' y' = ∑ i, y' i * η' (Pi.single i 1) := by
    have : y' = ∑ i, y' i • Pi.single i (1 : X.E) := by ext j; simp [Pi.single_apply]
    conv_lhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  have hdot : (fun a => ι (η' (Pi.single (e' a) 1))) ⬝ᵥ (fun a => ι (y' (e' a))) = ι (η' y') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum, dotProduct]
    exact Fintype.sum_equiv e' _ _ (fun a => by simp [mul_comm])
  have hϖ : (W.ϖ : k) = ι (qOf P.1 : X.E) := hA.compl.unif
  have hcM : ((W.ϖ ^ cst.M : kˣ) : k) = ι ((qOf P.1 : X.E) ^ cst.M) := by
    rw [Units.val_pow_eq_pow_val, hϖ, map_pow]
  rw [hrow, ftY, if_neg hA.nmem]
  by_cases hη : ∀ i : Fin (R.N (s + 1)), IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))
  · rw [if_pos hη, hat_coset_box W.cond hν (neg_mem (one_mem _)) _ _ (fun a => ?_), hdot]
    · have hres : resCard k = qOf P.1 := ComplRes.resCard_eq hA.compl W.unif
      obtain ⟨p, hp, hpϖ⟩ := GlobalTheory.PeriodicIntegral.exists_irreducible_of_isUnif W.unif
      have hnabs : nabs k W.ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
      have hnM : nabs k (W.ϖ ^ cst.M) = ((qOf P.1 : ℝ) ^ cst.M)⁻¹ := by
        rw [show nabs k (W.ϖ ^ cst.M) = nabs k W.ϖ ^ cst.M by simp [nabs], hnabs, hres, inv_pow]
      have hcard : Fintype.card (XIx (Fin R.k) (Fin R.t) (s + 1)) = R.N (s + 1) := by
        simpa using Fintype.card_congr e'
      have hqi : ∀ j, ι ((qOf P.1 : X.E) ^ j) ∈ 𝒪[k] := fun j => by
        rw [map_pow, map_natCast]; exact pow_mem (natCast_mem _ _) _
      have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η' y')) := by
        rw [← hint, hsum]
        obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + 2 * cst.M := ⟨_, (Nat.sub_add_cancel hD).symm⟩
        have : (qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ i, y' i * η' (Pi.single i 1)) =
            -((qOf P.1 : X.E) ^ d *
              ∑ i, ((qOf P.1 : X.E) ^ cst.M * y' i) * ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single i 1))) := by
          rw [hd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [epsSg, Int.cast_neg, Int.cast_one]
          ring
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_neg, map_mul, map_sum]
        exact neg_mem (mul_mem (hqi _) (sum_mem fun i _ => by
          rw [map_mul]; exact mul_mem ((hint _).2 (hy' i)) ((hint _).2 (hη i))))
      have h1 := hA.psi _ hi
      have h2 : ι ((epsSg : X.E) * η' y') = -1 * ι (η' y') := by simp [epsSg]
      rw [map_mul σ₀, ← h1, h2, map_inv₀, map_pow, map_natCast, hnM, hcard]
      push_cast
      rw [inv_pow, ← pow_mul]
    · rw [show (fun a => ι (η' (Pi.single (e' a) 1))) a * ((W.ϖ ^ cst.M : kˣ) : k) =
        ι ((qOf P.1 : X.E) ^ cst.M * η' (Pi.single (e' a) 1)) by rw [hcM, ← map_mul, mul_comm]]
      exact (hint _).2 (hη _)
  · rw [if_neg hη, map_zero]
    by_contra hne
    have hm := mul_mem_of_hat_cosetInd_ne_zero k W.ψ W.cond ν _ (W.ϖ ^ cst.M) (-1) _ _ hne
    refine hη fun i => (hint _).1 ?_
    have h' := neg_mem (hm (e'.symm i))
    convert h' using 1
    rw [map_mul, ← hcM]
    simp only [Equiv.apply_symm_apply]
    ring

end GlobalTheory.TwBridge.TopHat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtSobolevThetaFormHeisenbergAlongRealLin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

noncomputable section

namespace GlobalTheory.MatCoeffDeriv

open GlobalTheory.FockCompare

theorem hasDerivAt_form_heisO_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∀ w : WO S T, HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) (ℓ (heisO ψ S T w (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)) - deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * ℓ (heisO ψ S T w f)) 0 := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf w
  have hL : IsRealDir T S M := ⟨hM, hMf⟩
  have hg : IsThetaFunO ψ S T (heisO ψ S T w f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  set g := heisO ψ S T w f with hg_def
  set c : ℝ → ℂ := fun s => ψ (symplOH S T w (M s)) with hc_def

  have lsub : ∀ a b, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b → ℓ (a - b) = ℓ a - ℓ b := by
    intro a b ha hb
    have := hℓ.add (a - b) b (GlobalTheory.OrientedHeis.theta_sub ha hb) hb
    rw [sub_add_cancel] at this
    rw [this]; ring

  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hce : c = fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
      (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) := by
    funext s
    show ψ (symplOH S T w (M s)) = _
    rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 M hL s, GlobalTheory.OrientedHeis.psi_symplOH h hψ, map_smul]
    rfl
  have hcd : HasDerivAt c (deriv c 0) 0 := by
    refine DifferentiableAt.hasDerivAt ?_
    have h2 : ContDiff ℝ ∞ fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
        (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.mul contDiff_const)))
    rw [hce]
    exact h2.differentiable (by simp) 0
  have hc0 : c 0 = 1 := by
    show ψ (symplOH S T w (M 0)) = 1
    rw [M.map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, ψ.map_zero_eq_one]
  have hcne : ∀ s, c s ≠ 0 := by
    intro s; rw [hce]; exact Complex.exp_ne_zero _

  have hF : ∀ s, heisO ψ S T (w + M s) f = c s • heisO ψ S T (M s) g := by
    intro s
    rw [hg_def, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul,
      GlobalTheory.FinTranslate.symplOH_skew (S := S) (T := T) w (M s), add_neg_cancel, ψ.map_zero_eq_one, one_smul, add_comm]

  obtain ⟨U, hUo, hUl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hUo
  have key := ((_root_.GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ S T d g hg).2 M hM hMf).2
  have hmemM : ∀ t, heisO ψ S T (M t) g ∈ GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
    ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (M t),
      fun u hu h0 => GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)⟩
  have hmemg : g ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hUl⟩
  have hmemd : GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
    refine ⟨GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hg, fun u hu h0 => ?_⟩
    funext p
    have : (fun t => heisO ψ S T (M t) g p) = fun t => heisO ψ S T u (heisO ψ S T (M t) g) p := by
      funext t; rw [GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)]
    conv_rhs => unfold GlobalTheory.OrientedHeis.dLine; rw [this]
    unfold GlobalTheory.OrientedHeis.dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  have hG : HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) (ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff, tendsto_iff_edist_tendsto_0]
    have hφ : ∀ t : ℝ, (t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g ∈
        GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)) hmemd
    have he : ∀ t : ℝ, edist (slope (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) 0 t - ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0
        = ‖ℓ ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)‖ₑ := by
      intro t
      rw [edist_zero_right, lsub _ _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)).1 hmemd.1,
        hℓ.smul _ _ (Submodule.sub_mem _ (hmemM t) hmemg).1, lsub _ _ (hmemM t).1 hg, slope_def_module,
        sub_zero, M.map_zero, GlobalTheory.WeilVacMove.heisO_zero, Complex.real_smul, Complex.ofReal_inv]
    simp_rw [he]
    have hT : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * supSob ψ θ d ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) -
        GlobalTheory.OrientedHeis.dLine ψ S T M g)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) key (Or.inr ENNReal.coe_ne_top)
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le)
      (fun t => hC _ (hφ t))

  set f' : WO S T → ℂ := fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0 with hf'_def
  have hf'θ : IsThetaFunO ψ S T f' := GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hf
  have hdl : GlobalTheory.OrientedHeis.dLine ψ S T M g = heisO ψ S T w f' - (2 * deriv c 0) • g := by
    funext p
    set H : ℝ → ℂ := fun s => heisO ψ S T w (heisO ψ S T (M s) f) p with hH_def
    have hHd : HasDerivAt H (heisO ψ S T w f' p) 0 := by
      have hd := (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL hf (p + w) 0).differentiableAt.hasDerivAt
      exact hd.const_mul (ψ (symplOH S T p w))
    have hH0 : H 0 = g p := by
      show heisO ψ S T w (heisO ψ S T (M 0) f) p = heisO ψ S T w f p
      rw [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
    have hEq : (fun s : ℝ => heisO ψ S T (M s) g p) = fun s => (c s)⁻¹ * ((c s)⁻¹ * H s) := by
      funext s
      have e1 : H s = c s * heisO ψ S T (w + M s) f p := by
        show heisO ψ S T w (heisO ψ S T (M s) f) p = _
        rw [GlobalTheory.OrientedHeis.heisO_heisO]; rfl
      rw [e1, hF s, Pi.smul_apply, smul_eq_mul]
      field_simp [hcne s]
    have hci := hcd.inv (by rw [hc0]; exact one_ne_zero)
    have hD := hci.mul (hci.mul hHd)
    have hD' : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) g p) _ 0 :=
      hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => congrFun hEq s)
    show deriv (fun s : ℝ => heisO ψ S T (M s) g p) 0 = _
    rw [hD'.deriv]
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hH0]
    ring

  have hfun : (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) = fun s => c s * ℓ (heisO ψ S T (M s) g) := by
    funext s
    rw [hF s, hℓ.smul _ _ (hmemM s).1]
  rw [hfun]
  have hP := hcd.mul hG
  refine hP.congr_deriv ?_
  rw [hdl, lsub _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf'θ w) (GlobalTheory.OrientedHeis.theta_smul _ hg),
    hℓ.smul _ _ hg, hc0]
  simp only [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  ring

end GlobalTheory.MatCoeffDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqOneOfTrivialSplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

theorem heckeChar_eq_one_of_split : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  intro D ν hν hs
  obtain ⟨N, hN, hA⟩ := _root_.GlobalTheory.HeckeSplitAll.char_trivial_modSet D ν hν.1
  have hH : grpH D N ≤ ν.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ((⟨k, rfl⟩ | ⟨e, he, hx⟩) | hx)
    · exact hν.2 k
    · exact hs e he x hx
    · exact hA x hx
  have hcl : closure (grpH D N : Set (AE D)ˣ) ⊆ ν.ker := by
    refine closure_minimal hH ?_
    have : (ν.ker : Set (AE D)ˣ) = ν ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hν.1
  intro x
  obtain ⟨z, hz, hxz⟩ := _root_.GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem D N hN x
  have h1 : ν (x * z⁻¹) = 1 := hH hxz
  have h2 : ν z = 1 := hcl (GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one D N hN z hz)
  have : x = x * z⁻¹ * z := by group
  rw [this, map_mul, h1, h2, one_mul]

end GlobalTheory.HeckeSplitAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
section
namespace I195MixedCoordinates_5a743adb4eaabe3d936622f8

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_5a743adb4eaabe3d936622f8

public noncomputable abbrev _root_.I195MixedCoordinates_0bc2bf51bedd9bcbcf543475.source :=
  @_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisMixSource

theorem heis_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f x) ∧ (∀ x w, (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w ((_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  intro D ψ hψ S S₀ T ρ d v f hf
  have hψc : Continuous ψ := hψ.1.1
  refine ⟨fun x a => GlobalTheory.MixModel.Check.mixS_heis_extX d v.μ v.𝓕 f a x, fun x a => ?_,
    fun x w => GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part d v.μ v.𝓕 f w x, ?_, fun w => ?_⟩
  · funext w₀
    exact GlobalTheory.MixModel.Check.mixS_heis_extY d v.covol hf a x w₀
  · have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
    have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
    have h0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
    have K := _root_.GlobalTheory.Unf.ParCont.parCont D T.rank ρ v (Mx D T.rank ρ × WO S₀ T)
      (fun a p => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) ?_
      (fun γ hγ x p => d.integrandS_periodic hf p.1 p.2 γ hγ x)
    · exact K.2.1
    · have e : (Function.uncurry fun (a : Mx D T.rank ρ) (p : Mx D T.rank ρ × WO S₀ T) =>
          heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) =
          fun q => ψ (symplOH S T (d.extY T q.1) (d.extX T q.2.1)) *
            f (d.extY T q.1 + d.extX T q.2.1 + d.ext0 T q.2.2) := by
        funext q; exact d.integrandS_eq f q.2.1 q.1 q.2.2
      rw [e]
      exact (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_fst)
        (hX.comp (continuous_fst.comp continuous_snd)))).mul
        (hf.cont.comp (((hY.comp continuous_fst).add (hX.comp (continuous_fst.comp continuous_snd))).add
          (h0.comp (continuous_snd.comp continuous_snd))))
  · have hg0 : heisO ψ S T (d.ext0 T w) f 0 = f (d.ext0 T w) := by
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · have hz := (_root_.GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d v.μ v.𝓕 v.covol f
      haveI : Subsingleton (Matrix (Fin T.rank) (Fin 0) D.host.E) := ⟨fun a b => Matrix.ext fun _ j => j.elim0⟩
      have h1 : ∀ x : Matrix (Fin T.rank) (Fin 0) D.host.E, (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f (rat x) w = f (d.ext0 T w) :=
        fun x => congrFun (hz (rat x)) w
      rw [show (fun x : Matrix (Fin T.rank) (Fin 0) D.host.E => (_root_.I195MixedCoordinates_5a743adb4eaabe3d936622f8.source d) T ψ v.μ v.𝓕 f (rat x) w) =
        fun _ => f (d.ext0 T w) from funext h1]
      exact hasSum_single (f := fun _ : Matrix (Fin T.rank) (Fin 0) D.host.E => f (d.ext0 T w))
        (0 : Matrix (Fin T.rank) (Fin 0) D.host.E) fun b hb => absurd (Subsingleton.elim b 0) hb
    · obtain ⟨hsplit, hrat, hYe, hXe, -, hres, -, -, -⟩ := _root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
      have hg : IsThetaFunO ψ S T (heisO ψ S T (d.ext0 T w) f) :=
        (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hf
      have hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) v.μ v.𝓕 := hrat ▸ v.covol
      have hG := GlobalTheory.MixModel.gram_conjTranspose S
      have c1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * S.gram * d.e' = 1 := by
        have h := congrArg Matrix.conjTranspose d.e'e
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
      have c2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.e' = 0 := d.e'e'
      have c3 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.i₀ = 0 := by
        have h := congrArg Matrix.conjTranspose d.i₀e'
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
      have H := (GlobalTheory.TwFour.value_zero_eq_sum_restrictions D S S₀ T ρ d.e d.e' d.i₀ (hsplit hρ) c1 c2 c3 ψ hψ
        v.μ v.𝓕 hcov _ hg).2
      rw [hg0] at H
      convert H using 1
      funext y
      rw [hXe, ← hres]
      change d.mixS T ψ v.μ v.𝓕 f (rat y) w =
        d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) (rat y) 0
      rw [GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part]
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

end GlobalTheory.HeisMixSource
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualAtSumLattice
section
noncomputable section
open scoped Matrix Classical TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.Inhab
variable {D : D7}

section Generic

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) {n m k : Type}

variable [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq m] [DecidableEq k]

end Generic

section Lattice

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable {L' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}

end Lattice

section Frame

variable {T T' : HSp D} {t : ℕ} (d : HypDec T T' t)

variable (c : Mx D T'.rank T'.rank)

end Frame

theorem exists_good (V : HSp D) : ∃ l : Lvl V, l.Good :=
  let ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj V
  ⟨⟨frameLat V, a⟩, isLattice_frameLat_host V, SelfDual.isSelfDualAt_frameLat D V, ha⟩

end GlobalTheory.RegSch.Inhab
end
end

