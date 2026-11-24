module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.DualIrr

theorem dual_irr : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro D V θ c hθ hc N hN

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (atTau θ V τ g')⁻¹ = atTau θ V τ g := by
    intro τ g hg
    have hu : IsUnit (gramAt D V τ).det := by
      have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [this]
      exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
    have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    set gi := (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ with hgi
    have h2 : gi * g = 1 := by
      rw [hgi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
    have h3 : g * gi = 1 := mul_eq_one_comm.1 h2
    have hgi' : gi ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      show giᴴ * gramAt D V τ * gi = gramAt D V τ
      calc giᴴ * gramAt D V τ * gi = giᴴ * (gᴴ * gramAt D V τ * g) * gi := by rw [h1]
        _ = (g * gi)ᴴ * gramAt D V τ * (g * gi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [h3]; simp
    refine ⟨gi, hgi', ?_⟩
    have e : atTau θ V τ g * atTau θ V τ gi = 1 := by
      rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hgi', h3, GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ]
    rw [eq_inv_of_mul_eq_one_right e, inv_inv]
  set U := N.dualCoannihilator with hUdef
  have hstab : ∀ a ∈ GinfC V, ∀ v ∈ U, c.ρ a v ∈ U := by
    intro a ha
    refine Submonoid.closure_induction (motive := fun a _ => ∀ v ∈ U, c.ρ a v ∈ U) ?_ ?_ ?_
      (Formalism.IndefR.TopMult.ginf_mem_closure hθ ha)
    · rintro x ⟨τ, g, hg, rfl⟩ v hv
      obtain ⟨g', hg', e⟩ := hinv τ g hg
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro f hf
      have := hv _ (hN τ g' hg' f hf)
      rw [e] at this
      simpa [LinearMap.dualMap_apply] using this
    · intro v hv; simpa using hv
    · intro x y _ _ hx hy v hv
      rw [map_mul, Module.End.mul_apply]
      exact hx _ (hy v hv)
  have hU : ∀ u ∈ GinfC V, U.map (c.ρ u) ≤ U := by
    rintro u hu _ ⟨v, hv, rfl⟩
    exact hstab u hu v hv
  have hN' : U.dualAnnihilator = N := Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases GlobalTheory.GenRealSchur.irr_real c hc U hU with h | h
  · right; rw [← hN', h, Submodule.dualAnnihilator_bot]
  · left; rw [← hN', h, Submodule.dualAnnihilator_top]

end GlobalTheory.DualIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainLValuesNeZeroAndParamsInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto.ChainVal

variable {D : D7}

abbrev vf (χ : (AE D)ˣ →* Circle) : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := GlobalTheory.LFun.val (F := D.host.F) χ

theorem twist_sum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → GlobalTheory.LFun.Fam K)
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) : GlobalTheory.LFun.twist (∑ i ∈ s, f i) z = ∑ i ∈ s, GlobalTheory.LFun.twist (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => funext w; simp [GlobalTheory.LFun.twist]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.LFun.twist_add, ih]

theorem stepPar_same (χ : (AE D)ˣ →* Circle) (t : ℕ) (B : GlobalTheory.LFun.Fam D.host.E) :
    GlobalTheory.ChainOnto.stepPar χ χ t B = B + GlobalTheory.LFun.segFam (vf χ) t := by
  funext w; simp [GlobalTheory.ChainOnto.stepPar, GlobalTheory.LFun.segFam, vf]

theorem chainPar_closed (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    chainPar c B k = B + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i)) c.t := by
  induction k with
  | zero => simp [chainPar]
  | succ k ih => rw [chainPar_succ, ih, stepPar_same, Finset.sum_range_succ, add_assoc]

theorem chainPar_twist (c : Com D) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) :
    GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹ =
      GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ + ∑ i ∈ Finset.range k, GlobalTheory.LFun.segFam (vf (c.χ i * (c.χ k)⁻¹)) c.t := by
  rw [chainPar_closed, GlobalTheory.LFun.twist_add, twist_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.LFun.twist_segFam]
  congr 1
  funext w; simp [vf, mul_comm]

theorem locL_finsetSum {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K)
    (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single {K : Type} [Field K] [NumberField K] (T : Set (HeightOneSpectrum (𝓞 K)))
    (z : HeightOneSpectrum (𝓞 K) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 :=
  fun w _ => ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {K : Type} [Field K] [NumberField K] {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K)))
    (A : GlobalTheory.LFun.Fam K) (s : Finset ι) (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ)
    (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end GlobalTheory.EvenOnto.ChainVal


open GlobalTheory.EvenOnto.ChainVal in
theorem GlobalTheory.EvenOnto.chainL_and_inj : ∀ D : D7, ChainL D ∧ ∀ (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)), chainPar c B k w = chainPar c B' k w → B w = B' w := by
  intro D
  refine ⟨?_, ?_⟩
  · intro c hc B hB k hk
    set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
    have hnt : c.n + 2 ≤ c.t := hc.step
    have hnt' : (c.n : ℝ) + 2 ≤ c.t := by exact_mod_cast hnt
    have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.range k → Differentiable ℂ Λ ∧
        (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
          (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.χ i * (c.χ k)⁻¹) w}) z) ∧
        ∀ n : ℕ, 1 ≤ n → Λ n ≠ 0 := by
      intro i
      by_cases hi : i ∈ Finset.range k
      · obtain ⟨Λ, h⟩ := GlobalTheory.T.quotient_char_partial_L_entire_nonvanishing_integers D c hc i k (Finset.mem_range.1 hi) hk
        exact ⟨Λ, fun _ => h⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose Λ hΛ using hΛ
    set A := GlobalTheory.LFun.twist B (vf (c.χ k))⁻¹ with hA
    have hAb : GlobalTheory.LFun.Bounded T A c.n (((c.n : ℝ) - 1) / 2) :=
      hB.twist fun w _ => by simp [vf, GlobalTheory.LFun.norm_val]
    let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => vf (c.χ i * (c.χ k)⁻¹)
    have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
      (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
    let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
      ∏ i ∈ Finset.range k, ∏ l ∈ Finset.range c.t, Λ i (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l)
    have hEq : ∀ x : ℂ, ((c.n : ℝ) + c.t + 2) < x.re →
        H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.χ k) (x + 1 / 2) := by
      intro x hx
      have hre : ∀ l : ℕ, l < c.t → 1 < (x + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l).re := by
        intro l hl
        have : (l : ℝ) + 1 ≤ c.t := by exact_mod_cast hl
        have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _
        simp
        linarith
      show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
        (GlobalTheory.LFun.val (F := D.host.F) (c.χ k))⁻¹) (x + 1 / 2)
      change _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k) (vf (c.χ k))⁻¹) (x + 1 / 2)
      rw [chainPar_twist, ← hA, eulerProd_add_segFam T A (Finset.range k) z c.t (x + 1 / 2)
        (hAb.converges (by have hr0 : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _; simp; linarith))
        (fun i _ l hl => hzc i _ (hre l hl))]
      refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi =>
        Finset.prod_congr rfl fun l hl => ?_)
      exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
    have hU : IsOpen (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
    have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2)) := by
      refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
      · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
        simp only [GlobalTheory.Cont.mem_rightOf] at hx
        simp
        linarith
      · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
          (hΛ i hi).1.comp (by fun_prop)
    have hAn := hD.analyticOnNhd hU
    have hmem : ((c.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf ((c.n : ℝ) / 2) := by
      simp only [GlobalTheory.Cont.mem_rightOf]
      simp
      linarith
    refine ⟨H ((c.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
      (c.n : ℝ) + c.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
    refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
    · simp
      linarith
    · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      have e : (c.t : ℂ) / 2 + 1 / 2 + ((c.t : ℂ) - 1) / 2 - l = ((c.t - l : ℕ) : ℂ) := by
        rw [Nat.cast_sub hl'.le]
        ring
      rw [e]
      exact (hΛ i hi).2.2 _ (by omega)
  · intro c k B B' w h
    induction k with
    | zero => simpa [chainPar] using h
    | succ k ih =>
      apply ih
      rw [chainPar_succ, chainPar_succ] at h
      simp only [GlobalTheory.ChainOnto.stepPar] at h
      have h2 := add_right_cancel h
      exact Multiset.map_injective (mul_right_injective _) h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem parIndep_even : ∀ D : D7, ParIndep D := by
  intro D c hc j hj s hs ι x B hpar hB
  classical
  rw [linearIndependent_iff']
  intro t a hsum i₀ hi₀
  obtain ⟨hne0, _⟩ := hpar i₀
  obtain ⟨v, hv⟩ : ∃ v, PiLocalization₂.val (x i₀) v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne0
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simpa [PiLocalization₂.val] using h w
  let p : ι → Prop := fun i => PiLocalization₂.val (x i) v ≠ 0
  let f : {i // p i} → (GA D s.V → ℂ) := fun i g => conj (PiLocalization₂.val (x i.1) v g)
  have hli : LinearIndependent ℂ f := by
    refine GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV D s.V c.S {i // p i} f (fun i => B i.1) ?_ ?_ ?_
    · intro i h0
      apply i.2
      funext g
      have := congrFun h0 g
      simpa [f] using this
    · intro i
      exact (hpar i.1).2 v i.2
    · intro i i' hii'
      exact hB i.1 i'.1 (fun h => hii' (Subtype.ext h))
  rw [linearIndependent_iff'] at hli
  have hsum' : ∀ g, ∑ i ∈ t, a i * PiLocalization₂.val (x i) v g = 0 := by
    intro g
    have := congrArg (fun y : s.CC c => PiLocalization₂.val y v g) hsum
    simpa [PiLocalization₂.val, Finset.sum_apply] using this
  have key := hli (t.subtype p) (fun i => conj (a i.1)) ?_ ⟨i₀, hv⟩ (by simp [Finset.mem_subtype, hi₀])
  · simpa using key
  · funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, f, Pi.zero_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun i => conj (a i) * conj (PiLocalization₂.val (x i) v g)) (p := p)]
    rw [Finset.sum_filter_of_ne]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [← map_zero (starRingEnd ℂ), ← hsum' g, map_sum]
        exact Finset.sum_congr rfl (fun i _ => (map_mul (starRingEnd ℂ) _ _).symm)
    · intro i _ hne h0
      apply hne
      simp [h0]

theorem eig_parOfVal_indep : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → EigSpan D ∧ ParOfVal D ∧ ParIndep D := by
  intro hC D hF hM
  refine ⟨?_, ?_, parIndep_even D⟩
  · intro c hc j hj s hs
    have hspan := _root_.GlobalTheory.EvenOntoDecomp.cc_span_partFull hC D hF c hc j hj s hs
    have hpar := _root_.GlobalTheory.EvenOnto.partPar hC D c hc j hj s hs
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 ?_
    rintro u ⟨e, he⟩
    by_cases h0 : u = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ((hpar u e he).1 h0)
  · intro c hc j hj s hs x w B hv hf
    obtain ⟨e, he⟩ := _root_.GlobalTheory.EvenOnto.ValPart.valPart_mem hC D hM c hc j hj s hs x w B hv hf
    exact (_root_.GlobalTheory.EvenOnto.partPar hC D c hc j hj s hs x e he).2 w B hv hf

end GlobalTheory.EvenOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoeffici
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.MeasPet

variable {D : D7}


open GlobalTheory.ChainOnto.HaarInf in
theorem meas_petco : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  intro D c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  let K : Subgroup (GA D V) := s.J
  let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
  let A : Subgroup (GA D V) := Lf.comap (GlobalTheory.AutMult.toFin V)
  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg => Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hg)
  have hAset : (A : Set (GA D V)) = s.big := by
    ext g
    refine ⟨fun hg => ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩, ?_⟩
    rintro ⟨b, κ, hκ, rfl⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
    have e : GlobalTheory.AutMult.toFin V (κ : GA D V) = ⟨κ, hs.fin hκ⟩ := GlobalTheory.AutMult.toFin_coe (⟨κ, hs.fin hκ⟩ : GfC V)
    rw [map_mul, GlobalTheory.AutMult.toFin_coe_inf, one_mul, e]
    exact hκ
  have hLf : IsOpen (Lf : Set (GfC V)) := by
    obtain ⟨U, hU, hUK⟩ := hs.isOpen
    refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
    exact Subgroup.mem_subgroupOf.2 (hUK _ (Subgroup.mem_subgroupOf.1 hk) k.2)
  have hAopen : IsOpen (A : Set (GA D V)) := hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)
  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact hs.stab _ (hfinK g hg) v
  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen
  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    constructor
    · rintro ⟨hgA, hgf⟩
      have := hfinK g hgA
      rwa [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hgf⟩ : GfC V))] at this
    · intro hg
      refine ⟨?_, hs.fin hg⟩
      refine Subgroup.mem_comap.2 (Subgroup.mem_subgroupOf.2 ?_)
      rw [show (GlobalTheory.AutMult.toFin V g : GA D V) = g from congrArg Subtype.val (GlobalTheory.AutMult.toFin_coe (⟨g, hs.fin hg⟩ : GfC V))]
      exact hg
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.ChainOnto.isCompact_of_integral_open D V s.Λ hs.selfDual K hs.fin hs.stab hs.isOpen
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    rw [← SetLike.mem_coe, hAset]
    exact ⟨b, 1, one_mem _, by simp⟩
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨⟨hIopen.measurableSet, hAset ▸ hAopen.measurableSet, hAset ▸ hAint, _, hHaar, fun f F hf hF => ?_⟩, ?_⟩
  · have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
      (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
    have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
      conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
      exact hF _ _ (hfinK g hg)
    have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
      (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
    rw [← hAset]
    refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
    rw [setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]
  · intro ipD ip hM u v b κ hκ
    have hmem := (mem_multT c.θ s.M (s.J : Set (GA D V)) 1 (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ))).1 u.2
    have hmap := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    obtain ⟨w, hw, hU⟩ := GlobalTheory.ChainOnto.mult_equiv_real D c.θ s.V s.par s.M (s.J : Set (GA D V)) 1 hc.inf v b
    have hUw := hU _ hmem
    have ev : ∀ x : s.M.Vec, PiLocalization₂.val u (PiTensorProduct.tprod ℂ x) =
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D V → ℂ)) x := by
      intro x; simp [PiLocalization₂.val, PiTensorProduct.lift_symm]
    have key : rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        PiLocalization₂.val u (PiTensorProduct.tprod ℂ w) := by
      funext g
      rw [ev, ev, hUw]
      simp only [rTr]
      rw [← mul_assoc]
      simpa using hmap.lev v κ hκ (g * (b : GA D s.V))
    have hsch : s.pet (PiLocalization₂.val u (PiTensorProduct.tprod ℂ w)) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) =
        ip u u * ipD (PiTensorProduct.tprod ℂ w) (PiTensorProduct.tprod ℂ v) := hM.schur u u _ _
    rw [key, hsch, hM.pure w v]
    simp only [hw]

end GlobalTheory.EvenOnto.MeasPet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCharpolyKernelEqStableOrbitalIntegralsStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → Integrable (descend (ratPts σ J) (polKernel P J (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf v) (ff v)) * ∏ w, Phi (J := J) (μa w) (dta w) (fa w) := by
  first | exact @GlobalTheory.TrEll.integral_polKernel | exact GlobalTheory.TrEll.integral_polKernel | (intros; apply GlobalTheory.TrEll.integral_polKernel <;> assumption)
end

