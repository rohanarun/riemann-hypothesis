module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InflationBasic
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_const_mul t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_const_mul x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsContRepKernelIntegralCompactSupport
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelContRep

theorem continuous_integral_kernel {X Z : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace Z] [T2Space Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : Measure Z) [IsFiniteMeasureOnCompacts ν] (K : X → Z → ℂ)
    (hK : Continuous fun p : X × Z => K p.1 p.2) (y : Z → ℂ) (hy : MemLp y 2 ν) (C : Set Z)
    (hC : IsCompact C) (h0 : ∀ᵐ z ∂ν, z ∉ C → y z = 0) :
    Continuous fun x => ∫ z, K x z * y z ∂ν := by
  have : IsFiniteMeasure (ν.restrict C) := ⟨by simpa using hC.measure_lt_top⟩
  have hi : Integrable y ν :=
    IntegrableOn.integrable_of_ae_notMem_eq_zero (s := C) ((hy.restrict C).integrable one_le_two) h0
  have hc : ∀ x, Continuous fun z => K x z := fun x => hK.comp (Continuous.prodMk_right x)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hU.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine continuousAt_of_dominated (bound := fun z => M * ‖y z‖) ?_ ?_ (hi.norm.const_mul M) ?_
  · exact Filter.Eventually.of_forall fun x => (hc x).aestronglyMeasurable.mul hi.1
  · filter_upwards [hx] with x hxU
    filter_upwards [h0] with z hz
    by_cases hzC : z ∈ C
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM (x, z) ⟨hxU, hzC⟩) (norm_nonneg _)
    · simp [hz hzC]
  · exact Filter.Eventually.of_forall fun z =>
      ((hK.comp (Continuous.prodMk_left z)).mul continuous_const).continuousAt

theorem ext_ae_eq_on_fund (B : RowsAut) (y : B.I.L2 B.μf B.fund) :
    B.I.ext y =ᵐ[(B.I.muA B.μf).restrict B.fund] (y : B.I.GA → ℂ) := by
  have h2 : ∀ᵐ z ∂(B.I.muA B.μf), ∀ γ ∈ B.I.GFset, γ ≠ 1 →
      γ * z ∉ (fun y => γ * y) '' B.fund ∩ B.fund := by
    refine (ae_ball_iff (GlobalTheory.RatDiscrete.countable_GFset B.I)).2 fun γ hγ => ?_
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun z h => absurd h1 h
    · filter_upwards [(GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf γ).quasiMeasurePreserving.ae
        (measure_eq_zero_iff_ae_notMem.1 (B.fund_spec.2.2 γ hγ h1))] with z hz _
      exact hz
  filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem B.fund_spec.1] with z hz hzf
  have h := B.fund_spec.2.1 z
  have e : B.I.rep B.fund z = h.choose * z := by
    unfold AutInst.rep; exact dif_pos h
  have e1 : h.choose = 1 := by
    by_contra hne
    exact hz _ h.choose_spec.1 hne ⟨⟨z, hzf, rfl⟩, h.choose_spec.2⟩
  show (y : B.I.GA → ℂ) (B.I.rep B.fund z) = _
  rw [e, e1, one_mul]

theorem isContRep_of_kernel (hA : KernelA) : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) := by
  intro B d h hd hn hl hb T hT y C hC h0
  obtain ⟨-, hK, hinv, -⟩ := hA B d h hd hn hl hb
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  have : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  refine ⟨?_, fun γ hγ x => ?_, ?_⟩
  · exact continuous_integral_kernel _ (kern B.I (phe B d)) hK _ (Lp.memLp y) C hC h0
  · simp only [(hinv γ hγ _ _).1]
  · obtain ⟨h1, h2⟩ := GlobalTheory.ConvKernel.rconv_eq_integral B _ T hT y
    have h3 := ((GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.2.2 y).1
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx2, (GlobalTheory.AdelicUnfold.integral_unfold_kernel B _ _ x h3 hx1).2]
    refine integral_congr_ae ?_
    filter_upwards [ext_ae_eq_on_fund B y] with z hz
    rw [hz]

theorem isContRep_integral_kernel : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ (y : B.I.L2 B.μf B.fund) (C : Set B.I.GA), IsCompact C → (∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0) → IsContRep B (T y) (fun x => ∫ z in B.fund, kern B.I (phe B d) x z * (y : B.I.GA → ℂ) z ∂(B.I.muA B.μf)) :=
  isContRep_of_kernel _root_.GlobalTheory.KernelConv.kernelA

end GlobalTheory.KernelContRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KappaBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeKappaL

theorem kappa_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := GlobalTheory.WedgeKappa.n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) l => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r l
  have hdual := fun J : Sub (2 * r + k + 1) l =>
    GlobalTheory.KappaDual.kappa_dual hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (lb ν) hDS hDSJ hF hT hG
      (fun s hs => (_root_.GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length k r l hl z hG.1).1 s hs) (hSF ν hν0).1 hnz J
      (lb (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) l, ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, lb ν (ev (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • lb (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) l, 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.MomMass.mom_mass hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.mass_bound_low_types hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) l) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply GlobalTheory.WedgeKappa.eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.MomLem8.moment_lemma_pieri hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • lb ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • lb (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : lb (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.quotMeas_ae_mem_and_measurable hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(_root_.GlobalTheory.FlagPartialWedge.fixes_partial_wedge_and_length k r l hl z hG.1).2 _ hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.WedgeKappaL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputs

theorem hpk_det (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem urep_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  have hu := ((uHGroup _ _ (hpk_det k r)).2.2 g hg).1
  have h := opn_mul_le g⁻¹ g
  rw [nonsing_inv_mul _ hu, opn_one] at h
  rcases (opn_nonneg g).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0] at h; linarith

theorem coef_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {a b g : Mat k r} (ha : a ∈ GG k r)
    (hb : b ∈ GG k r) (hg : g ∈ GG k r) (u v : H) :
    coef σ (σ a u) (σ b v) g = coef σ u v (b⁻¹ * g * a) := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  have hx : b⁻¹ * g * a ∈ GG k r := hmul _ (hmul _ (hinv b hb).2 _ hg) _ ha
  have e : g * a = b * (b⁻¹ * g * a) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv b hb).1, Matrix.one_mul]
  have e2 : σ g (σ a u) = σ b (σ (b⁻¹ * g * a) u) := by
    have h1 := hσ.1.2 g hg a ha
    have h2 := hσ.1.2 b hb _ hx
    rw [← e, h1] at h2
    exact congrArg (fun T : H →L[ℂ] H => T u) h2
  unfold coef
  rw [e2]
  exact (LinearIsometry.mk (σ b : H →ₗ[ℂ] H) (hσ.2.1 b hb)).inner_map_map v _

theorem decay_span {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {V : Set H} {a : ℝ} (ha : 0 ≤ a) (hσ : IsURepOn (GG k r) σ) (hV : Decay σ V a) :
    Decay σ (Submodule.span ℂ {v | ∃ g ∈ GG k r, ∃ u ∈ V, v = σ g u} : Submodule ℂ H) a := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  intro u hu v hv
  refine Submodule.span_induction₂ (p := fun u v _ _ => ∃ C : ℝ, ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro _ _ ⟨x, hx, u, hu, rfl⟩ ⟨y, hy, v, hv, rfl⟩
    obtain ⟨C, hC⟩ := hV u hu v hv
    have hK : 0 < opn y * opn x⁻¹ := mul_pos (opn_pos hy) (opn_pos (hinv x hx).2)
    refine ⟨|C| * (opn y * opn x⁻¹) ^ a, fun g hg => ?_⟩
    have hm : y⁻¹ * g * x ∈ GG k r := hmul _ (hmul _ (hinv y hy).2 _ hg) _ hx
    rw [coef_translate hσ hx hy hg]
    have e : g = y * (y⁻¹ * g * x) * x⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv y hy).1, Matrix.one_mul,
        Matrix.mul_assoc, mul_nonsing_inv _ (hinv x hx).1, Matrix.mul_one]
    have h1 : opn g ≤ opn y * opn x⁻¹ * opn (y⁻¹ * g * x) := by
      calc opn g = opn (y * (y⁻¹ * g * x) * x⁻¹) := by rw [← e]
        _ ≤ opn (y * (y⁻¹ * g * x)) * opn x⁻¹ := opn_mul_le _ _
        _ ≤ opn y * opn (y⁻¹ * g * x) * opn x⁻¹ :=
          mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _)
        _ = _ := by ring
    have h2 := Real.rpow_le_rpow_of_nonpos (opn_pos hg) h1 (neg_nonpos.2 ha)
    rw [Real.mul_rpow hK.le (opn_nonneg _)] at h2
    have hp := opn_pos hm
    calc _ ≤ |C| * opn (y⁻¹ * g * x) ^ (-a) :=
          (hC _ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      _ = |C| * (opn y * opn x⁻¹) ^ a * ((opn y * opn x⁻¹) ^ (-a) * opn (y⁻¹ * g * x) ^ (-a)) := by
          rw [mul_assoc |C|, ← mul_assoc (_ ^ a), ← Real.rpow_add hK]; simp
      _ ≤ _ := by gcongr
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_left, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_right, norm_mul, norm_star, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

theorem gap_of_nodes (D : D7) (τ : D.what₂.Tau) (h : ℝ) (hanti : StrictAnti (lamD D τ))
    (hb : ∀ j, 1 ≤ j → j + 1 ≤ D.R.m → h ≤ bOne D τ (j + 1) - bOne D τ j) :
    GapAtLeast (epsSH D.R) (lamD D τ) h := by
  have hd := dimS_eq D.R
  have hm := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have step : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1), D.R.k - 1 ≤ i →
      h ≤ lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := by
    intro i hi hk
    have h0 := hb (i - (D.R.k - 1) + 1) (by omega) (by omega)
    unfold bOne at h0
    rw [dite_eq_left (by omega), dite_eq_left (by omega)] at h0
    unfold lamD lamSH lamS
    simp only [Fin.val_cast]
    rw [dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
    have e : i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 := by omega
    simp only [e, Nat.add_sub_cancel] at h0 ⊢
    linarith
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      h ≤ lamD D τ a - lamD D τ b := by
    intro a b hab hne
    have hab' : a.val < b.val := hab
    have hb' := b.isLt
    by_cases ha : D.R.k - 1 ≤ a.val
    · have h1 := step a.val (by omega) ha
      have h2 := hanti.antitone (show (⟨a.val + 1, by omega⟩ : Fin _) ≤ b from hab')
      simp only [Fin.eta] at h1
      linarith
    · have hbk : D.R.k ≤ b.val := by
        by_contra hc
        apply hne
        unfold epsSH epsS
        simp only [Fin.val_cast]
        rw [if_pos (by omega)]
        split_ifs
        · rfl
        · have : b.val - (D.R.k - 1) = 0 := by omega
          simp [this]
      have h1 := step (b.val - 1) (by omega) (by omega)
      have h2 := hanti.antitone (show a ≤ (⟨b.val - 1, by omega⟩ : Fin _) from by
        show a.val ≤ b.val - 1; omega)
      have e : (⟨b.val - 1 + 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) = b := Fin.ext (by simp only; omega)
      rw [e] at h1
      linarith
  intro a b hne
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact (key a b h1 hne).trans (le_abs_self _)
  · exact absurd (by rw [h1]) hne
  · rw [abs_sub_comm]; exact (key b a h1 hne.symm).trans (le_abs_self _)

theorem decay_low (hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow) {k r : ℕ} (hk : 1 ≤ k) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hg : GapAtLeast ε lam (((2 * r + k + 1 : ℕ) : ℝ) ^ 19))
    {P : Mat k r} (hP : IsCayleyU k r ε P) :
    Decay σ (lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5) := by
  intro u hu v hv
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hr : 2 * ((r : ℝ) + 1) ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hn]; push_cast; linarith
  have hn2 : 2 ≤ n := by have : (0 : ℝ) ≤ r := by positivity
                         linarith
  have h13 : (120 : ℝ) ≤ n ^ 13 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 13)
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have hh : 120 * n ^ 3 ≤ n ^ 19 := by
    have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
    rw [this]; gcongr
  obtain ⟨C, hC⟩ := hD k r hk ε lam (n ^ 19) H σ hl hσ hg hh P hP u v hu hv
  have hs : Real.sqrt (2 * ((r : ℝ) + 1)) ≤ n := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hs0 : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := by positivity
  have he : 2 * n ^ 5 ≤ n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by
    rw [le_div_iff₀ (by positivity)]
    calc 2 * n ^ 5 * (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ 2 * n ^ 5 * (8 * n) := by gcongr
      _ = 16 * n ^ 6 := by ring
      _ ≤ n ^ 13 * n ^ 6 := by gcongr; linarith
      _ = _ := by ring
  obtain ⟨K, hK, hc⟩ := GlobalTheory.SOrb.CCBridge.opn_gN_compare k r
  refine ⟨|C| * K ^ |-(2 * n ^ 5)|, fun g hg => ?_⟩
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have h2 : Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) ≤ K ^ |-(2 * n ^ 5)| * opn g ^ (-(2 * n ^ 5)) :=
    GlobalTheory.SOrb.CCBridge.rpow_compare hK _ (by linarith) (opn_pos hg) (hc g).2 (hc g).1
  calc _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
        (hC g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

end GlobalTheory.Amp.LocalInputs
end

