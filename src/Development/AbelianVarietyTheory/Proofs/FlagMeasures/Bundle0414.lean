module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyRecursionStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0015
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularGe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMajorantLengthMomentLowestKType
section
noncomputable section

namespace GlobalTheory.MomOneGap

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

variable {k r : ℕ}

theorem lev_zero_of_wt (hH : HypsG) (hk : 1 ≤ k) {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Q : Mx k r}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hE : R.IsE Q E) (S : Submodule ℂ R.H) (hfin : FiniteDimensional ℂ S)
    (hst : PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S)
    (hmax : ∀ (μ : Fin (2 * r + k + 1) → ℝ) (v : R.H), v ∈ S → v ≠ 0 →
      PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) μ v →
      PI.UpqRep.CDom ε μ (Formalism.QuantumDeterminants.lowK ε mu))
    (w : R.smSub) (hwS : (w : R.H) ∈ S)
    (hw : PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) (fun g => R.σ (Q⁻¹ * g * Q)) (Formalism.QuantumDeterminants.lowK ε mu) (w : R.H)) :
    Lev ε E mu 0 w := by
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hDS : R.IsDS ε mu := GlobalTheory.isDS_of_isDG hR
  obtain ⟨-, hS2⟩ := GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r ε mu R hDS Q hQ S hfin hst
  obtain ⟨hw1, hw2⟩ := GlobalTheory.TorusWeight.torus_weight_action hK k r ε mu R hDS Q E hQ hE (Formalism.QuantumDeterminants.lowK ε mu) w hw
  have hMod := Gp91.GlobalTheory.T.cayley_endomorphisms_modular hH k r ε mu R hk hR Q E hQ hE
  refine GlobalTheory.lev_zero_of_kHighest _ _ _ E _ w hMod.1 hMod.2.1 ⟨hw1, ?_⟩ ?_
  · intro a b hab he
    by_contra h0
    have hmem : ((E a b w : R.smSub) : R.H) ∈ S := by
      rw [hE a b w]; exact hS2 a b he _ hwS
    have h0' : ((E a b w : R.smSub) : R.H) ≠ 0 := fun h => h0 (Subtype.ext h)
    exact GlobalTheory.DominantRootSums.not_cDom_add_root _ ε _ a b hab (hmax _ _ hmem h0' (hw2 a b))
  · have hle : Formalism.REAL.kSpan ε E w ≤ S.comap R.smSub.subtype := by
      refine sInf_le ⟨hwS, ?_⟩
      intro a b he x hx
      show ((E a b x : R.smSub) : R.H) ∈ S
      rw [hE a b x]; exact hS2 a b he _ hx
    have : FiniteDimensional ℂ (S.comap R.smSub.subtype) :=
      FiniteDimensional.of_injective
        ((R.smSub.subtype.comp (S.comap R.smSub.subtype).subtype).codRestrict S (fun x => x.2))
        (fun x y h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h'))
    exact Submodule.finiteDimensional_of_le hle

theorem oneLength_moment_lowestType_largeGap (hH : GlobalTheory.GapIn.Hyp) (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ)
    (hS : Setup lam u b bv ga h q0 z π μW μN μG νq R l dg) (ν : Fin (2 * r + k + 1) → ℤ) (q : ℕ)
    (hν : n1 ν + (r + 1) * q ≤ q0) (hq : (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2) (w : (R ν).H)
    (hw : PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w)
    (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq
      ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) := by
  classical
  have hHG : HypsG := hH.1
  have hK : PI.KFinSmooth := hHG.1.2.2.1
  have hSG : SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg :=
    (_root_.GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg).1 hS
  have hNum := hS.1
  have hFam := hS.2.1
  have hSide := hS.2.2.1
  have hSF := hS.2.2.2
  have hk : 1 ≤ k := hNum.1
  have hν0 : n1 ν ≤ q0 := le_trans (Nat.le_add_right _ _) hν
  obtain ⟨Q, hQ, hw1, hwL⟩ := hw
  have hQu : IsUnit Q := hQ.1.1
  have hE : ∀ ν', ∃ E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub,
      n1 ν' ≤ q0 → (R ν').IsE Q E ∧ Formalism.REAL.GlRel E := by
    intro ν'
    by_cases h' : n1 ν' ≤ q0
    · obtain ⟨E, hE⟩ := GlobalTheory.smooth_gl_module hK k r _ _ (R ν') (hFam ν' h') Q hQu
      exact ⟨E, fun _ => hE⟩
    · exact ⟨fun _ _ => 0, fun h'' => absurd h'' h'⟩
  choose E hE using hE
  have hDS := hFam ν hν0
  have hDG : (R ν).IsDG (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) := hSG.2.1 ν hν0
  have hD := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 _ _ _ hDS Q hQ
  obtain ⟨hG, -, hlen, hmeas⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hSide
  obtain ⟨hBeL, hdg, -⟩ := hSF ν hν0
  obtain ⟨hmul, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r _ _ (R ν) hDS
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r z := hSide.2.1
  obtain ⟨⟨hb1, hb2, -, -, -⟩, -⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  have hb : (1 : ℝ) ≤ b := by linarith
  have hA : 0 ≤ (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) := by
    have : 0 ≤ bv := by linarith
    positivity
  have hA' := mul_nonneg hA (by positivity : (0 : ℝ) ≤ (b ^ 2) ^ (2 * r))
  have hnum := GlobalTheory.MomNum.mom_num k r lam u b bv ga h q0 _ hNum hT
  have hsmS : ∀ S : Submodule ℂ (R ν).H, FiniteDimensional ℂ S →
      PI.UpqRep.IsKStableOn (PI.BesselPeriodGGP.eps48 k r) (fun g => (R ν).σ (Q⁻¹ * g * Q)) S → S ≤ (R ν).smSub :=
    fun S h1 h2 v hv => ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK k r _ _ (R ν) hDS Q hQ S h1 h2).1 v hv).2
  have key := GlobalTheory.MomOne.lintegral_le_of_highest (m := νq) hD.2.2.1 _ (R ν).smSub hsmS
    (fun v x => ((lenA k r z (Matrix.of x) a ^ q * Real.sqrt (dg ν) : ℝ) : ℂ) • l ν ((R ν).σ (Matrix.of x) v))
    ?_ ?_ ?_ ?_ (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ q) (pow_nonneg (hA'.trans hnum) q) ?_ w hwL hw1
  · simpa only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le] using key
  · intro v hv v' hv'
    filter_upwards [hG] with x hx
    simp only [Pi.add_apply]
    rw [map_add (f := _), hBeL.1.1 _ (hsm _ hx v hv) _ (hsm _ hx v' hv'), smul_add]
  · intro c v hv
    filter_upwards [hG] with x hx
    simp only [Pi.smul_apply]
    rw [map_smul, hBeL.1.2.1 c _ (hsm _ hx v hv), smul_comm]
  · intro v hv
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((((hlen a).pow_const q).mul_const _).aestronglyMeasurable)).smul (hmeas (l ν) hBeL.1 v hv)
  · intro g hg v hv
    obtain ⟨hgG, hgU⟩ := GlobalTheory.MomOne.conj_back hQ hg
    simp only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le]
    have := GlobalTheory.MomOne.lintegral_rmul hSide
      (fun x => lenA k r z x a ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ x v)‖ ^ 2))
      (((GlobalTheory.LengthCont.lenA_continuousOn k r z hSide.1 hT a).pow _).mul (continuousOn_const.mul
        ((GlobalTheory.cwCont_continuousOn_hasDerivAt hK k r _ _ (R ν) hDS Wp (l ν) hBeL.1.1 hBeL.1.2.1 hBeL.1.2.2.2
          v hv).1.norm.pow 2))) ?_ hgG
    · rw [← this]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [GlobalTheory.MomOne.lenA_mul_unitary z _ hgU, hmul _ hx _ hgG]
    · intro s hs x hx
      have e := (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.2 s hs a
      obtain ⟨h', hh, m, hmN, rfl⟩ := hs
      obtain ⟨u₀, hπ⟩ := hSide.2.2.1
      have hsG : h' * m ∈ GG k r := Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hmN.1
      beta_reduce
      rw [e, hmul _ hsG _ hx, hBeL.1.2.2.1 h' hh m hmN _ (hsm _ hx v hv), norm_smul,
        Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_norm, one_mul, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ h' hh]
  · intro S hfd hst hcd v hv hv1 hwt
    simp only [GlobalTheory.MomOne.norm_sq_scaled _ _ hdg.le]
    have hvs : v ∈ (R ν).sm := hsmS S hfd hst hv
    by_cases hnz : NzOn (R ν) (l ν)
    · have hLev := lev_zero_of_wt hHG hk hDG hQ (hE ν hν0).1 S hfd hst hcd ⟨v, hvs⟩ hv hwt
      have hv1' : ‖(⟨v, hvs⟩ : (R ν).smSub)‖ = 1 := hv1
      have hmain := GlobalTheory.MomOne.single_moment_le (Formalism.QuantumDeterminants.Mt k r) νq r q (fun a x => lenA k r z (Matrix.of x) a)
        (fun x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2)
        (((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) (b ^ 2)
        hlen
        (fun a => hG.mono fun x hx => (GlobalTheory.TensLen.lengths k r z hSide.1 hT _ hx).2.2.1 a)
        (((hmeas (l ν) hBeL.1 v hvs).norm.aemeasurable.pow_const 2).const_mul _)
        (fun x => mul_nonneg hdg.le (by positivity))
        (by
          have := ((Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hSG ν hν0).2 hnz).2 v hvs
          simpa only [one_mul, hv1, one_pow, ENNReal.ofReal_one] using this)
        hA (one_le_pow₀ hb)
        (fun q' hq' => by
          have := Gp91.GlobalTheory.T.family_setup_cayley_recursion hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hSG hQ hE
            q' ν (by omega) 0 (by omega) ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this)
        (fun a q' hq' => by
          have := Gp91.GlobalTheory.T.family_setup_cayley_bound hHG k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hSG hQ hE ν hν0
            0 q' (by omega) a ⟨v, hvs⟩ hLev
          simpa only [hv1', one_pow, mul_one] using this) a
      exact hmain.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hA' hnum _))
    · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
        intro v hv
        by_contra hne
        exact hnz ⟨v, hv, hne⟩
      refine le_of_eq_of_le ?_ bot_le
      rw [bot_eq_zero, ← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hG] with x hx
      rw [hz _ (hsm _ hx v hvs)]
      simp

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem moment_one_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν (q : ℕ), n1 ν + (r + 1) * q ≤ q0 → (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) a ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Tz k r z) b ^ q) :=
  fun hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a =>
    oneLength_moment_lowestType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν q hν hq w hw a

end main

end GlobalTheory.MomOneGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsRawMassAndGenusMass
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowsRawMass

open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowsLift (D : D7) (u : D.what₂.Word) : LiftsConjugateUnderStabilizer D u := by
  intro hp h3 hs F0 he hz
  exact GlobalTheory.T.row_lattices_same_middle_conjugate_unipotent D u hp h3 hs F0 he hz

theorem gluingNum (D : D7) (u : D.what₂.Word) : GluingNumber D u := by
  intro hp h3 hs F0 he hz Λ hΛ
  exact GlobalTheory.T.card_middleLattices_over_genus_lattice D u hp h3 hs F0 he hz Λ hΛ

theorem rowsGenus (D : D7) (u : D.what₂.Word) : OrthLatticesOneGenus D u := by
  intro hp h3 hs F0 he hz Λ hΛ
  exact GlobalTheory.T.rowBaseLattices_mem_same_hermitianGenus D u hp h3 hs F0 he hz Λ hΛ

theorem main : ∀ (D : D7) (u : D.what₂.Word), UnitaryVolumeMass.stLem3L0 D u := by
  intro D u hp h3 hs F0 he hz s hsr

  have glue := Formalism.MainNotions.BridgeLemma₂.gluing_mass_of_lift_number_genus D u (rowsLift D u) (gluingNum D u) (rowsGenus D u)
  have hT : ((Tu D u : ℝ) - 1) ^ D.R.f ≠ 0 := by
    apply pow_ne_zero
    have : (3 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast h3
    linarith

  have hm := fun Λ (hΛ : IsRowLat D F0 Λ) => GlobalTheory.T.mass_rowLattice_orthogonal_split_prime D u F0 he hz hp hs Λ hΛ

  obtain ⟨Λ₀, hΛ₀⟩ := GlobalTheory.Mass.RowEx.main D u F0 he hz hp hs
  refine ⟨?_, fun Λ hΛ => ⟨?_, (hm Λ hΛ).2⟩⟩
  · rw [glue hp h3 hs F0 he hz Λ₀ hΛ₀ s hsr, (hm Λ₀ hΛ₀).1, div_pow, mul_assoc, div_mul_cancel₀ _ hT]
  · rw [glue hp h3 hs F0 he hz Λ hΛ s hsr, mul_div_cancel_right₀ _ hT]

end GlobalTheory.Mass.RowsRawMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFundDomainVolumeClassical
section
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom
open Formalism.L2.SG.PoincareInHH.PoincareSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formallyUnramified_host (D : D7) : Algebra.FormallyUnramified (𝓞 D.host.F) (𝓞 D.host.E) := by
  haveI := D.host.isCMField_hostE
  have : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  infer_instance

theorem cancel_conj {m : ℕ} (A M N : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A.det)
    (h : A * M * A⁻¹ = A * N * A⁻¹) : M = N := by
  have key : ∀ Z : Matrix (Fin m) (Fin m) ℂ, A⁻¹ * (A * Z * A⁻¹) * A = Z := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA,
      Matrix.one_mul]
  rw [← key M, h, key N]

theorem isDomN (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word) :
    GlobalTheory.SnMass.IsDomN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Lc X) (Pc X u) (Ac X C)
      (Gm D '' (trX X C '' Y.FN u)) := by
  obtain ⟨hmeas, hex, huniq⟩ := Y.FN_fund u
  obtain ⟨hsurj, hinj, hmul⟩ := _root_.GlobalTheory.CovDom.transport_real_points D X θ C
  obtain ⟨h8a, h8b⟩ := _root_.GlobalTheory.CovDomGrp.nO_eq_nLam_coords D X θ C u
  have hgrp := Formalism.L2.SG.Pf.IdMeet.noinfEqC_holds D X u Y.hK
  have hA : ∀ w, IsUnit (Ac X C w).det := by
    intro w
    have h1 := (_root_.GlobalTheory.CovDom.ModelIso.model_adapted D X θ C u).1 w
    have h2 := (_root_.GlobalTheory.CovDom.herm_selfDual D X).1.2
    have e : ((Jc X).map w.embedding).det = w.embedding (Jc X).det := by rw [RingHom.map_det]; rfl
    have h3 : ((Jc X).map w.embedding).det ≠ 0 := by rw [e]; exact (map_ne_zero _).2 h2
    rw [← h1, Matrix.det_mul, Matrix.det_mul] at h3
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h3)
  refine ⟨_root_.GlobalTheory.CovDom.measurableSet_Gm_trX_image D X θ C _ hmeas, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj x hx
  obtain ⟨s, hs, hsg⟩ := hex g
  obtain ⟨γ, hγ, hc⟩ := h8b s hs
  refine ⟨γ, ⟨hγ, trX X C (s * g), ⟨s * g, hsg, rfl⟩, ?_⟩, ?_⟩
  · funext w
    rw [hc w, ← hmul]
    simp
  · rintro γ' ⟨hγ', y, ⟨f, hf, rfl⟩, hy⟩
    obtain ⟨s', hs', hc'⟩ := h8a γ' hγ'
    have hfe : f = s' * g := by
      apply hinj
      funext w
      have := congrFun hy w
      simp only at this ⊢
      rw [this, hc' w, ← hmul]
      simp
    have hmem : s' * s⁻¹ ∈ NOinf X u := by
      rw [hgrp] at hs hs' ⊢
      exact Subgroup.mul_mem _ hs' (Subgroup.inv_mem _ hs)
    have hss : s' * s⁻¹ = 1 := huniq (s * g) hsg _ hmem (by rw [show s' * s⁻¹ * (s * g) = s' * g by group, ← hfe]; exact hf)
    have hs'e : s' = s := by rw [mul_inv_eq_one] at hss; exact hss
    subst hs'e
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    have hm := cancel_conj _ _ _ (hA w) ((hc' w).trans (hc w).symm)
    refine Matrix.ext fun i j => w.embedding.injective ?_
    have := congrFun (congrFun hm i) j
    simpa only [Matrix.map_apply] using this

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal = (2 * D.host.v) ^ (((D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) * D.R.k + (D.R.rS : ℝ) / 2) * Fintype.card D.what₂.Tau) := by
  intro D X Y θ C u
  obtain ⟨hs, hnum⟩ := _root_.GlobalTheory.CovDom.normalising_constants D
  obtain ⟨hH, hSD⟩ := _root_.GlobalTheory.CovDom.herm_selfDual D X
  obtain ⟨hF, hDu, hT⟩ := _root_.GlobalTheory.CovDom.frame_dual_lat D X u
  obtain ⟨hM, hAd⟩ := _root_.GlobalTheory.CovDom.ModelIso.model_adapted D X θ C u
  have hI := _root_.GlobalTheory.SnMass.VolN.covolume_N D.host.F D.host.E D.sp.cm.sig D.R.k D.R.rS (Jc X) (Lc X) (Pc X u) (fc X) (Tc u)
    (Ac X C) (sc D) (GlobalTheory.AdelicU.isCMExt_host D) (formallyUnramified_host D) hH hSD hF hDu hT hM hs hAd
  have h1 := hI.2 _ (isDomN D X Y θ C u)
  have hv : 0 ≤ 2 * D.host.v := by unfold Host.v Host.rdE; positivity
  change (Measure.pi _ (trX X C '' Y.FN u)).toReal = _
  rw [← _root_.GlobalTheory.CovDom.measure_Gm_image D, h1, hnum, ENNReal.toReal_ofReal (Real.rpow_nonneg hv _)]

end GlobalTheory.CovDom
end
end

