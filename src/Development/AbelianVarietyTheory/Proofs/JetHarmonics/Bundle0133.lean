module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0120
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Development.AutomorphicArithmetic.OrbitLabellings.PkgZeroCsNuNonposOfMonSupply
public import Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError
public import Development.AutomorphicArithmetic.OrbitLabellings.FMulLeastAdmissibleLevelRowsLe
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0068
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamObj
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

theorem le_DF_of_mult_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (h : 0 < Dw.mult τ) : a (τ, 0) ≤ DF Dw a := by
  unfold DF
  calc a (τ, 0) = a (τ, ((⟨0, h⟩ : Fin (Dw.mult τ)) : ℕ)) := rfl
    _ ≤ ∑ i : Fin (Dw.mult τ), a (τ, i) :=
        Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem thl_nonneg' (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem one_le_log_of_five_le {k : ℕ} (hk : 5 ≤ k) : 1 ≤ Real.log k := by
  have h5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem parOK_parAt {N : NumDatum} {j l : ℕ} (h : ParOK (parOf N j l)) (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) :
    ParOK (parAt N j d pos) := ⟨h.card, h.m_pos, h.mk_le, h.r_eq, h.SE_nonneg⟩

theorem degHyp2_parOf {N : NumDatum} {j : ℕ} {W : RPl N.R → ℕ} {T θ0 rest C1 : ℝ}
    (h : RF.DegHyp2 (parAt N j 1 fun z _ => z) W T θ0 rest C1) (l : ℕ) : RF.DegHyp2 (parOf N j l) W T θ0 rest C1 :=
  ⟨h.T_one, h.w_pos, h.TW_lo, h.TW_hi, h.th_rng, h.th_m, h.rest_nonneg, h.rest_le⟩

private theorem odd_ordP_of_conjIn {N : NumDatum} {l : ℕ} (h : ConjIn N l) : Odd (N.ordP l) := by
  unfold NumDatum.ordP
  rw [if_neg (by rw [h.1]; simp)]
  exact h.2

theorem nuGood : NuGoodSt := by
  intro C1 hC1
  obtain ⟨CI, hCI, HI⟩ := _root_.GlobalTheory.InertContent.main C1 hC1
  obtain ⟨CP, hCP, HP⟩ := _root_.GlobalTheory.GoodDepth.ConjPkg.phiCBd C1 hC1
  obtain ⟨CS, hCS, HS⟩ := _root_.GlobalTheory.GoodDepth.splitBd C1 hC1
  obtain ⟨CC, hCC, HC⟩ := UpperTheory.rowBound_le_Fnum_sum_add_error _root_.GlobalTheory.oddBlock_supply.2 _root_.GlobalTheory.CharBlock.chSupply.2 _root_.GlobalTheory.MonBlock.monSupply.2 C1 hC1
  obtain ⟨HZ, -⟩ := _root_.GlobalTheory.GoodDepth.zeroBd
  refine ⟨2 * CI + 2 * CP + 2 * CC + CS + 2, by positivity, ?_⟩
  intro E _ _ _ H Dw lv Xo c _ hstar hIC hPk N j pl a nW T b L w hj1 hjm hpl hp hq hdom hG hw hb la h2 hq' hd hg0 hg1 hM
  obtain ⟨PI, PP, PS, PZ, -, PC, PZC⟩ := hPk
  have hl : (resCharOf la).Prime := Crude.resCharOf_prime la
  have hin := hG.inert_ge _ hl
  have red := GlobalTheory.GoodDepth.nuW_bound_of_charts E H Dw lv Xo c hIC la lv.M a nW
  have PI' := PI hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PP' := PP hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PS' := PS hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZ' := PZ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZC' := PZC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PC' := PC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  clear PI PP PS PZ PZC PC
  generalize resCharOf la = l at *
  obtain ⟨θ0, hdeg⟩ := hG.deg
  have hT1 : (1 : ℝ) ≤ T := hdeg.T_one
  have hT1' : 1 ≤ T := by exact_mod_cast hT1
  have hwpos : ∀ z, 0 ≤ N.w j z := fun z => (hdeg.w_pos z).le
  have hsum : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hwpos z
  have hw0 : 0 ≤ w := hsum.trans hw
  obtain ⟨hF0, htri, hOK, hFC, hFI⟩ := GlobalTheory.ContentValue.main N j l hl h2 hq' hd hg0 hg1 hwpos hG.ratio
  have hm2 := N.R.two_le_m
  have hmk := N.R.m_add_three_le_k
  have hf2 : 2 ≤ N.R.f := hm2.trans N.R.m_le_f
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hn : ((N.R.k - 1 : ℕ) : ℝ) = (N.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    have := ne_two_of_not_small h2
    omega
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨R1, R2, R3, R4⟩ := GlobalTheory.RowBudgets.main N.R.r N.R.f (N.R.k - 1) N.R.m nW T l N.R.k b L w (by omega) (by omega) (by omega)
    hf2 hT1' (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  have R5 := UpperTheory.f_mul_leastAdmissibleLevel_rows_le N.R.r N.R.f (N.R.k - 1) N.R.m nW l N.R.k L (by omega) (by omega) (by omega)
    hf2 (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  rw [hn] at R3 R4
  have hzero : ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
      ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ 0 := by
    intro s hs hrow V io e ho y hy C ν hν
    by_cases hc : ConjIn N l
    · obtain ⟨Pk, rfl⟩ := PZC' V io e ho y hy C nW ν hν hc.1 (odd_ordP_of_conjIn hc) hwpos s hs hrow
      exact UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply _root_.GlobalTheory.MonBlock.monSupply.2 _ _ Pk
    · obtain ⟨d, _, pos, Pk, rfl⟩ := PZ' V io e ho y hy C nW ν hν hc hwpos s hs
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))) hrow)
      exact HZ _ _ Pk
  have hSE : 0 ≤ N.Sc + N.eta := hOK.SE_nonneg
  have hlog : 1 ≤ Real.log N.R.k := one_le_log_of_five_le (by omega)
  have hth := thl_nonneg' N.R.k l
  set A1 : ℝ := Real.log N.R.k * N.R.m * w / l with hA1
  set A2 : ℝ := N.R.f * N.R.k * (N.Sc + N.eta) / l with hA2
  set A3 : ℝ := N.R.k * thl N.R.k l * w with hA3
  set A4 : ℝ := if N.sc.X'' N.R.n < (l : ℝ) then N.R.k * w / (l : ℝ) ^ 2 else 0 with hA4
  have a1 : 0 ≤ A1 := by positivity
  have a2 : 0 ≤ A2 := by positivity
  have a3 : 0 ≤ A3 := by positivity
  have a4 : 0 ≤ A4 := by rw [hA4]; split_ifs <;> positivity
  have hA4' : (if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ≤ 2 * A4 := by
    rw [hA4]
    split_ifs
    · gcongr
    · simp
  set B : ℝ := N.FjP j l + (2 * CI + 2 * CP + 2 * CC + CS + 2) * (A1 + A2 + A3 + A4) with hB
  have hB0 : 0 ≤ B := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hmain : ∀ (V : CDVR) (io : c.F →+* V.Fr) (e : ℕ), OverLa la V.V io e → ∀ y : IntFr Xo c V io, y.IsAlg →
      ∀ (C : IntChart V io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ B / T := by
    intro V io e ho y hy C ν hν
    have hBT : 0 ≤ B / T := by positivity
    by_cases hb0 : b < 0
    · refine le_trans (hzero 0 (fun τ hτ => ?_) (by simp) V io e ho y hy C ν hν) hBT
      have h1 := hG.first τ hτ
      have h2 : (0 : ℝ) ≤ (T : ℝ) * a (τ, 0) := by positivity
      exfalso; linarith
    push Not at hb0
    by_cases hl2 : N.R.m * b / (T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * L) ≤ l
    · obtain ⟨s, hs1, hs2⟩ := R3 hl3 hb0 hl2
      exact le_trans (hzero s (fun τ hτ => hs2 _ (hG.first τ hτ)) hs1 V io e ho y hy C ν hν) hBT
    push Not at hl2
    have hadd := R4 (by omega) hl2 hb
    have herr : errB (parOf N j l) l T ≤ 2 * (A1 + A2 + A3) := by
      have e1 : Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l ≤ A1 := by rw [hA1]; gcongr
      have e3 : N.R.k * thl N.R.k l * (∑ z, N.w j z) ≤ A3 := by rw [hA3]; gcongr
      have : errB (parOf N j l) l T = Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + A2 +
        N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * Real.log N.R.k ^ 2 := rfl
      rw [this]; linarith
    rw [le_div_iff₀ hTpos, mul_comm]
    have p1 := mul_nonneg hCI.le a1
    have p2 := mul_nonneg hCI.le a2
    have p3 := mul_nonneg hCI.le a3
    have p4 := mul_nonneg hCI.le a4
    have q1 := mul_nonneg hCP.le a1
    have q2 := mul_nonneg hCP.le a2
    have q3 := mul_nonneg hCP.le a3
    have q4 := mul_nonneg hCP.le a4
    have s1 := mul_nonneg hCS.le a1
    have s2 := mul_nonneg hCS.le a2
    have s3 := mul_nonneg hCS.le a3
    have s4 := mul_nonneg hCS.le a4
    have c1 := mul_nonneg hCC.le a1
    have c2 := mul_nonneg hCC.le a2
    have c3 := mul_nonneg hCC.le a3
    have c4 := mul_nonneg hCC.le a4
    rcases htri with hI | hS
    · have h5 := hin hI
      by_cases hc : PhiC N l
      · obtain ⟨Pk, hT, hν'⟩ := PP' V io e ho y hy C nW ν hν hc T θ0 C1 (degHyp2_parOf hdeg l) R1
        have h1 := HP _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFC hc
        have h3 := mul_le_mul_of_nonneg_left herr hCP.le
        have h1' : (T : ℝ) * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + CP * errB (parOf N j l) l T := h1
        rw [hB]; linarith
      by_cases hcs : ConjIn N l
      · obtain ⟨Pk, hT, hν'⟩ := PC' V io e ho y hy C nW ν hν hcs.1 (odd_ordP_of_conjIn hcs) T θ0 C1
          (degHyp2_parOf hdeg l) (R5 h5)
        have h1 := HC _ l hOK.card hOK.m_pos hOK.mk_le hOK.r_eq hOK.SE_nonneg hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCC.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
      · obtain ⟨Pk, hT, hν'⟩ := PI' V io e ho y hy C nW ν hν hI hcs T θ0 C1 (degHyp2_parOf hdeg l) (R2 h5)
        have h1 := HI _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCI.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
    · obtain ⟨d, _, pos, Pk, hT, hν'⟩ := PS' V io e ho y hy C nW ν hν hS T θ0 C1 hdeg
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1)
      have h1 := HS _ l (parOK_parAt hOK d pos) hl Pk
      rw [hT, hν'] at h1
      have h1' : (T : ℝ) * ν ≤ CS * ((N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l) := h1
      have e1 : (N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l ≤ A1 + A2 := by
        rw [hA1, hA2, add_div]
        have : (N.R.m : ℝ) * (∑ z, N.w j z) ≤ Real.log N.R.k * N.R.m * w := by
          calc (N.R.m : ℝ) * (∑ z, N.w j z) = 1 * N.R.m * (∑ z, N.w j z) := by ring
            _ ≤ _ := by gcongr
        gcongr
      have h3 := mul_le_mul_of_nonneg_left e1 hCS.le
      rw [hB]; linarith
  obtain ⟨r1, r2, -⟩ := red (B / T) (by positivity) hmain
  refine ⟨r1, ?_, fun hDF => ?_⟩
  · rw [le_div_iff₀ hTpos, mul_comm] at r2
    exact r2
  · refine (red 0 le_rfl (hzero 1 (fun τ hτ => ?_) ?_)).2.2 rfl
    · have := le_DF_of_mult_pos Dw a τ hτ
      omega
    · rw [mul_one]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InputExistsOfMemberExists
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.CuspFamilyCompare

section Pairing

variable {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

end Pairing

theorem exp_unique {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ}
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ G)} (he : ∀ z w, e (z + w) = e z * e w) (he' : ∀ z w, e' (z + w) = e' z * e' w)
    (hol : IsHolTo Set.univ (fun z => (e z).left)) (hol' : IsHolTo Set.univ (fun z => (e' z).left))
    (u : Fin g → (Sp (DualNumber ℂ) ⟶ G.left)) (hd : ∀ i, IsDerivAt0 (fun z => (e z).left) (Pi.single i 1) (u i))
    (hd' : ∀ i, IsDerivAt0 (fun z => (e' z).left) (Pi.single i 1) (u i)) : e = e' := by
  have h0 : e 0 = e' 0 := (HolHom.map_zero_eq_one he).trans (HolHom.map_zero_eq_one he').symm
  refine HolHom.eq_of_fderiv_eq he he' hol hol' fun U hU f => ContinuousLinearMap.coe_injective ((Pi.basisFun ℂ _).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact (((HolHom.isDerivAt0_iff _ _ _).1 (hd i)).2 U hU f).symm.trans
    (((HolHom.isDerivAt0_iff _ _ _).1 (hd' i)).2 U (h0 ▸ hU :) f)

section Tangent

open GlobalTheory.ArcQ GlobalTheory.TorusTangent ReciprocityTheory.ChartRestriction.G.DVR

variable {K : Type} [Field K] {D₀ : Out.DegPre K}

variable [NumberField K]

end Tangent

section Exponents

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {X : Type} [AddCommGroup X]
  [Module (𝓞 E) X] {g : ℕ} {ξ : Module.Dual ℤ X} {be : LinearMap.BilinForm ℤ X}

end Exponents

section Fibre

variable {K : Type} [Field K]

variable [NumberField K] {D₀ : Out.DegPre K}

end Fibre

variable {D : D7} {T : Core D} {j : ℕ}

section Family

variable {n' : ℕ} {La c₁ : ℝ}


end Family

section Comparison₂

variable {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Comparison₂

section Claims

variable {n' : ℕ} {La c₁ : ℝ} {Wp : ValuationSubring ℂ} {Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype}
  {σ : T.Q.c.F →+* ℂ} {k : (T.U j σ).Comp} {x : ((T.U j σ).X k).dom} {ξ : Fin D.R.r → D.host.E}
  {ν : ((T.U j σ).X k).Ψ → ℝ} {lam : Fin (D.R.r - 2) → Fin D.R.r → D.host.E}


end Claims

end GlobalTheory.CuspFamilyCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPullbackSecModelUniversalBijectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powPullbackSec_modelUniversal_bijective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ q : ℕ, (∀ σ, ∃! hh, SecTieF I P F xF q σ hh) ∧ (∀ hh, ∃! σ, SecTieF I P F xF q σ hh) ∧ ∀ (u : F) (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))), SecTieF I P F xF q σ hh → (∀ jj, σ'.f jj = resTop _ (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ.f jj) → (∀ jj, hh'.f jj = liftFun Xo.univ.t.G _ (toΓ F u) * hh.f jj) → SecTieF I P F xF q σ' hh' := by
  first | exact @GlobalTheory.SecTie.secTie_bijective | exact GlobalTheory.SecTie.secTie_bijective | (intros; apply GlobalTheory.SecTie.secTie_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RestDegAdd
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem restDeg_add {d : ℕ} [NeZero d] (bgr : ZMod d → Fin 2) (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.restDeg bgr n ga K + ∑ s, n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ s : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g s k := by
  unfold RF.restDeg
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0 := by
    rw [Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) (W : P.Pl → ℕ) :
    ∑ z ∈ Z, ∑ s : ZMod P.d, W (P.pos z s.val) = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem wtHyp_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m → (∀ z, InPsi H (pl z)) → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → ∀ (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)) (bgr : ZMod d → Fin 2) (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ)), RF.IsReps (parAt N j d pos) Z → Function.Bijective (fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2) → (∀ z s, tau z (bgr s) s = pl (pos z s.val)) → RF.WtHyp N.R.k N.R.r Z bgr (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) (fun z => RF.alongOrb (parAt N j d pos) z (gapW N pl a)) (fun _ _ => 0) (restOf N Dw pl a) := by
  intro E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
    unfold Datum.mult; split_ifs <;> omega
  have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
  have hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) =
      gapW N pl a (pos z s.val) := by
    intro z s
    rw [htau]
    have hm : Dw.mult (pl (pos z s.val)) = Dw.p := if_pos (hpsi _)
    rw [hm]
    unfold gap gapW
    rw [if_pos (by omega), if_pos (by omega)]
    rfl
  refine ⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩
  have hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i) := by
    unfold DF
    rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
  have key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) +
      (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a := by
    have hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z :=
      sum_reps (parAt N j d pos) Z hZ (gapW N pl a)
    rw [hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have := restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))
    simp only [hmain] at this
    rw [Finset.mul_sum, this]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2
  unfold restOf
  rw [← key]
  push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
  simp

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValue
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthRule

theorem depth_le_scaled_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  intro D T h j hj w hw s hs la y f hf
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA w) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ hw) f hf
  have hsK : ((s : 𝓞 T.Q.c.F) : T.Q.c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  let F : (recB h.toLawsCore).Cusp j w := ⟨f, hc⟩
  have hF : F ∈ (recPJ h j hj).thAll w := Submodule.subset_span hf
  have hsF : s • F ∈ (recPJ h j hj).WWc s w := ⟨F, hF, rfl⟩
  refine (iInf₂_le (s • F) hsF).trans (le_of_eq ?_)
  rw [recPJ_vAt_inc h j hj la y w (s • F)]
  have h1 : (s • F).1 = ((s : 𝓞 T.Q.c.F) : T.Q.c.F) • f := rfl
  rw [h1]
  exact vAtV_smul y _ f hsK

end GlobalTheory.DepthRule
end

