module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0139
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0162
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0220
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0076
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0213
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0221
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0140
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0711
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0173
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RamificationIndexIntegralOfThirdJump
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem ramification_index_integral_of_third_jump_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  intro _ _
  refine StepW.of_all fun K B f T w _ _ _ P x _ j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eExp_integer_of_levelC : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ _ : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, ∀ j g, ∃ z : ℤ, eExp (Dof x) j g = z := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | exact _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.ramification_index_integral_of_third_jump_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RankGrowthBoundSmallScale
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.HodgeSteps
theorem rk_le_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hX hP hSi hTo hG hQ hN hDG hS hFD hDeg hSh
  refine ((((((((((hDG.and hS).and hFD).and hDeg).and hSh).and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hS)).and (_root_.GlobalTheory.T.size_bounds_for_family_alt hS)).and
    (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt hP hG hQ hSi hTo hN hDG hS hFD)).and (_root_.GlobalTheory.T.abs_flat_c1_add_logOm_le_and_logSum_badPrimes_le hFD)).and _root_.GlobalTheory.HSApp.wtBig_run_alt).and _root_.GlobalTheory.CovTop.WtShape.wtN_z).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, -, a1⟩, A, -, a2⟩, _, -, a3⟩, _, -, a4⟩, _, -, a5⟩, _, -, a6⟩, _, -, a7⟩, _, -, a8⟩, _, -, a9⟩,
    _, -, a10⟩, _, -, a11⟩ := h
  obtain ⟨x0, h⟩ := (((((((((a1.and a2).and a3).and a4).and a5).and a6).and a7).and a8).and a9).and a10).and a11
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY s hs1 hs2 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩, b8⟩, b9⟩, b10⟩, b11⟩ := h x hx hle ι p hp
  clear h a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
  obtain ⟨-, g1, -, -, -, hfin, -, -⟩ := b1 i hi Y hY
  obtain ⟨hb1, -, -, -, -, hbk, hq⟩ := b2 i
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨-, hρ0, hρ1, -⟩ := hq u1 hu
  obtain ⟨δ, hδ, hdg⟩ := b4 i hi Y hY u1 hu
  have hsh := b5 i hi Y hY u1 hu
  obtain ⟨hp1, hq1, hf, hu1, hA, -, hanti⟩ := b6 i hi
  obtain ⟨hL, hj, hL1, -, -, -, -, -, hf8, hr100, -, -, hPP, -, hz1, hz2, -⟩ := b7 i hi Y hY
  have hval := b8 i hi Y hY
  obtain ⟨hC, hl, hF, -⟩ := b9 i hi Y hY
  have hgap := (b10 i hi).gaps
  have hdom := (b11 i).dom
  have hfl := b3 i hi Y hY
  clear b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 hq
  rw [← hu1 u1 hu] at hA hanti hz1 hz2 hval hgap
  clear hu1
  generalize (Fm.parT x hx ι).PP = PP at *
  rw [← CompHS.dimFlag_eq] at hgap
  have hd3 : 3 ≤ CompHt.dimFlag (dat p i) := by
    rw [CompHS.dimFlag_eq, FlagTan.dimFlag]
    exact le_trans hf (Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega)))
  have hPP100 : 100 ≤ PP := by
    refine le_trans ?_ hPP
    have c1 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have c2 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c3 : (8 * 100 * 1 : ℝ) ≤ zBase (Fm.L x ι) := by
      unfold zBase
      gcongr
    exact le_trans (by linarith) (le_self_pow₀ (by linarith) (by norm_num))
  have hT : 1000 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 ≤ lenT p i PP := by
    refine le_trans ?_ (Nat.le_ceil _)
    have c1 := (Fm.D x ι).R.two_le_m
    have c2 := (Fm.D x ι).R.m_add_three_le_k
    have c3 : (0 : ℝ) < (Fm.D x ι).R.m := by exact_mod_cast (by omega : 0 < (Fm.D x ι).R.m)
    have c4 : ((Fm.D x ι).R.m : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : (Fm.D x ι).R.m ≤ (Fm.D x ι).R.k)
    have c5 : 1000 ≤ PP ^ 2 := by nlinarith
    rw [le_div_iff₀ c3]
    gcongr
  obtain ⟨a, ha1, ha2⟩ := exists_jet_order _ _ _ (by omega) hT hρ0 hz2
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hY.1 u1 fun τ a b hb => by
    rw [← gap_eq _ hb]
    refine le_trans ?_ (hgap τ a (hb ▸ b.2))
    exact_mod_cast bir_gap_le _ _ hd3
  have hboth := _root_.GlobalTheory.DegVal.compDeg_between _ _ _ _ _ _ _ Y.U hY.1.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSi hTo hN _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1) u1 (fun τ => (hA τ).1) (fun τ => (hA τ).2) hbir hval
  have hc0 : 1 ≤ cZero (Fm.D x ι) ((i : ℕ) + 1) := by
    have := (cZeroN_isLeast (Fm.D x ι) ((i : ℕ) + 1)).1.2.2
    unfold cZero
    omega
  have ew : uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) =
      fun τ => uM p i τ + (((s + 1 : ℕ) : ℤ) * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ := by
    funext τ k
    simp only [uM, uW, uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have em : uW p i + (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) • hodgeWt (dat p i) = uM p i := by
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hl1 : ∀ τ, Antitone ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    exact (hanti (s + 1) (by omega) τ).1
  have hl2 : ∀ τ, Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + 4 : ℕ) : ℤ) • u1 τ -
      (uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) := fun τ => by
    rw [ew]
    have := (hanti (s + 1) (by omega) τ).2
    rwa [if_neg (Nat.succ_ne_zero s)] at this
  have hl3 : ∀ τ, 1 ≤ gap ((uW p i + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i)) τ) ((dat p i).p - 1) :=
    fun τ => by
      rw [ew]
      refine le_trans ?_ (le_gap_bar (dat p i) hp1 hq1 (uM p i) τ ?_ _)
      · push_cast
        nlinarith [Int.natCast_nonneg s]
      · simpa using (hanti 0 (by omega) τ).1
  have hev : Even (p.κ i).n := (p.κ i).n_even
  have g2 : Y.GoodAt (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) :=
    _root_.GlobalTheory.CovTop.HodgeSteps.covering_goodAt_shift hP _ p.T hL _ hj Y _ _ hY.1 (le_add_right hp1) hC hl hF _ _ ((Fm.D x ι).R.k - 1) _ hev
      (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hl1 hl3).1
  have htw := ((_root_.GlobalTheory.T.twisted_flat_bundle_ranks hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 _ hfl).2 _ (p.κ i).n ((Fm.D x ι).R.k - 1) · hdom hev)
  rw [htw _ g1, htw _ g2]
  have hk : 0 < PP * kap p i := by linarith
  have hz : zed p i PP u1 ≤ min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i)) := le_min hz2 ((le_div_iff₀ hk).2 hz1)
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  first
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSi hTo hG hQ hN
    | have hJ := _root_.GlobalTheory.T.jet_rank_complex_le hP hSi hTo hG hQ hN
  letI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun Z _ => ?_
  have d0 : 0 < Y.dg u1 Z := hδ.trans_le (hdg Z).1
  have d1 : (1 - CompHt.rhoB (dat p i) u1) * CompHt.topDeg Y.U Z u1 ≤ Y.dg u1 Z :=
    (CompHt.delPrime_eq Y.U Z (CompHt.vdm_pos fun τ => (hA τ).1).ne').ge.trans (hboth Z Z).1
  have d2 := hJ _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 Z u1 _ _ a hgap hl1 hl2 (by
    have h1 : 0 < 1 - CompHt.rhoB (dat p i) u1 := by linarith
    refine lt_of_mul_lt_mul_left ?_ h1.le
    have e1 := mul_le_mul_of_nonneg_left d1 (Nat.cast_nonneg (lenT p i PP + CompHt.dimFlag (dat p i) + 4))
    have e2 := mul_lt_mul_of_pos_right ha1 d0
    linarith)
  calc _ ≤ _ := d2
    _ ≤ (1 + zed p i PP u1) * binT p i PP * Y.dg u1 Z := mul_le_mul_of_nonneg_right ha2 d0.le
    _ ≤ (1 + zed p i PP u1) * Y.rkC (uM p i) Z := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hsh Z).1 (by linarith)
    _ ≤ _ := by
      rw [← em]
      exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
end GlobalTheory.CovTop.HodgeSteps
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_growth_bound_small_scale_alt_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ s : ℕ, 1 ≤ s → s ≤ 2 → (Y.rk (Gs p i (s * cZero (Fm.D x ι) ((i : ℕ) + 1))) : ℝ) ≤ (1 + min (1 / 2) ((Fm.L x ι).sc.b / (PP * kap p i))) * Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt | exact _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt | (intros; apply _root_.GlobalTheory.CovTop.HodgeSteps.rk_le_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsCusp
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Blocks
open NumberField IsDedekindDomain Polynomial Filter
section Satake
open GlobalTheory.LFun GlobalTheory.PRep GlobalTheory.CuspRep Formalism.UG
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
variable [_root_.NumberField.IsTotallyComplex E]
end Satake
section Local
open GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
variable [_root_.NumberField.IsTotallyComplex E] (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL)
end Local
section Polar
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.ThetaPull GlobalTheory.UnitaryBC Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap continuous_ideleMap ideleMap_principalIdele continuous_adeleMap)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
end Polar
section Record
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} {l : ℕ} [Fact l.Prime]
variable {ι : Qbar l ≃+* ℂ}
end Record
section True
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.RowPar GlobalTheory.RowTie GlobalTheory.CuspRep GlobalTheory.WeilDeligne
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {D : D7} {T : WDTie D.nd D.naut}
  (C : _root_.GlobalTheory.HeightCounting.CGTrueT hL D T)
include hF in
theorem readsCusp_alt : haveI := host_isCMField D.host; ReadsCusp D.naut fun a π => (C.e a π).1 := by
  have := host_isCMField D.host
  refine ⟨fun a _ => Subtype.val_injective.comp (C.e a).injective, fun a π _ => (C.e a π).2, fun a π w _ hu => ?_⟩
  rw [T.frobEig w _ hu, C.loc]
  exact _root_.GlobalTheory.HeightCounting.Blocks.exists_satake_frobenius_eigenvalues_eq_inv_of_unramified hL hF _ _ (by have e := (T.unr w _).1 hu; rwa [C.loc] at e)
end True
end GlobalTheory.HeightCounting.Blocks
namespace GlobalTheory.HeightCounting
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecT
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
namespace GlobalTheory.FormDict.RecTLaws
section Core
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem hasSatGL_rec_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (cls (ParLaws.toRep σ))).unr ∧
      (rc (cls (ParLaws.toRep σ))).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (cls (ParLaws.toRep σ))).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H _).2 hsph
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl
end Core
section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
theorem equiv_transported_reciprocity_eq_local_reciprocity (w : PlE H) {n : ℕ} (σ : LocIrr w n) :
    T.e w (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (cls (ParLaws.toRep σ)) :=
  (T.e w).apply_symm_apply _
theorem transported_reciprocity_prod : RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w c n d hd σ σ' e
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.UpperTheory.One.M.locProd_eqG_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]
  congr 2
  funext i
  exact (_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity T hL w (σ i)).symm
theorem transported_reciprocity_satake : RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w n σ S hS
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FormDict.RecTLaws.hasSatGL_rec_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) σ S hS
  have hu : A.unr (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) := (T.unr w _).2 (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h1)
  exact ⟨hu, (T.frobEig w _ hu).trans (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h2)⟩
theorem transported_reciprocity_speh_of_generic_unitary_dual (hTZ : GlobalTheory.Published.GenericUnitaryDualGL) (hSC : GlobalTheory.Published.StandardCosocleGL) :
    RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w a d n hd P σ σ' hP hu hq
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.GlobalTheory.T.local_langlands_speh_product' _ _ _ w _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ'
    hu hg hq, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, T.tw, _root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]
end Record
theorem transported_reciprocity_prod_and_speh_and_satake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
      (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) :=
  fun hTZ hSC hL _ _ _ _ _ T => ⟨_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod T hL, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_speh_of_generic_unitary_dual T hL hTZ hSC, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_satake T hL⟩
end GlobalTheory.FormDict.RecTLaws
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReferenceLiftInjective
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.LiftRef.UpInjRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.RecTie Formalism.IndefR.Lev
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  intro _ _
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters OverRows
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y hH _ _ _ _ Rw a M tup Q _ _ j h1 h2 σ y hy h0 => ?_
  obtain ⟨i, rfl⟩ : ∃ i : Fin (w.st Z).toD7.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact thetaT_inj_real _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hH i σ y hy h0
end GlobalTheory.LiftRef.UpInjRows
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaT_mu0_injective_on_isot : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  first | exact @_root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LiftRef.UpInjRows.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RigidRawPacketEqPow
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Rigid
theorem rigid_raw_packet_eq_pow_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D₁ D₂ : D7) (p : TwPack D₁) (A : Finset (PlE D₁.host)) (ι : GlobalTheory.Mem.Top.TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (cf : CharFrame D₂) (C : NChoice D₂) (tp : TupTied D₂ cf C) (v : D₂.what₂.places.Pl), SameExport D₁ D₂ → BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2 → GlobalTheory.Mem.Top.TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ → PsiChoiceCompatible D₂ cf C tp → TwistedAt D₂ v → HEq (C.twI v) p.1 → HEq (C.Q v) p.2.1 → C.k' v = p.2.2.1 → HEq (tp.psi v) χ → (∀ z : ℂ, z ^ D₂.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D₂.what₂.LL, D₂.what₂.embLL x = z) → ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l p.1) ∧ HEq (rawPack C v) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  intro hc D₁ D₂ p A ι χ cf C tp v h hO hF hT htw hi hQ hk hχ hL
  obtain ⟨ψ₂, ι₂, A₂, hO₂, hF₂, hl, hpow⟩ := transfer h p A ι χ hO hF (C.twI v) (C.Q v) (C.k' v) (tp.psi v) hi hQ hk hχ
  obtain ⟨a, ha, hψ⟩ := pow_of_tied hc.cheb cf C tp v ψ₂ ι₂ hF₂ hT htw hO₂.2.2.1 hL
  refine ⟨a, by rw [Int.natAbs_natCast, ← hl]; exact ha, ?_⟩
  have e : rawPack C v = (⟨C.twI v, C.Q v, C.k' v, ψ₂ ^ (a : ℤ)⟩ : TwPack D₂) := by
    rw [zpow_natCast, ← hψ]
    rfl
  rw [e]
  exact hpow a
end GlobalTheory.HeightCounting.Rigid
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowDepthOfPrimitive
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowDepthTrue
open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up in
set_option maxHeartbeats 2000000 in
theorem rowDepth_allSt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  intro hPr
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine (hId.and (GlobalTheory.RowDepthTrue.stepW_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev Start)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x
  obtain ⟨hHo, hF, -⟩ := H.2 (w.st x.o.Z) hO
  exact rowDepth_rowRepR hPr.hc hPr.decay _ _ _ _ _ _ _ _ _ _ _ _ x.m.z.pins x.m.intersectionNumber_baseChange hHo hF
end GlobalTheory.RowDepthTrue
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_of_repOf_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => RowDepth (Dof x) (repOf x.r.Y) := by
  first | exact @_root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | exact _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt | (intros; apply _root_.GlobalTheory.RowDepthTrue.rowDepth_allSt_alt_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ScOfSck
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ChoiceEx
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
theorem sc_of_sck_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (h : _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL) : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL :=
  StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H P x l => by
    obtain ⟨s, h1, h2⟩ := exists_settings_conj (D := Dof x) l.a.elem.star l.b.Bs.cover
    obtain ⟨c, -⟩ := H P x l s h1 h2
    exact ⟨c⟩)
end GlobalTheory.HeightCounting.Up.ChoiceEx
end
end
end

