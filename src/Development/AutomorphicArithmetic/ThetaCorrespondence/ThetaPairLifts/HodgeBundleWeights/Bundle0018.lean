module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0017
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionWeightBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.WeilBound.CoreStatements.ComplexPeriods.FlatDegreeResidues.FlatSlim
public import Development.WeilBound.CoreStatements.ResolutionCharZero.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0016
public import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsFlatUnitSection
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.FlatUnit
open GlobalTheory.FlatLine
theorem exists_flat_unit_section : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  intro hP D T j Y e o hY hE
  obtain ⟨N, hN, hA⟩ := _root_.GlobalTheory.T.flat_unit_exists_at_every_level hP D T j Y e o hY hE
  refine ⟨N, hN, fun w => ?_⟩
  classical
  let G : Psi T.Q.H → WTZ D.host.E := fun τ => wtOf (T.Q.Dw j) ((N : ℤ) • flatWt (T.Q.Dw j) τ) 0
  let φw : GlobalTheory.AllWt.Weight (T.Q.Dw j) →+ WTZ D.host.E :=
    { toFun := fun la => wtOf (T.Q.Dw j) la 0, map_zero' := GlobalTheory.AllWt.wtOf_zero,
      map_add' := fun a b => wtOf_add' a b }
  have hsum : wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0 = ∑ τ, (-w τ) • G τ := by
    rw [parWt_eq_sum]
    show φw _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => by simp) fun τ _ => ?_
    show φw _ = (-w τ) • φw _
    rw [map_zsmul, map_zsmul, smul_smul]
    congr 1; ring
  have hpair : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) τ, ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (G τ)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (G τ) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(G τ)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z τ => by
    obtain ⟨s, i, h⟩ := hA Z τ
    exact ⟨s, i, h, _root_.GlobalTheory.T.inverse_of_flat_unit_isIntegral hP D T j Y e o hY hE (N : ℤ) Z τ s i h⟩
  have hZ : ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂), ∃ s t : Rul Y.d.Xo₂ Y.d.c₂, (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ t ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * t = t ∧ s * t = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)) t z ≤ C)) ∧ ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • t) := fun Z => by
    obtain ⟨s, t, h⟩ := _root_.GlobalTheory.FlatUnitProd.exists_unit_sum _ _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r Y.U (xiR D) Z (Psi T.Q.H) G
      (fun τ => GlobalTheory.AllWt.even_wtOf _ _) (hpair Z) (fun τ => -w τ)
    refine ⟨s, t, ?_⟩
    rw [hsum]
    exact h
  choose s t hst using hZ
  haveI := CompFin.finite_comp Y.d.Xo₂ Y.d.c₂
  haveI := Fintype.ofFinite (Comp Y.d.Xo₂ Y.d.c₂)
  choose m hm hv using fun Z => (hst Z).2
  have hsZ : ∀ Z, s Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have htZ : ∀ Z, t Z ∈ GlobalTheory.AllWt.suppOn Z := fun Z => by
    rw [← (hst Z).1.2.2.2.1, mul_comm]; exact GlobalTheory.AllWt.mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hM0 : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun Z _ => (hm Z).ne')
  refine ⟨∑ Z, s Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • ∑ Z, t Z, ((∏ Z, m Z : ℕ) : Y.d.c₂.F),
    Submodule.sum_mem _ fun Z _ => (hst Z).1.1, hM0, ?_, ?_, ?_⟩
  · rw [mul_smul_comm, Finset.sum_mul_sum]
    have hd : ∑ Z, ∑ Z', s Z * t Z' = ∑ Z, idem Z := Finset.sum_congr rfl fun Z _ => by
      rw [Finset.sum_eq_single Z]
      · exact (hst Z).1.2.2.2.2.1
      · intro Z' _ hne
        rw [← (hst Z).1.2.2.1, ← (hst Z').1.2.2.2.1, mul_mul_mul_comm, idem_mul_idem_of_ne (Ne.symm hne),
          zero_mul]
      · intro h; exact absurd (Finset.mem_univ Z) h
    rw [hd, sum_idem]
  · intro la' v hv'
    have hV := isVal_valSet la' v hv'
    rw [Finset.smul_sum]
    refine val_sum_nonneg hV _ _ fun Z _ => ?_
    rcases mem_valOn_or (Z := Z) hv' with h | h
    · have hsplit : ((∏ Z, m Z : ℕ) : Y.d.c₂.F) • t Z =
          (∏ Z' ∈ Finset.univ.erase Z, m Z') • ((m Z : Y.d.c₂.F) • t Z) := by
        rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ Z), Nat.cast_mul, mul_comm, mul_smul]
        exact Nat.cast_smul_eq_nsmul Y.d.c₂.F _ _
      rw [hsplit]
      exact val_nsmul_nonneg hV _ (hv Z la' v h).2
    · rw [h _ (Submodule.smul_mem _ _ (htZ Z))]
      exact le_top
  · intro σ hσ kk
    choose C hC using fun Z => (hst Z).1.2.2.2.2.2 σ hσ
    have hL := GlobalTheory.AllWt.lieFacZ_pos (Dw := T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
    refine ⟨∑ Z, max (C Z) 0 / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D)
      (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0), fun y hy => ?_⟩
    have e1 : rdU (Y.U σ) (∑ Z, s Z) kk = ∑ Z, rdU (Y.U σ) (s Z) kk := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1]
    refine (pnorm_sum_le _ _ _ _ y).trans (Finset.sum_le_sum fun Z _ => ?_)
    by_cases hz : (⟨kk, y⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [le_div_iff₀ hL]
      have h1 := (hC Z ⟨kk, y⟩ hz).1
      calc _ = GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0)
            (s Z) ⟨kk, y⟩ := by unfold GlobalTheory.AllWt.homN GlobalTheory.AllWt.ptN; ring
        _ ≤ C Z := h1
        _ ≤ max (C Z) 0 := le_max_left _ _
    · have h0 : rdU (Y.U σ) (s Z) kk y = 0 := GlobalTheory.AllWt.rdU_eq_zero (Y.U σ) (hsZ Z) hz
      have : ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ)
          (wtOf (T.Q.Dw j) (parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) (s Z) kk) y = 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm; rw [h0, norm_zero, zero_mul]
      rw [this]
      exact div_nonneg (le_max_right _ _) hL.le
end GlobalTheory.FlatUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detLine_flat_unit_exists : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ N : ℕ, 0 < N ∧ ∀ w : GlobalTheory.AllWt.Psi T.Q.H → ℤ, ∃ (φ φ' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), φ ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) ∧ t ≠ 0 ∧ φ * φ' = t • 1 ∧ (∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v φ') ∧ ∀ σ, GoodEmb Y.d.c₂ σ → ∀ kk, ∃ C : ℝ, ∀ y ∈ ((Y.U σ).X kk).dom, ((Y.U σ).X kk).pnorm (GlobalTheory.AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) (GlobalTheory.FlatLine.parWt (T.Q.Dw j) fun τ => (N : ℤ) * w τ) 0) kk) (rdU (Y.U σ) φ kk) y ≤ C := by
  first | exact @_root_.GlobalTheory.FlatUnit.exists_flat_unit_section | exact _root_.GlobalTheory.FlatUnit.exists_flat_unit_section | (intros; apply _root_.GlobalTheory.FlatUnit.exists_flat_unit_section <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsInverseIntegralInvariant
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.KeyInvInt
open GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FlatLine
set_option maxHeartbeats 800000 in
theorem exists_inverse_integral_invariant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  intro _hP D T j Y e o hY _hE
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨hr, -, -, -, -, g, ee, F, -⟩ := hY.unf _ hσ
  have h1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨K, hK, hKv⟩ := GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ _ _ _ _ _ _ g ee hpq
  obtain ⟨ρ, hρ⟩ := GlobalTheory.KeyRoot.exists_keySec_pow_four κ k₁ k₂ k₆ k₄ _ _ _ _ _ _ g ee _ _ (Y.U _) K hσ
    (hY.unf _ hσ) hY.geo hpq hK hKv
  choose a ha hZ using hρ
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hKint : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 Y.d.c₂.F)),
      ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) w, 0 ≤ v (K : Rul Y.d.Xo₂ Y.d.c₂) := by
    by_cases hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p
    · exact fun w v hv => (GlobalTheory.KeyIntegralVal.key_valuation_bounds κ hkr _ _ _ _ _ _ g ee K hpq hg hK hKv w v hv).1
    · exact _root_.GlobalTheory.KeyValAny.key_valuation_nonneg κ hkr _ _ _ _ _ _ g ee K hpq hK hKv
  obtain ⟨t, ht, hint⟩ := _root_.GlobalTheory.RuleIntegral.exists_smul_nonneg _ _ _ _ _ _ (K : Rul Y.d.Xo₂ Y.d.c₂) (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂) a ha hZ hKint
  have hwt : ∀ (m : ℤ) (τ : D.host.E →+* ℂ) (i : ℕ), i < (T.Q.Dw j).mult τ → (wtOf (T.Q.Dw j) 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst _ _ (T.Q.Dw j)
  have hex : GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1 = -keyEx (T.Q.Dw j) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · rfl
    · simp only [GlobalTheory.AllWt.exOf, exZ, keyEx, Pi.neg_apply]
      exact hwt 1 τ i i.2
  refine ⟨((ρ.ρ⁻¹ : (Rul Y.d.Xo₂ Y.d.c₂)ˣ) : Rul Y.d.Xo₂ Y.d.c₂), t • (ρ.ρ : Rul Y.d.Xo₂ Y.d.c₂), t, ?_, ht, ?_, hint⟩
  · rw [hex]
    exact GlobalTheory.AllWt.inv_mem_secZ ρ.mem
  · rw [mul_smul_comm, Units.inv_mul]
end GlobalTheory.KeyInvInt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_invariant_integral : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @_root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | exact _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant | (intros; apply _root_.GlobalTheory.KeyInvInt.exists_inverse_integral_invariant <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsNonzeroSectionWeightBound
section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaSteep
section Tau
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open GlobalTheory.ThetaConst
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end Tau
section Key
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal GlobalTheory.ShFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Key
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.HSApp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.ThetaConst GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.AllWt in
theorem exists_theta_multiplication_rule (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (hM : 5 ^ 4 ∣ l.M)
    (Z : Comp Xo c) (s : ∀ τ, FlatSec U x Z τ) :
    ∃ f : secZ Xo c (exOf Dw ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw) 0), f.1 ∈ suppOn Z ∧ f ≠ 0 ∧
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), (∀ a, io a ∈ (algebraMap T.V T.Fr).range) →
        (letI := io.toAlgebra; LiesOn Z y.1) → GlobalTheory.SlopeRec.HasPhi y φ → evI y f.1 ≠ 0 →
          8 * φ / 625 ≤ (vV T.V (evI y f.1) : ℝ) := by
  obtain ⟨K, hK, hKv⟩ := exists_key Xo c hL.pos hL.good
  have h : HasPts U Z := hasPts U hL.pos hL.good hL.unf Z
  have h5 : Odd 5 := by decide
  obtain ⟨x₀, hx₀⟩ := exists_isAdm Dw (R := 5) (by norm_num)
  obtain ⟨u, f, hf, hfZ⟩ := exists_isGenRule_nonzeroOn (Xo := Xo) (c := c) h5 (by norm_num) hM x₀ Z
  refine ⟨⟨thetaOn h s K f, thetaOn_mem_secZ h s hK (IsTauRule.mem_sec h5 hf)⟩, thetaOn_mem_suppOn h s K f,
    fun h0 => ((nonzeroOn_thetaOn_iff h s K f).2 hfZ).ne_zero (congrArg Subtype.val h0), fun T io y φ hio hZ hφ hne => ?_⟩
  letI := io.toAlgebra
  have hid : evI y (idem Z) = 1 := evR_idem hZ y.2.1
  let ev : Rul Xo c →* T.Fr :=
    ⟨⟨evI y, by rw [← mul_one (evI y 1), ← hid, ← evI_mul, one_mul]⟩, evI_mul y⟩
  have hio0 : ∀ a, a ≠ 0 → vV T.V (io a) = 0 := fun a ha => by
    have h1 := (mem_range_iff T _).1 (hio a)
    have h2 := (mem_range_iff T _).1 (hio a⁻¹)
    have h3 := vV_mul (V := T.V) ((map_ne_zero io).2 ha) ((map_ne_zero io).2 (inv_ne_zero ha))
    rw [← map_mul, mul_inv_cancel₀ ha, map_one, show vV T.V (1 : T.Fr) = 0 by simp [vV]] at h3
    omega
  have hs : ∀ τ, ev (s τ).sig ∈ (algebraMap T.V T.Fr).range := fun τ => by
    have h1 := _root_.GlobalTheory.T.archimedean_section_integral_frame_of_laws hP hP.q2 E H Dw l Xo c r U x hL Z τ (ArchSec.ofConst (s τ)) T io y hio0 hZ
    change nval T.V 1 (ev (s τ).sig) = 0 at h1
    by_cases h0 : ev (s τ).sig = 0
    · exact h0 ▸ zero_mem _
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_eq_zero, Int.cast_eq_zero] at h1
    exact (mem_range_iff T _).2 h1.ge
  have e : evI y (thetaOn h s K f) = evI y f ^ 8 * (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    change ev _ = ev f ^ 8 * _
    rw [thetaOn, shift_sig]
    simp only [map_mul, map_pow, map_prod]
    rw [show ev (idem Z) = 1 from hid, one_mul, mul_assoc]
  have hB : ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q)) ∈ (algebraMap T.V T.Fr).range :=
    mul_mem (pow_mem (hKv T io y hio) _) (prod_mem fun τ _ => pow_mem (hs τ) _)
  change evI y (thetaOn h s K f) ≠ 0 at hne
  change _ ≤ (vV T.V (evI y (thetaOn h s K f)) : ℝ)
  rw [e] at hne ⊢
  have hf0 : evI y f ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  have b1 := tau_bound y hφ h5 (by norm_num) (fun _ => hx₀.spans (by norm_num) u) hf hf0
  have b2 : (0 : ℝ) ≤ vV T.V (ev K ^ (Dw.p + Dw.q) * ∏ τ, ev (s τ).sig ^ (4 * (Dw.p + Dw.q))) := by
    exact_mod_cast (mem_range_iff T _).1 hB
  rw [vV_mul (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne),
    show vV T.V (evI y f ^ 8) = 8 * vV T.V (evI y f) by simp [vV]]
  push_cast at b1 ⊢
  linarith
variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)
variable {X} in
set_option maxHeartbeats 1000000 in
theorem exists_section_of_theta_datum (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : FlatCore.Laws U x)
    (hM : 5 ^ 4 ∣ l.M) (TF : TorFlag Xo c) (s : ∀ τ, FlatLine.FlatSec U x Z τ)
    (hdeg : ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ ν, Centred y ν → ∃ φ : ℝ, 0 < φ ∧ PhiAt TF.X Z y ν φ) :
    ∃ θ : H0 (str₀ TF.X Z) (L₀ TF.X Z ((8 * ((Dw.p + Dw.q : ℕ) : ℤ)) • GlobalTheory.CompHt.hodgeWt Dw)) ⊤, θ ≠ 0 ∧
      ∀ (y : Y₀ TF.X Z) ν, Centred y ν → ∀ φ : ℝ, PhiAt TF.X Z y ν φ → ∀ j hj (m : ℤ),
        ν (H0.germ j y (memTop y) hj θ) = ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          8 * φ / 625 ≤ (m : ℝ) := by
  obtain ⟨f, hfZ, hf0, hf⟩ := _root_.GlobalTheory.ThetaSteep.exists_theta_multiplication_rule hP hL hM Z s
  obtain ⟨hs, -, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hL.geo
  haveI := hs
  haveI := hc
  haveI : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (FlagTan.dimFlag Dw) _
  haveI := GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected (str₀ TF.X Z)
  haveI : IsLocallyNoetherian (Y₀ TF.X Z) := LocallyOfFiniteType.isLocallyNoetherian (str₀ TF.X Z)
  have hN : Geo.Tor.IsNormalScheme (Y₀ TF.X Z) := fun y => by
    obtain ⟨_, _⟩ := TF.X.normal (inc₀ TF.X Z y)
    let e := (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  obtain ⟨θ, hθ⟩ := exists_extension hN (isLB_L₀ TF.X Z _) (dense_U₀ TF.X Z).nonempty (sec₀ TF.X Z _ f)
    fun y hy _ j hj => by
      obtain ⟨ν, hν⟩ := exists_centred y
      obtain ⟨_, -, T, io, y', g, ρ, φT, hρ, hφT, -, hpt, hval⟩ := hdeg y hy ν hν
      obtain ⟨g1, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
      refine ⟨T, g, g1, g2, fun hO hi => ?_⟩
      obtain ⟨a1, a2, -, a4⟩ := through_point TF.X Z y T io y' g hpt
      obtain ⟨u, hu⟩ := a4 _ f j hj hO hi
      rw [hu]
      refine mul_mem ⟨_, rfl⟩ ?_
      by_cases h0 : evI y' f.1 = 0
      · exact h0 ▸ zero_mem _
      have b1 := hf T io y' φT a1 a2 hφT h0
      have b2 := hφT.nonneg
      refine (mem_range_iff T _).2 ?_
      have : (0 : ℝ) ≤ vV T.V (evI y' f.1) := by linarith
      exact_mod_cast this
  refine ⟨θ, fun h0 => hf0 (eq_zero_of_sec₀ TF.X Z hfZ (by rw [← hθ, h0, map_zero])), fun y ν hν φ hφ j hj m hm => ?_⟩
  obtain ⟨T, io, y', g, ρ, φT, hρ, hφT, rfl, hpt, hval⟩ := hφ
  obtain ⟨-, g2⟩ := local_injective_of_centred hν T g ρ hρ hval
  obtain ⟨a1, a2, a3, a4⟩ := through_point TF.X Z y T io y' g hpt
  have hi := top_le_stalkPt y ((algebraMap T.V T.Fr).comp g) _ hj
  obtain ⟨u, hu⟩ := a4 _ f j hj a3 hi
  rw [← hθ, val_restr_pt le_top _ j (top_le_stalkPt y _ ⊤ (memTop y)), val_stalkPt y j (memTop y) hj,
    RingHom.comp_apply] at hu
  have hne : ν (H0.germ j y (memTop y) hj θ) ≠ 0 := hm ▸ WithZero.coe_ne_zero
  have hg0 : algebraMap T.V T.Fr (g (H0.germ j y (memTop y) hj θ)) ≠ 0 := fun h => hne (by
    rw [(injective_iff_map_eq_zero _).1 g2 _ ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective T.V T.Fr) _ h),
      map_zero])
  have hv := hval _ hne
  rw [hu] at hg0 hv
  rw [hm, vV_mul (left_ne_zero_of_mul hg0) (right_ne_zero_of_mul hg0), vV_unit, zero_add,
    show WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m from rfl] at hv
  have b1 := mul_le_mul_of_nonneg_left (hf T io y' φT a1 a2 hφT (right_ne_zero_of_mul hg0)) hρ.le
  push_cast at hv
  linarith
end Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end GlobalTheory.ThetaSteep
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatTensorSwapIsIso
section
section
theorem UpperTheory.Lit.Flat.flat_tensor_swap_isIso : _root_.GlobalTheory.T.FlatDegreeHypotheses :=
  fun _ _ _ => FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightArchimedeanContribution
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace PositivityTheory.Xj7N
open GlobalTheory GlobalTheory.CompHS GlobalTheory.Adelic
section Generic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Generic
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : D7} {V : (c.F →+* ℂ) → HSp D}
  {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
end Main
theorem weil_height_archimedean_contribution : NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → ∀ (N m : ℕ) (b : Module.Basis (Fin N) Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (g : Matrix (Fin N) (Fin m) Y.d.c₂.F) (A : (Y.d.c₂.F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) b g A → ∀ (σ : Y.d.c₂.F →+* ℂ) (ρ : Om Z →+* ℂ), ρ.comp (algebraMap Y.d.c₂.F (Om Z)) = σ → ∀ τ : ℕ, 0 < τ → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) τ t, ‖ρ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂))‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (genVal Z ((b i : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂))) ^ τ := by
  intro hNV hP D T j Y e o hY hf Z u t hG hB _ _ N m b g A hF σ ρ hρ τ _ f hfs
  have hd : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := fun σ hσ => by
    obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
    exact hdU.2.2.2.1
  have hD : 1 ≤ GlobalTheory.FlagTan.dimFlag (T.Q.Dw j) := by
    have h2 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q :=
      (hY.unf _ (goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom)).1
    have hm := D.R.two_le_m
    have hk := D.R.m_add_three_le_k
    have h3 : 2 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
      rw [← h2]; unfold Formalism.BasicNotions.Ranks.r; omega
    exact Nat.mul_pos (by omega) (Nat.choose_pos h3)
  obtain ⟨TF⟩ := DifferentiableLines.nonempty_toroidal_flag_bundle hP.p1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.CompHS.TorFlagEx.one_le_of_dimFlag hD)
  have hspan : ∀ σ, GoodEmb Y.d.c₂ σ → ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) u 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ w ∈ framesOn (Y.U σ) Z, P w.1 w.2 = Q w.1 w.2 := fun σ hσ P hPh => by
    obtain ⟨m', as, fs, hfs', hPQ⟩ := _root_.PositivityTheory.Xj7N.local_unit_map_surjective hNV hP D T j Y e o hY hf Z TF u hG hB σ hσ P hPh
    choose g' hg hgf using fun i => _root_.ModelDimension.cusp_form_extension_vanishing D T j Y e o hY hf Z TF u (fs i) (hfs' i)
    refine ⟨∑ i, as i • rdU (Y.U σ) (g' i), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨g' i, hg i, rfl⟩), fun w hw => ?_⟩
    rw [hPQ w hw]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hgf i σ hσ w hw]
  exact norm_small_le hY.unf hd (AllWt.even_wtOf u 0) hspan hF σ ρ hρ τ t f hfs
end PositivityTheory.Xj7N
end
end
end

