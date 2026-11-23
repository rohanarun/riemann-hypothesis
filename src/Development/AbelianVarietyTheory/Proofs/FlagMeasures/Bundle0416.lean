module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0046
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0015
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Development.AbelianVarietyTheory.Counterexamples.TransversalityLocal.FramePairFixatorUnitaryAndFixesFrame
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapsLargeGapPeriodIdentities
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
noncomputable section

namespace GlobalTheory.AmpTKGap

variable {k r : ℕ}

theorem side_bessel (hH : GlobalTheory.GapIn.Hyp) (L : LocBessel k r) (h : ℝ) (hgap : GapAtLeast L.ε L.lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hc : L.c ≠ 0) (hκ0 : 0 < L.κN) (hκt : L.κN ≠ ⊤)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (u : Fin k → ℝ) (μW : Measure (Mt k r)) (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : IsHCTypeW k r z u π)
    (hW : IsHaarOn (UWset k r z) μW) :
    ∃ l : L.Hs → Wp, (∀ x ∈ (GlobalTheory.AmpTK.rep L).sm, ∀ v ∈ (GlobalTheory.AmpTK.rep L).TK,
      Formalism.FourierDecayAlt.ThreeDimData.be z L.c π L.σ μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧ GlobalTheory.AmpTK.SmCW L l := by
  haveI := FiniteDimensional.complete ℂ Wp
  obtain ⟨μG, hG⟩ := GlobalTheory.SnMass.Inhab.exists_isHaarOn k r
  have hN := GlobalTheory.haarLie_isHaarOn_Nset k r L.κN hκ0 hκt.lt_top
  obtain ⟨νq, hq⟩ := GlobalTheory.exists_isQuotMeas_bessel_subgroup k r z μW L.μN μG hz hT hW hN hG
  obtain ⟨U, hS⟩ := GlobalTheory.AmpNormal.sideG_of hκt.lt_top hz hT hπ hW hG hq
  obtain ⟨t, ht, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r L.c hc
  obtain ⟨-, htc, hψ⟩ := htz z hz
  have hR : Formalism.MainNotions.S.IsURepOn (GG k r) (GlobalTheory.AmpTK.rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  obtain ⟨hS', hB⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π U L.c μW L.μN μG νq t ht htN htc hψ hS
  obtain ⟨-, hbe⟩ := hB (GlobalTheory.AmpTK.rep L) hR
  have hDG : (GlobalTheory.AmpTK.rep L).IsDG L.ε L.lam := ⟨L.hlam, L.hσ, h, hgap, hok⟩
  obtain ⟨l₁, hl₁⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r L.ε L.lam h (GlobalTheory.AmpTK.rep L) Wp z π U μW _ μG _ hDG hgap hok hS'
  have hti := GlobalTheory.BesselMove.inv_mem ht
  refine ⟨fun v => l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ v), fun x hx v hv => hbe l₁ hl₁ x hx v hv, ?_, ?_, ?_⟩
  · intro v hv w hw
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (v + w)) = _
    rw [map_add (f := _)]
    exact hl₁.1.1 _ (GlobalTheory.BesselMove.sig_sm hR hti hv) _ (GlobalTheory.BesselMove.sig_sm hR hti hw)
  · intro a v hv
    show l₁ ((GlobalTheory.AmpTK.rep L).σ t⁻¹ (a • v)) = _
    rw [map_smul]
    exact hl₁.1.2.1 _ _ (GlobalTheory.BesselMove.sig_sm hR hti hv)
  · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hti) hl₁.1.2.2.2

theorem exists_besselTK : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (h : ℝ),
    Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.c ≠ 0 → 0 < L.κN → L.κN ≠ ⊤ →
    ∃ (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq), GlobalTheory.AmpTK.BeTK L l l' ∧ GlobalTheory.AmpTK.SmCW L l ∧ GlobalTheory.AmpTK.SmCW L l' := by
  intro hH k r L h hgap hok hc hκ0 hκt
  obtain ⟨l, hl, hsl⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z L.π L.u L.μW L.hz.1 L.hz.2 L.hπ L.hμW.1
  obtain ⟨l', hl', hsl'⟩ := side_bessel hH L h hgap hok hc hκ0 hκt L.z' L.π' L.u' L.μW' L.hz'.1 L.hz'.2 L.hπ' L.hμW'.1
  exact ⟨l, l', ⟨hl, hl'⟩, hsl, hsl'⟩

end GlobalTheory.AmpTKGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticeWeightedCountLeExplicit
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
open ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.GlueCount

def locSpOf {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) : Formalism.L2.SG.CntLocal.LocSp D M where
  V := Vp D
  H p := locHerm M p (hA p).2.2.1
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p x y := baseChangeAt_form M p (hA p).2.2.1 x y

theorem exists_unif_at {D : D7} (p : PlF D) : ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := by
  haveI := (D.s.atP p).lf
  exact IsDiscreteValuationRing.exists_irreducible _

theorem exists_unifs (D : D7) : ∃ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], ∀ p, Irreducible (ϖ p) :=
  ⟨fun p => (exists_unif_at p).choose, fun p => (exists_unif_at p).choose_spec⟩

theorem one_mem_stabFix {D : D7} (U : Submodule D.host.E (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT U Λ := by
  refine ⟨(Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U).one_mem, ?_⟩
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

section Reps
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.Asm Formalism.L2.SG.CntLocal Module

theorem exists_glueReps (D : D7) (u u' : D.what₂.Word) (hT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2])
    (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂)
    (G' : LFlag (D.sp.Y 0) D.R.rS (Tn u')) (hz : G'.zt = G'.fl.z) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') (ZhatL (lf D F0) G'))) :
    ∃ s, IsGlueReps (VS D).hT (UPair D F0 G') (MMof D F0 G') s := by
  haveI : Fact HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  obtain ⟨hLat, -⟩ := mmChar_of local_unimodular_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
  by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 G')
  · obtain ⟨hK, hF, hN⟩ := field_dictionary_holds D
    obtain ⟨hC, hPD, hUr, hWr⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR _ G' hz rfl hP
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hcJ : ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsMaximal →
        cJ (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭 < finrank D.host.E (orthK (VS D).hT (UPair D F0 G')) := by
      intro 𝔭 _
      have := cJ_le (VS D).hT (UPair D F0 G') (MMof D F0 G') 𝔭
      rw [hWr]
      omega
    have hne := glueExists_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN (UPair D F0 G') hC hPD
      ⟨(VS D).L0, (VS D).standardTuple_isLattice, (VS D).baseLattice_isUnimodular⟩ (MMof D F0 G') hLat hI hcJ
    have hMC : MassConst D.host.E D.host.F (finrank D.host.E (orthK (VS D).hT (UPair D F0 G')))
        (cMass D.host.E D.host.F (D.R.k - 1)) := by
      rw [hWr]
      exact (cMass_spec hK hF (D.R.k - 1) (by omega)).2
    obtain ⟨s, hs1, hs2, hs3, -⟩ := gluing_mass_holds D.host.E D.host.F (VS D).V hK hF (VS D).hT (VS D).herm hN
      (UPair D F0 G') hC hPD (MMof D F0 G') hLat hI hne _ hMC
    exact ⟨s, hs1, hs2, hs3⟩
  · exact ⟨∅, isGlueReps_empty (glueSet_eq_empty (U := UPair D F0 G') hI)⟩

end Reps

theorem glueSum_le : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.L2.SG.Pf.LocCP.LocTied D → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), G'.zt = G'.fl.z → TotPos (Gval (lf D (X.Fu u)) G') → ∃ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s ∧ (s.Nonempty → (∃ Λ, IsRowLat D (X.Fu u) Λ ∧ G' ∈ Formalism.L2.SG.CntLocal.EZ ((Tu D u' : ℕ) : D.host.E) (X.Fu u) Λ (ZhatL (lf D (X.Fu u)) G')) ∧ glueSum (lf D (X.Fu u)) G' s ≤ 2 * (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) := by
  intro D X Y u u' hTied hk hT G' hz hTP
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  have hR : IsRowReps D (X.Fu u) (Y.what₂ u) := Y.rowsOK u
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (Formalism.L2.SG.CntLocal.GZ (Formalism.L2.SG.CntLocal.Tn u) (Formalism.L2.SG.CntLocal.Tn u')
      (ZhatL (lf D (X.Fu u)) G')) := hTP
  obtain ⟨s, hs⟩ := exists_glueReps D u u' hT (X.Fu u) (Y.what₂ u) hR G' hz hP
  obtain ⟨-, hchar⟩ := Formalism.L2.SG.Pf.Cnt.mmChar_of Formalism.L2.SG.Pf.Cnt.local_unimodular_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G'
    hz rfl hP
  have e4 := Formalism.L2.SG.Pf.Cnt.lattice_groupoid_holds D u u' hT (X.Fu u) (Y.what₂ u) hR _ G' hz rfl hP s hs
  refine ⟨s, hs, fun hne => ?_⟩
  obtain ⟨Λ, hΛ⟩ := hne
  refine ⟨⟨Λ, (hchar Λ).2 (hs.1 Λ hΛ)⟩, ?_⟩
  have hsum : glueSum (lf D (X.Fu u)) G' s = Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u)
      (ZhatL (lf D (X.Fu u)) G') * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
    exact e4.symm
  have hpos : 0 < glueSum (lf D (X.Fu u)) G' s := by
    unfold glueSum
    refine Finset.sum_pos (fun Λ' hΛ' => ?_) ⟨Λ, hΛ⟩
    haveI : Finite (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      (hs.2.2 Λ' hΛ').to_subtype
    haveI : Nonempty (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D (X.Fu u) G') Λ') :=
      ⟨⟨1, one_mem_stabFix _ _⟩⟩
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  have hnu : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') ≠ 0 := by
    intro h0
    rw [hsum, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hrow : ∃ Λ₁ ∈ Y.what₂ u,
      (Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) Λ₁ (ZhatL (lf D (X.Fu u)) G')).Nonempty := by
    by_contra hno
    push_neg at hno
    apply hnu
    unfold Formalism.L2.SG.CntLocal.nu
    rw [Finset.sum_eq_zero (fun Λ₁ h1 => by simp [Formalism.L2.SG.CntLocal.cntE, hno Λ₁ h1]), zero_div]
  obtain ⟨ϖ, hϖ⟩ := exists_unifs D
  have hfe := Formalism.L2.SG.Pf.formulaExplicitAt_of_eta D Formalism.L2.SG.Pf.Cnt.DualityBasisChange.frameBasisL_holds
    (fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hTied p) Y.δ Y.M Y.agree (locSpOf Y.δ Y.M Y.agree) u u' hT
    (X.Fu u) (Y.what₂ u) hR ϖ hϖ _ hP
  obtain ⟨-, hbdd, -, hαpos, hDI⟩ := Formalism.L2.SG.Pf.Cnt.densInputT_holds D hTied hk Y.δ Y.M Y.agree
    (locSpOf Y.δ Y.M Y.agree) u u' hT (X.Fu u) (Y.what₂ u) hR ϖ hϖ
  obtain ⟨hk2, P, q, l, hl, hS, hx⟩ := hDI
  have hsd := (Formalism.FourierDecayAlt.Final.tc_densChain Formalism.FourierDecayAlt.Final.tc_densSum Formalism.FourierDecayAlt.Final.tc_densLeTwo
    Formalism.FourierDecayAlt.Final.tc_densSize P q l _ _ _ _ hk2 hl hS hx).2
  have hdle : ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
      (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p ≤ 2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p :=
    (le_csSup hbdd ⟨_, hrow, rfl⟩).trans ((div_le_iff₀ hαpos).1 hsd)
  obtain ⟨Λ₁, hΛ₁, -⟩ := hrow
  have hc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) :=
    Formalism.L2.SG.Pf.Cnt.cExpl_pos' D u (X.Fu u) (Y.what₂ u) hR ⟨Λ₁, hΛ₁⟩
  have hm : 0 ≤ Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) :=
    Finset.sum_nonneg (fun _ _ => by unfold Formalism.MainNotions.S.wRow; positivity)
  have hN : 0 ≤ Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
      (ZhatL (lf D (X.Fu u)) G') := Real.sqrt_nonneg _
  have hfe' : Formalism.L2.SG.CntLocal.nu (Formalism.L2.SG.CntLocal.Tn u') (X.Fu u) (Y.what₂ u) (ZhatL (lf D (X.Fu u)) G') =
      Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E)
        ((Tu D u' : ℕ) : D.host.E) (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1) *
      ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
        (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := hfe
  rw [hsum, hfe']
  calc _ = (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) *
        ∏' p, Formalism.L2.SG.CntLocal.densP (locSpOf Y.δ Y.M Y.agree) Y.δ ϖ (Formalism.L2.SG.CntLocal.Tn u)
          (Formalism.L2.SG.CntLocal.Tn u') (ZhatL (lf D (X.Fu u)) G') p := by ring
    _ ≤ (Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) *
        Formalism.L2.SG.CntLocal.sqrtAbsNormOfScaledGram ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E)
          (ZhatL (lf D (X.Fu u)) G') ^ (D.R.k - 1)) * (2 * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p) :=
      mul_le_mul_of_nonneg_left hdle (by positivity)
    _ = _ := by ring

end GlobalTheory.GlueCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InverseMajorantLengthMomentLargeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMomentGap

theorem inv_len_moment_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a
  have hSG := (_root_.GlobalTheory.GapSetup.families_gap.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  have hS' := hS
  obtain ⟨hN, hF, hG, hSF⟩ := hS'
  have hb : 1 ≤ b := by
    obtain ⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
    have e1 := h7 (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e2 := h8 (Fin.last _)
    have e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ e3
    have e5 := neg_abs_le (lam (Fin.last _))
    linarith [e1.2]
  have hdg : 0 < dg ν := (hSF ν hν).2.1
  obtain ⟨m1, -, m3, m4⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq
    (hF ν hν) hG
  refine _root_.GlobalTheory.LowTypeMassGap.mass_low_gap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν
    (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw
  intro Q E hQ hE v hv hv1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2
  have hv1' : ‖(v : (R ν).H)‖ = 1 := hv1
  simp only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass
  have hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c := by
    filter_upwards [m1] with x hx
    obtain ⟨e1, e2⟩ := _root_.GlobalTheory.LastLen.last_len k r z hG.1 hG.2.1 _ hx
    refine ⟨?_, fun c => (e2 c).1⟩
    have := (e2 (Fin.last r)).1
    nlinarith
  have hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq :=
    (((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _
  have key := _root_.GlobalTheory.lintegral_prod_pow_le_of_moments (Mt k r) νq r q
    (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2)
    (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val))
    (fun c => (m3 _).div (m3 _))
    (fun c => by
      filter_upwards [hpos] with x hx
      exact div_nonneg (hx.2 _).le (hx.2 _).le)
    hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)
    (fun c => by
      have := Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν
        0 (r * q) (by omega) c v hv
      rwa [hv1, one_pow, mul_one] at this)
  have hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [← hpw]
  refine le_trans (lintegral_mono_ae ?_) key
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.1 (hx.2 a).le

end GlobalTheory.InvLenMomentGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalGlobalCongruenceLatticeTypedPlace
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IotaLocGlob

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

theorem bcP_osmul (p : PlF D) (a : 𝓞 D.host.E) (y : (VS D).V) :
    baseChange₂ D p (a • y) = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]

theorem smulLat_le (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    (locH Z p).smulLat (algebraMap _ _ (Formalism.MainNotions.S.LocNG.theta (Z.M p))) (lattice₂ D Z.M p Λ) ≤
      lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  exact IotaBP.typed_q_mem Z p g hs F F' hv

theorem mem_latP_XLam (Z : LocDat D) (p : PlF D) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ)
    (hX : v ∈ (locH Z p).X (scaled Z p (frame F))) : v ∈ lattice₂ D Z.M p (XLam Λ F) := by
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp F) hΛ
  have hsp : v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp F : Set (VS D).V)) := by
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨a, rfl⟩
    have e : scaled Z p (frame F) a.castSucc = frFac Z.δ p a.castSucc • baseChange₂ D p (F.fl.e a) := by
      simp only [scaled, GlobalTheory.LocExt.frame_castSucc]
    show scaled Z p (frame F) a.castSucc ∈ _
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F.fl.e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)
  have h : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp F)) : Set (Vp D p)) := by
    rw [hsat]; exact ⟨hv, hsp⟩
  exact h

theorem locglob : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (Z.M p).split ≠ none → ∀ a : 𝓞 D.host.E, (∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE (a : D.host.E) - 1 = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o) → (∀ p' : PlF D, p' ≠ p → ∃ o ∈ (D.s.atP p').O, (D.s.atP p').ιE (a : D.host.E) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) * o) → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → ∀ {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T'), ∀ y ∈ Λ, (a • y ∈ NgX Λ (gS D) F F' ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p y)) := by
  intro D Z p hsp a ⟨o, ho, hao⟩ hoth Λ hΛ T T' F F' y hy
  obtain ⟨g, hs⟩ := Option.ne_none_iff_exists'.1 hsp
  have hyp : baseChange₂ D p y ∈ lattice₂ D Z.M p Λ := BwdNP.baseChange_mem_localLattice Z hy p
  constructor
  · intro h
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', e⟩ := IotaBP.NgX_dec h
    obtain ⟨w, hw, w', -, hgq, -⟩ := IotaBP.gS_typed Z p g hs
    have h2 : baseChange₂ D p (a • y) = (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • baseChange₂ D p μ + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      rw [e, map_add (f := _), map_add (f := _), Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    have key : baseChange₂ D p y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
        (w • (baseChange₂ D p μ - o • baseChange₂ D p y)) + baseChange₂ D p ξ + baseChange₂ D p ξ' := by
      calc baseChange₂ D p y = (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y - ((D.s.atP p).ιE (a : D.host.E) - 1) • baseChange₂ D p y := by
            rw [sub_smul, one_smul]; abel
        _ = _ := by
            rw [hao, ← bcP_osmul, h2, hgq]
            simp only [smul_sub, smul_smul, mul_assoc]
            abel
    refine ⟨_, ?_, baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ) p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (IotaBP.xi_mem hξ') p,
      GlobalTheory.LocExt.bcP_Xsp_mem Z p F (Submodule.mem_inf.1 hξ).2, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' (Submodule.mem_inf.1 hξ').2, key⟩
    rw [GlobalTheory.NonGenericLocalCheck.theta_some (M := Z.M p) (h := hs)]
    refine Submodule.subset_span ⟨w • (baseChange₂ D p μ - o • baseChange₂ D p y), ?_, rfl⟩
    exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw
      (sub_mem (BwdNP.baseChange_mem_localLattice Z hμ p) (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
  · rintro ⟨A, hA, B, hB, C, hC, hBX, hCX, he⟩
    refine GlobalTheory.GenMass.GlueLoc.mem_of_bcP Z (IotaBP.isLattice_NgX_aux hΛ F F').fg fun p' => ?_
    by_cases hp : p' = p
    · rw [hp, bcP_osmul]
      have e : (D.s.atP p).ιE (a : D.host.E) • baseChange₂ D p y =
          baseChange₂ D p y + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • baseChange₂ D p y) := by
        rw [smul_smul, ← hao, sub_smul, one_smul]; abel
      rw [e]
      refine add_mem ?_ (IotaBP.smul_gS_mem Z p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p ho hyp))
      rw [he]
      refine add_mem (add_mem (smulLat_le Z p g hs Λ F F' hA) ?_) ?_
      · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (mem_latP_XLam Z p hΛ.fg F hB hBX)
      · exact IotaBP.localLattice_mono Z p le_sup_right (mem_latP_XLam Z p hΛ.fg F' hC hCX)
    · obtain ⟨o', ho', hao'⟩ := hoth p' hp
      have e : baseChange₂ D p' (a • y) = (D.s.atP p').ιE ((gS D : ℕ) : D.host.E) • (o' • baseChange₂ D p' y) := by
        rw [bcP_osmul, smul_smul, ← hao']
      rw [e]
      exact IotaBP.smul_gS_mem Z p' F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p' ho' (BwdNP.baseChange_mem_localLattice Z hy p'))

end GlobalTheory.IotaLocGlob
end
end

