module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistTranslationsActAtLevelPrimeProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0419
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_mem_level_of_thetaDatum_ne_zero : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → L.Q = ∅ → IsIdemSum e (L.Pg ∪ ∅) → ∀ g : GA D S, (∀ v, (∀ PP ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) → GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig S.gram ΛS v) → ∀ x, (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ ∅ L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → Lev.finE S g ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L := by
  first | exact @GlobalTheory.SuppLevO.finE_mem_lev | exact GlobalTheory.SuppLevO.finE_mem_lev | (intros; apply GlobalTheory.SuppLevO.finE_mem_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsActOnRamifiedColumns
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwSProof

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem ramAt_fixed {p₀ : SplitPt D k} {β : Frame p₀ S n} {P : Pair k n} {φ₀ : GA D S → ℂ} (h : GlobalTheory.FinPl.RamAt β P φ₀) {g : GL n k}
    (hg : g • P = P) : rTrans (β.gl g) φ₀ = φ₀ := by
  obtain ⟨φ, ⟨heq, -, -⟩, rfl⟩ := h
  have := heq g P
  rw [hg] at this
  exact this.symm

theorem comb_foldr (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (η : ι → 𝓀[k]ˣ) (J : List ι) :
    ∃ c : GA D S →₀ ℂ, (∀ g ∈ c.support, g ∈ grpAt S fun x => ∃ i, x = (p i).v) ∧
      ∀ φ, J.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) φ = trc c φ := by
  have hsub : ∀ i, grpAt S (· = (p i).v) ≤ grpAt S fun v => ∃ i, v = (p i).v :=
    fun i => AllBij.congGrp_mono S (AllBij.idAt_mono fun v hv => ⟨i, hv⟩)
  induction J with
  | nil =>
    refine ⟨Finsupp.single 1 1, fun g hg => ?_, fun φ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]; exact Subgroup.one_mem _
    · exact (AllBij.act_single_one φ).symm
  | cons i l ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨-, -, C, -, hC, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl (η i) S (β i) (Q i)
    refine ⟨AllBij.cmul (Finsupp.mapDomain (β i).gl C) c, fun g hg => ?_, fun φ => ?_⟩
    · exact AllBij.cmul_mem (S := grpAt S fun v => ∃ i, v = (p i).v)
        (fun g h => hsub i (AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) C g h))
        (fun g h => hc g (Finsupp.mem_support_iff.2 h)) g (Finsupp.mem_support_iff.1 hg)
    · show sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) (l.foldr _ φ) = _
      rw [hl, hC, AllBij.sum_rep_eq]
      exact (AllBij.act_cmul _ _ _).symm

theorem sOp_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : 𝓀[k]ˣ) (i : ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ) := by
  obtain ⟨hbij, -, c, -, hc, -⟩ := ramBijective_holds D k (p i) n q (χ i) (hχ i) _ rfl ε S (β i) (Q i)
  have hT : ∀ φ, sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) ε φ = AllBij.act (Finsupp.mapDomain (β i).gl c) φ :=
    fun φ => (hc φ).trans (AllBij.sum_rep_eq _ _ _)
  have hC := AllBij.mapDomain_mem _ (AllBij.gl_mem (β i)) c
  refine ⟨by rw [hT]; exact AllBij.isContAut_act _ hφ.1, fun i' => ?_⟩
  rcases eq_or_ne i' i with rfl | hne
  · exact hbij.mapsTo (hφ.2 i')
  · rw [hT]
    exact AllBij.ramAt_act _ _ _ (fun x hx g => AllBij.grpAt_comm S (fun e => hne (hinj e)) (hC x hx)
      (AllBij.gl_mem _ g)) (hφ.2 i')

theorem foldr_keeps (hinj : Function.Injective fun i => (p i).v) (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n) (q : Unif k)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (ε : ι → 𝓀[k]ˣ) (l : List ι) {φ : GA D S → ℂ}
    (hφ : IsContAut S φ ∧ ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') φ) :
    IsContAut S (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) ∧
      ∀ i', GlobalTheory.FinPl.RamAt (β i') (Q i') (l.foldr (fun i φ' => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (ε i) φ') φ) := by
  induction l with
  | nil => exact hφ
  | cons i l ih => exact sOp_keeps hinj β Q q χ hχ (ε i) i ih

end Local

theorem twS : TwS' := by
  intro B X I hOk hPins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd J q χ hχ
  have hinj : Function.Injective fun i => (p i).v := _root_.GlobalTheory.AdForm.StdT.places_injective I hOk hPins l Z u p β Q L hStd
  have key : ∀ j (hj : j ≤ B.R.m) φ, RamT (I := I) (l := l) (u := u) (a := a) j φ → ∀ η : ι → 𝓀[k]ˣ,
      ∃ φ', RamT (I := I) (l := l) (u := u) (a := a) j φ' ∧ ∀ b y, A.rd θ j hj b φ' y =
        J.foldr (fun i f => sOp (β j i) (Q j i) q (resChar (χ i) (hχ i) q) (η i) f) (A.rd θ j hj b φ y) := by
    intro j hj φ hφ η
    obtain ⟨c, hc, hfold⟩ := comb_foldr (β j) (Q j) q χ hχ η J
    have hram := _root_.GlobalTheory.AdForm.ram_iff_scalar_ram I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
    have hR : ∀ b y, IsContAut _ (trc c (A.rd θ j hj b φ y)) ∧
        ∀ i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (trc c (A.rd θ j hj b φ y)) := by
      intro b y
      rw [← hfold]
      exact foldr_keeps hinj (β j) (Q j) q χ hχ η J ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩
    obtain ⟨φ', hφ'F, hφ'⟩ := _root_.GlobalTheory.AdForm.TransAct.twTransAct I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj c hc φ hφ.1
      (fun b y i g hg => ramAt_fixed ((hR b y).2 i) hg)
    refine ⟨φ', ?_, fun b y => (hφ' b y).trans (hfold _).symm⟩
    have hram' := _root_.GlobalTheory.AdForm.ram_iff_scalar_ram I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ' hφ'F
    exact hram'.2.2 fun b y i => by rw [hφ' b y]; exact (hR b y).2 i
  classical
  refine ⟨fun j η φ => if h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ then
    (key j h.1 φ h.2 η).choose else φ, ?_⟩
  intro j hj φ hφ
  have hram := _root_.GlobalTheory.AdForm.ram_iff_scalar_ram I hOk hPins l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ.1
  refine ⟨fun b y => ⟨hram.1 b y, fun i => hram.2.1 hφ b y i⟩, fun η => ?_⟩
  have h : j ≤ B.R.m ∧ RamT (I := I) (l := l) (u := u) (a := a) j φ := ⟨hj, hφ⟩
  simp only [dif_pos h]
  exact (key j hj φ hφ η).choose_spec

end GlobalTheory.AdForm.TwSProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfSiegelWeil
section
namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowNGP →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  intro h hB hTB hN c
  have hT : GlobalTheory.SnPos.StepThmBGP := by
    intro Cg cb Cw cT CT C0 _ _ A
    obtain ⟨CB, h0, a, b, H⟩ := hTB Cg cb Cw cT CT C0 A
    exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩
  obtain ⟨_h1, _h2, h3, h4, h5, h6, _h7, _h8, _h9⟩ := _root_.GlobalTheory.closed_steps_equal_words
  have hG : GlobalTheory.Core.One.RowGen1P :=
    GlobalTheory.Core.One.rowGen1P_of_siegelWeil_of_points (GlobalTheory.St.swxs_of_siegelWeil h)
      _root_.GlobalTheory.Core.One.normalCountSteps.1 _root_.GlobalTheory.Core.One.normalCountSteps.2.1 _root_.GlobalTheory.Core.One.normalCountSteps.2.2 h3 h4 h5 hB h6 hT
  exact ⟨oneOn_singleton_of_rows.1 hG c, oneOn_singleton_of_rows.2 hN c⟩

end GlobalTheory.Core.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LevAssembly

theorem gAt_mem_levG_of_red : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → (∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 → gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g ∈ Lev.levG S βS L := by
  intro D S βS L hH g PP hPP huniq hQ hSt hred hr
  have hone : ∀ PP' : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) →
      Formalism.L2.DIV.redFn βS PP' (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) = 1 := by
    intro PP' hne
    exact _root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D S βS _ PP' hSt (GlobalTheory.AdelicU.proj_emb_ne _ _ hne _)
  refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC S _ _, ?_⟩
  show Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L
  refine ⟨⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA S _, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP' hPP' h]; exact hred
    · rw [hone PP' h]; exact Subgroup.one_mem _
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hone PP' (hQ PP' hPP')]; exact Subgroup.one_mem _
  · show Formalism.L2.DIV.rTup βS L _ ∈ L.P.H
    rw [hH, Subgroup.mem_bot]
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP'.1 _) = 1
    by_cases h : PP'.1.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · rw [huniq PP'.1 PP'.2 h]; exact hr
    · rw [hone PP'.1 h]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.LevAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwisted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LocSuppTw

variable {D : D7}

theorem datum_specQ (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D)
    (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  by_cases hc : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hc] at hx
    have hG := left_ne_zero_of_mul hx
    unfold omegaG at hG
    split_ifs at hG with hd
    · refine ⟨hc.2, fun PP hPP => ?_, hd.2⟩
      obtain ⟨a, ha, -, -⟩ := hd.2
      rw [← ha ⟨PP, hPP⟩]
      exact Matrix.isUnits_det_units (a ⟨PP, hPP⟩)
    · exact absurd rfl hG
  · rw [if_neg hc] at hx
    exact absurd rfl hx

theorem idemSum_left {e : AE D} {P Q : Finset (Pl D.host.E)} (h : IsIdemSum e (P ∪ Q)) :
    ∃ e₁ : AE D, IsIdemSum e₁ P := by
  obtain ⟨e₁, h₁⟩ := GlobalTheory.ExportSeries.SplitSet.mono ⟨e, h⟩ Finset.subset_union_left
  exact ⟨e₁, h₁⟩

theorem isIntM_smul' {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) : IsIntM (c • N) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hN i j)

theorem redM_smul_of_res {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Pl D.host.E)
    (h1 : Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = 1) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM PP (c • N) = redM PP N := by
  ext i j
  have h2 : (c • N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := isIntM_smul' hc hN i j
  have hsub : (⟨(c • N) i j, h2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨N i j, hN i j⟩ :=
    Subtype.ext (by simp [Matrix.smul_apply])
  unfold redM
  rw [dite_eq_left h2, dite_eq_left (hN i j), hsub, map_mul, h1, one_mul]

end GlobalTheory.LocSuppTw

namespace GlobalTheory.LocSuppTw

theorem smul_mul_gen {R : Type} [CommRing R] {a b c : ℕ} (f : R) (A : Matrix (Fin a) (Fin b) R)
    (G : Matrix (Fin b) (Fin c) R) : (f • A) * G = f • (A * G) := by
  ext i k
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem tri_of_mul_eq {κ : Type} [Field κ] {n r t : ℕ} (hr : r ≤ n) {a b R : GL (Fin n) κ} (h : b * R = a)
    (ha : a ∈ blockTri (blkOf r t)) (hb : b ∈ blockTri (blkOf r t)) (ha1 : upperLeftBlock hr a = 1) (hb1 : upperLeftBlock hr b = 1) :
    R ∈ blockTri (blkOf r t) ∧ upperLeftBlock hr R = 1 := by
  have hR : R = b⁻¹ * a := by rw [← h, inv_mul_cancel_left]
  have hmem : R ∈ blockTri (blkOf r t) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨hmem, ?_⟩
  have hle := blockTri_blkOf_le (κ := κ) (n := n) r t
  have ha2 := hle ha
  have hb2 := hle hb
  unfold upperLeftBlock at ha1 hb1 ⊢
  rw [hR, extendMatrixByIdentityAlongIndices_mul (blkR hr) (Subgroup.inv_mem _ hb2) ha2, extendOne_inv (blkR hr) hb2, ha1, hb1, inv_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem finE_gAt_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → PP' = PP) → Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS ∧ Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g))) = 1 := by
  intro D S T ΛS βS βT L χ ξ e hSD hFr hST hId hH g x hx hgx PP hPP _
  have hHalf : IsHalf e x := by
    by_contra hn
    exact hx (if_neg fun h => hn h.1)
  obtain ⟨hI1, hU1, a, ha, haT, haH⟩ := datum_specQ S T βS βT L χ ξ L.Q e x hx
  obtain ⟨hI2, hU2, a', ha', ha'T, ha'H⟩ := datum_specQ S T βS βT L χ ξ L.Q e (actO S T g 1 x) hgx

  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin S.rank) (Lev.EAf D), γ = βS⁻¹ * Lev.finE S g * βS := ⟨_, rfl⟩
  have hact : frMapO S T βS βT (actO S T g 1 x) = frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
    rw [hγ]
    exact GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x

  obtain ⟨e₁, h₁⟩ := idemSum_left hId
  obtain ⟨hc, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum h₁
  have hcc : toEAf D e₁ * toEAf D e₁ = toEAf D e₁ := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self h₁]
  have hmul : toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      toEAf D e₁ • (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := smul_mul_gen _ _ _
  have hI2' : IsIntM (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [← hact]
    exact hI2
  have hu1 : IsIntM (toEAf D e₁ • frMapO S T βS βT x) := isIntM_smul' hc hI1
  have hu1g : IsIntM (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [hmul]
    exact isIntM_smul' hc hI2'
  have hsupp : ∀ i j, toEAf D e₁ * (toEAf D e₁ • frMapO S T βS βT x) i j = (toEAf D e₁ • frMapO S T βS βT x) i j := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
  have hred1 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x) = redM PP (frMapO S T βS βT x) :=
    fun PP hP => redM_smul_of_res hc PP (hres PP hP) hI1
  have hred2 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) =
      redM PP (frMapO S T βS βT (actO S T g 1 x)) := by
    intro PP hP
    rw [hmul, hact]
    exact redM_smul_of_res hc PP (hres PP hP) hI2'

  obtain ⟨hγ1, hγ2, htop⟩ := _root_.GlobalTheory.HalfUnit.int_of_unit_tops (D := D) T.rank S.rank hST L.Pg e₁ h₁ (toEAf D e₁ • frMapO S T βS βT x) γ
    hu1 hu1g hsupp (fun PP hP => by rw [hred1 PP hP]; exact hU1 PP hP) (fun PP hP => by rw [hred2 PP hP]; exact hU2 PP hP)
  obtain ⟨hγ3, hγ4⟩ := _root_.GlobalTheory.ConjIntegral.conj_smul_isIntM S ΛS βS hSD hFr (Lev.finE S g) (GlobalTheory.LevSplit.finE_mem_UA S g) γ hγ e₁ hγ1 hγ2

  obtain ⟨hεε, hεc⟩ := _root_.GlobalTheory.IdemConjSum.idemSum_add_conj_idem L.Pg e₁ h₁
  obtain ⟨k, -, hk⟩ := _root_.GlobalTheory.GfCut.exists_cut S (GlobalTheory.LevelNbhd.finPartG S g) (e₁ + cA D e₁)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hkE := _root_.GlobalTheory.FineCut.finE_cut S βS (GlobalTheory.LevelNbhd.finPartG S g) k (e₁ + cA D e₁) hk
  rw [GlobalTheory.SuppLevO.finE_finPartG, ← hγ] at hkE
  obtain ⟨hkSt, hkred⟩ := _root_.GlobalTheory.FrameIdem.cut_mem_St_red S.rank βS γ (Lev.finE S k) L.Pg e₁ h₁ hγ1 hγ2 hγ3 hγ4 hkE
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g :=
    (_root_.GlobalTheory.CompIdem.projV_eq_of_idem S _ (GlobalTheory.LevelNbhd.finPartG S g) k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e₁ h₁ PP hPP) hk).trans
      (GlobalTheory.SuppLevO.proj_finPartG S g _)
  have hyv : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g :=
    GlobalTheory.AdelicU.proj_emb_self (σ := D.sp.cm.sig) (J := S.gram) _ _

  have hkloc := (_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D S βS ΛS hFr k).mp hkSt
  have hyS : Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) ∈ Formalism.L2.DIV.St βS := by
    rw [_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D S βS ΛS hFr]
    intro w
    by_cases hw : w = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)
    · subst hw
      rw [hyv, ← hpk]
      exact hkloc _
    · show GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram w (GlobalTheory.AdelicU.emb D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
        (GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) g)) ∈ _
      rw [GlobalTheory.AdelicU.proj_emb_ne (h := hw)]
      exact one_mem _

  have hk' : Lev.finE S k = Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g) *
      Lev.finE S ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  have hk'S : Lev.finE S ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) ∈ Formalism.L2.DIV.St βS := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hkSt
  have hproj1 : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
      ((gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hpk, hyv, inv_mul_cancel]
  have hR : Formalism.L2.DIV.redFn βS PP (Lev.finE S k) =
      Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) g)) := by
    rw [hk', Formalism.L2.DIV.redFn_mul hyS hk'S, _root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D S βS _ PP hk'S hproj1, mul_one]

  have hmulGL : a' ⟨PP, hPP⟩ * Formalism.L2.DIV.redFn βS PP (Lev.finE S k) = a ⟨PP, hPP⟩ := by
    apply Units.ext
    rw [Units.val_mul, hkred PP hPP, ha' ⟨PP, hPP⟩, ha ⟨PP, hPP⟩]
    have htopPP := htop PP hPP
    rw [hred2 PP hPP, hred1 PP hPP] at htopPP
    exact htopPP
  have hrb : ∀ b : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1), (fun PP => upperLeftBlock L.hr (b PP)) ∈ L.P.H →
      ∀ PP, upperLeftBlock L.hr (b PP) = 1 := by
    intro b hb PP'
    rw [hH, Subgroup.mem_bot] at hb
    exact congrFun hb PP'
  obtain ⟨h1, h2⟩ := tri_of_mul_eq L.hr hmulGL (haT _) (ha'T _) (hrb a haH _) (hrb a' ha'H _)
  rw [← hR]
  exact ⟨hyS, h1, h2⟩

end GlobalTheory.LocSuppTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisatiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  first | exact @GlobalTheory.QFinMain.qFin_of_pin | exact GlobalTheory.QFinMain.qFin_of_pin | (intros; apply GlobalTheory.QFinMain.qFin_of_pin <;> assumption)
end

