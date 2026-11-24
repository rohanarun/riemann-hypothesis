module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054

@[expose] public section

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainCells

theorem vol_dcell_and_disjoint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
  ∀ (r l t : ℕ) [MeasurableSpace (GL (Fin r ⊕ Blocks l t) k)] [BorelSpace (GL (Fin r ⊕ Blocks l t) k)]
    (m : Measure (GL (Fin r ⊕ Blocks l t) k)) [m.IsHaarMeasure], m (parahoric k (Fin r) (Blocks l t)) = 1 →
  ∀ [MeasurableSpace (GL (Fin (l * t)) k)] [BorelSpace (GL (Fin (l * t)) k)] (μK : Measure (GL (Fin (l * t)) k))
    [μK.IsHaarMeasure], μK (KO k (Fin (l * t))) = 1 →
  (∀ e : Fin (l * t) → ℤ, m.real (dcell ϖ (e ∘ (blkEquiv l t).symm)) =
    (resCard k : ℝ) ^ ((r : ℤ) * sumAbs e) * μK.real (cell k (Fin (l * t)) ϖ e)) ∧
  Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
    (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  intro k _ _ _ _ ϖ hϖ r l t _ _ m _ hm _ _ μK _ hμK
  refine ⟨fun e => ?_, _root_.GlobalTheory.CellDisjoint.dcell_pairwise_disjoint k ϖ hϖ r l t⟩
  obtain ⟨ho, hc⟩ := _root_.GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric k (Fin r) (Blocks l t)
  have h1 := _root_.GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul m _ ho hc (mtor (A := Fin r) ϖ (e ∘ (blkEquiv l t).symm))
  have h2 := _root_.GlobalTheory.measureReal_doubleCoset_eq_relIndex_mul μK (KO k (Fin (l * t))) SplitFlip.isOpen_KO SplitFlip.isCompact_KO (torusElt k _ ϖ e)
  have hs : sumAbs (e ∘ (blkEquiv l t).symm) = sumAbs e := by
    unfold sumAbs; exact Equiv.sum_comp (blkEquiv l t).symm (fun i => |e i|)
  have hm1 : m.real (parahoric k (Fin r) (Blocks l t) : Set _) = 1 := by simp [Measure.real, hm]
  have hK1 : μK.real (KO k (Fin (l * t)) : Set _) = 1 := by simp [Measure.real, hμK]
  rw [dcell, h1, cell, h2, hm1, hK1, GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement k ϖ hϖ, GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex k ϖ _ _ (blkEquiv l t), hs]
  simp

end GlobalTheory.ChainCells
