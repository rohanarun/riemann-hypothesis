module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0445

@[expose] public section

namespace GlobalTheory

theorem rowsPos_typeP : Formalism.L2.SG.RowsPos.TypeP :=
  _root_.GlobalTheory.TypeAsm.TopGap.typeBound_of_gap (GlobalTheory.GapIn.hyp_of_uniqGap _root_.GlobalTheory.uniqGap_and_besselOfW.1) _root_.GlobalTheory.uniqGap_and_besselOfW.2

end GlobalTheory
