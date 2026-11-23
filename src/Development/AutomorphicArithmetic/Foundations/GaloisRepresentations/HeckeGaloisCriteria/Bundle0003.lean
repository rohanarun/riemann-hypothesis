module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.BuDefQEta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthDecomposition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExtraTr
section
noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (c : CutD D)

def raw : Gen.Raw D :=
  ⟨(layCut D c).eta, (layCut D c).eta_nonneg, (layCut D c).reEta _ (layCut D c).eta_nonneg, (layerCut_admissible D c).reEta _ _,
    (layCut D c).etaOk_reEta⟩

@[reducible] def ledTr (L : SizeData₂ D) : SizeData₂ (cut D c) := Gen.ledTr (raw c) L

theorem tiesTr (h : Ties D) : Ties (raw c).rec' := Gen.tiesTr (raw c) h h.tw_cover


set_option maxHeartbeats 1600000 in
def extraTr {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D} {cX : ExtraC}
    (ex : Extra D L gatT Gx Gy K X cX) :
    Extra (raw c).rec' (Gen.ledTr (raw c) L) (Gen.gatTr (raw c) gatT) (Gen.instTr (raw c) Gx) (Gen.latTr (raw c) Gy) K
      (Gen.divTr (raw c) X) cX :=
  Gen.extraTr (raw c) ex (nchTr c ex.nch) (nchTie_tr c ex.nch_tie) (xdTr c ex.xd)
    (show BaseLevelRowSide (cut D c) from ⟨sideTr c ex.p0.s⟩) (rrDef_tr c _ ex.rationalRoots_def) (ambTr c ex.amb) (ambTr c ex.amb0) (kapSharp_tr c)

end UpperTheory.GalC
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.FactsOfPre
section
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain _root_.GlobalTheory Tr

variable {D : D7}


set_option maxHeartbeats 1000000 in
@[reducible] def nchCut (c : CutD D) (x : NChoice D) : NChoice (cut D c) := { x with }

set_option maxHeartbeats 1000000 in
theorem nct_cut (c : CutD D) {x : NChoice D} (h : NChTie D x) : NChTie (cut D c) (nchCut c x) :=
  { h with
    twOf_eq := fun a => h.twOf_eq a.1
    twSide_eq := fun a => h.twSide_eq a.1
    Q_eq := fun a => h.Q_eq a.1
    psi_eq := h.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

end UpperTheory.GalC
end
end

