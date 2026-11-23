module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def ListPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def ListSt (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  ListPin (Dof x) x.m.z.R.toRealDat.toLevCh cDep K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

end GlobalTheory.HeightCounting.Up

end
