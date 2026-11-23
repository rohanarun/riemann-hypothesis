module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.ServiceOfTiedSelection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Fc

def Lg1 (KP : ∀ B : GlobalTheory.Mem.Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (r : V4.Slot → Prop) : Prop :=
  ∃ R : V4.Slot, LargeBaseCondition KP Q R ∧ r (sAnd Q' R)

end GlobalTheory.Fc

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Cp

open _root_.Formalism _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Rows

section Col

variable {X : Formalism.L2.Col.Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}

@[reducible] def ColRec3.toS (c : GlobalTheory.Cp.ColRec3 X A3 P1 ψ1) : Formalism.L2.DIV.ColRec3 X A3 P1 ψ1 where
  Pr := c.Pr
  Rk := c.Rk
  W := c.W
  Ch := c.Ch
  sel := c.sel
  Sg := c.Sg
  hX := c.hX
  Lv := c.Lv
  Xg := c.Xg
  m2 := c.m2
  Gc := c.Gc
  mu := c.mu
  cst := c.cst
  Li := c.Li
  hL := c.hL
  hP := c.hP
  Mem := c.Mem
  wd := c.wd
  b := c.b
  hY := c.hY
  Am := c.Am
  hK := c.hK
  hF := c.hF
  hE := c.hE
  ev := c.ev

@[reducible] def ColRec3.ofS (c : Formalism.L2.DIV.ColRec3 X A3 P1 ψ1) : GlobalTheory.Cp.ColRec3 X A3 P1 ψ1 where
  Pr := c.Pr
  Rk := c.Rk
  W := c.W
  Ch := c.Ch
  sel := c.sel
  Sg := c.Sg
  hX := c.hX
  Lv := c.Lv
  Xg := c.Xg
  m2 := c.m2
  Gc := c.Gc
  mu := c.mu
  cst := c.cst
  Li := c.Li
  hL := c.hL
  hP := c.hP
  Mem := c.Mem
  wd := c.wd
  b := c.b
  hY := c.hY
  Am := c.Am
  hK := c.hK
  hF := c.hF
  hE := c.hE
  ev := c.ev

end Col

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem divRows3G_iff (P : RowSideFamily ex) : GlobalTheory.Cp.DivRows3G P ↔ Formalism.L2.DIV.DivRows3G P :=
  ⟨fun h => ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩,
    fun h => ⟨h.sharpRR, h.baseRR, h.divisionRows_rationalLift, h.thTheta, ⟨h.num.Ij, h.num.jw, h.num.etaJ⟩, h.colsBk⟩⟩

end GlobalTheory.Cp

end
end

