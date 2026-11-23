module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
section
noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwJoin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
    (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)
    (cf : CharFrame D) : Type 1 where
  X : RealSide D
  Γ_eq : X.Γ = G
  grp_eq : HEq X.grp iG
  fin_eq : HEq X.fin fG
  Pl0_eq : X.Pl0 = Pl0
  I0_eq : X.I0 = I0
  T_eq : X.T = T
  core_eq : X.core = C
  alg_eq : HEq X.alg aC
  R_eq : HEq X.R R
  F_eq : HEq X.F F
  cG_eq : HEq X.cG cG
  geo_eq : HEq X.geo geo
  A3_eq : HEq X.A3 A3
  Y : SerSide X (twEOf xd)
  S_eq : Y.S = S
  YS_eq : HEq Y.YS YS
  gal : GalSide D
  cf_eq : gal.cf = cf
  lam_eq : gal.lam.C = cf
  C_eq : X.R.C = cf
  field : FieldOk X
  cg : CGTrue hL D gal.wd
  base : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)

theorem TwJoin.Sb_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop} {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D}
    [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw} {YS : NExpRealS R cG S}
    {cf : CharFrame D} (a : TwJoin hL D nch xd first R F cG geo S YS cf) : a.X.R.Sb = R.Sb := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7, h8, hR, -, -, -, hA, -⟩ := a
  cases X
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hR hA ⊢
  subst h1 h4 h5 h6 h7
  cases h2; cases h3; cases h8; cases hA; cases hR
  rfl

end GlobalTheory.TwInputs

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
section
noncomputable section
namespace GlobalTheory.CoefDuty.OPinModel
open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.Mem.Col2

def LabFixed (D : D7) : Prop :=
  GlobalTheory.SerSys.LabTie D fun k => @GlobalTheory.Mem.TypePl.labDat (D.host.g k) ⟨D.host.g_prime k⟩

theorem labFixed_withLoc {D : D7} (L : LocAll (lay0 D)) : LabFixed (withLoc L) ↔ LabFixed D := Iff.rfl

theorem labFixed_of_typesTrue {D : D7} {P : PiBar D.host} {W : Omg D.host} (h : TypesTrue D.ntypes P W) : LabFixed D :=
  fun k => ⟨(h.teich k).symm, h.ser k⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

end GlobalTheory.CoefDuty.OPinModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

def RealSide.ofPins {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (p : GlobalTheory.Mem.R3.Pins R F cG)
    (h : GlobalTheory.Mem.R3.Holds R F) (g : GlobalTheory.RealGeo.InGeo geo) (f : Finite T) (hh : HostHyp D) (s : ∀ j, FWT.VStd D j)
    (z : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) : RealSide D :=
  { Γ := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, core := C, R := R, F := F, cG := cG, geo := geo,
    char := RealDat3.characterisation_of_weak p.char h.aux.ex, phs := p.phs, guard := p.keep.guard, valKs := p.keep.valKs,
    idem := by obtain ⟨_, _, _, h2, _⟩ := p.keep.grp; exact h2
    unif := h.prim.unif, integral := h.aux.integral, inGeo := g, finT := f, host := hh, std := s, size := z }

section Second

variable {D : D7} (X : RealSide D) (S : RatDat D.ntw) {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ} {Pq} {hL} {eig} {θ}
  (Bs : SideB D cf Rw low Pq S hL eig θ) (fi : ∀ i : Fin D.R.m, FormsIso (S.A ((i : ℕ) + 1)) (X.R.FW i))
  (geq : ∀ (i : Fin D.R.m) (g : S.G), X.cG (X.R.eG ((fi i).eG g)) = S.eG g)

def formsOf : NExpRealS X.R X.cG S :=
  ⟨fi, geq, Bs.rho, Bs.chiL, Bs.eF, fun i j b h1 h2 => ⟨1, one_ne_zero,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩, Bs.act⟩

def heckeOf : NExpRealH X.R X.cG S (formsOf X S Bs fi geq) :=
  { hL := hL, hs := Bs.hs, cHk := fun i b k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P) ^ k
    cHk_zero := fun _ _ _ => pow_zero _, cHk_unit := fun i b P => ((Bs.cHk i b P).isUnit.map _).pow _
    cHk_pow := fun _ _ _ _ => by rw [pow_one], hkEq := Bs.hkEq }

end Second

end GlobalTheory.TwInputs

end
end

