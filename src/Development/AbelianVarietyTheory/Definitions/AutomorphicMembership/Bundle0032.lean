module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure GoodO (D : D7) (nch : NChoice D) (xd : ThData D) : Prop where
  tw : ∃ I : TwIn D, I.E = twEOf xd ∧ DQ.GoodAllAt D nch I ∧ GlobalTheory.HeightCounting.GoodCl D nch I
  sep : ∀ v v', D.what₂.muAt v ≠ D.what₂.mu0 → D.what₂.muAt v' ≠ D.what₂.mu0 → nch.twI v ≠ nch.twI v' → Disjoint (nch.Q v) (nch.Q v')

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure Wit (𝒮 : Slots) (K : Ctx) (w : ColW B f T) (Z : w.Lt) (O : Obj2 (w.D Z)) : Type 1 where
  isOver : K.Over B.toPre
  forced : Forced K B T
  Wt : Set B.places.Pl
  pin : ColPin w
  coh : Coh B T
  vol : Formalism.L2.Theta.VolTieG (w.D Z)
  col : ColumnDataSplitPrimes K w Z
  what₂ : RowsT K w Z Wt O.p0
  rx : 𝒮.Rx K B f T w Z Wt O.p0 what₂
  lev : O.lev = col.full.1.base.lev0
  errX : O.errX = Formalism.L2.Herm.toErrXS col.full.1
  n : NchT w Z Wt O.nch
  nx : 𝒮.Nx K B f T w Z Wt O.p0 what₂ O.nch n O.xd
  sx : 𝒮.Sx K B f T w Z Wt O.p0 what₂ col.toColT
  ker0 : KerFam (w.D Z) col.Gt col.cmp (w.tw Z) O.Gy
  ker_eq : (⟨O.gatT, O.cmp, O.tw, O.ker⟩ : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)),
    KerFam (w.D Z) Gt cmp tw O.Gy) = ⟨col.Gt, col.cmp, w.tw Z, ker0⟩
  ker : KerT col.toColT O.X O.Gy ker0
  div : DivT n O.X
  th : ThT n O.th
  obj : ObjT O what₂
  ox : 𝒮.Ox K B f T w Z Wt O what₂
  real : Formalism.L2.Theta.RealTied (w.D Z)
  dsig_eq : ∀ τ, Z.S.dsig τ = Vol.trueDsig B.R (B.hc τ)
  gauge : O.gauge.IsGauge
  good : GoodO (w.D Z) O.nch O.xd

def Built.wit {𝒮 : Slots} {K : Ctx} {w : ColW B f T} {Z : w.Lt} {c : V4.Core K (w.st Z) f T} (b : Built 𝒮 K w Z c)
    (h : GoodO (w.D Z) c.O.nch c.O.xd) : Wit 𝒮 K w Z c.O :=
  { b with isOver := c.isOver, forced := c.forced, Wt := c.Wt, vol := (b.g Z.W Z.V Z.S Z.N).1, real := c.real, dsig_eq := c.dsig_eq,
           gauge := c.gauge_def, good := h }

structure WPt (𝒮 : Slots) (K : Ctx) : Type 1 where
  B : Base
  f : Fr B.toPre
  T : TwDat B
  w : ColW B f T
  Z : w.Lt
  O : Obj (w.D Z)
  x : Wit 𝒮 K w Z (ofObj O)

def WPt.Is {𝒮 : Slots} {K : Ctx} (p : WPt 𝒮 K) (D : D7) (O : Obj D) : Prop := (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨p.w.D p.Z, p.O⟩

abbrev PinT (𝒮 : Slots) (Bd : GlobalTheory.Fc.BdT) : Type 1 := ∀ (K : Ctx) (p : WPt 𝒮 K) (c : ℝ), Bd (p.w.D p.Z) p.O c → Prop

def linkOf {𝒮 : Slots} {Bd : GlobalTheory.Fc.BdT} (P : PinT 𝒮 Bd) : GlobalTheory.Fc.LkT Bd := fun K β c b =>
  ∃ (p : WPt 𝒮 K) (b' : Bd (p.w.D p.Z) p.O c), P K p c b' ∧
    (⟨β.D, β.O, b⟩ : Σ (D : D7) (O : Obj D), Bd D O c) = ⟨p.w.D p.Z, p.O, b'⟩

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.AtMember

variable {D : D7}

structure CorePin (J : Core D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop where
  laws : LawsCore J
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  pb : J.pb = pb

theorem CorePin.reCore {J : CoreJ D} {pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)} (h : CorePin J.toCore pb) {dict mu chiW x₀ cE}
    (hM : LawsM (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore) : CorePin (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore pb :=
  ⟨⟨hM, h.laws.cuspMul, h.laws.latZ, h.laws.cuNe, h.laws.expo⟩, h.canon, h.rank, h.pb⟩

structure FieldTies (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  del : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  del' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D
  small : ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

def HalfAt (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def NumAtL (L : SizeData₂ D) (x : ℝ) : Prop :=
  DV.KapDef D ∧ (∃ (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), GlobalTheory.BigOn.PageNum Tp x) ∧ FieldSmall D L

end GlobalTheory.AtMember
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.Model3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}

theorem fk_zero (t : RowsT K w Z Wt p0) (v : B.places.Pl) (hv : v ∉ Wt) (j : Fin B.R.m) :
    FK K.s (w.D Z) (j.1 + 1) (B.places.resChar v) = 0 := by
  by_contra h
  apply hv
  rw [t.exact]
  refine ⟨j, _, Or.inl rfl, Or.inr (Or.inr ?_)⟩
  have e : (w.D Z).plEq.symm ((w.D Z).plEq v) = v := Equiv.symm_apply_apply _ _
  show FK K.s (w.D Z) (j.1 + 1) ((w.D Z).what₂.places.resChar ((w.D Z).plEq.symm ((w.D Z).plEq v))) ≠ 0
  rw [e]
  exact h

section Idx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T' D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0}

end Idx

theorem fTypeG_ne {D : D7} (h : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : FTypeG D j ≠ 0 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 0 < Fintype.card D.what₂.Tau := by rw [D.what₂.card_Tau]; exact GaloisStage.f_pos D.R
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hf
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  let i : Fin (D.R.sigW j).1 := ⟨D.R.k + j - 1 - 1, by rw [hs]; omega⟩
  have e := (h j h1 h2 τ).1 i
  have l := DV.aPlusQ_last D j h1 h2 τ
  have p : (1 : ℤ) ≤ D.what₂.kaBig j τ i := by
    have : (1 : ℚ) ≤ (D.what₂.kaBig j τ i : ℚ) := e ▸ l
    exact_mod_cast this
  have q : 0 < fockDeg D j := by
    unfold fockDeg
    refine Finset.sum_pos' (fun t _ => add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) ⟨τ, Finset.mem_univ _, ?_⟩
    refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    exact abs_pos.2 (by omega)
  unfold FTypeG
  have : (0 : ℝ) < (fockDeg D j : ℝ) := by exact_mod_cast q
  linarith

theorem type_mem (t : RowsT K w Z Wt p0) (v : B.places.Pl) (i : Fin 2) (hv : B.places.resChar v = B.host.g i) : v ∈ Wt := by
  by_contra h
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  have z := fk_zero t v h ⟨0, hm⟩
  unfold FK at z
  rw [if_pos ⟨i, hv⟩] at z
  exact fTypeG_ne t.r.Y.kap 1 le_rfl hm z

end GlobalTheory.Mem.Top.Bl.Model3

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
  Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) (X0 : BaseLevelRowSide D) (tp : D.what₂.Tup → T)
  (eG : G ≃* G0g D.nd)


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure AllT : Type where
  jA : ∀ μ, (Fin (rDim D A P1 ψ1 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ
  jA0 : ∀ μ, (Fin (rDim D A P0 ψ0 (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb μ
  eMt : ∀ (i : Fin D.R.m) μ, (Fin (lDim D A P0 ψ0 i (tp μ)) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ ((i : ℕ) + 1)
  formsA : ∀ μ, FormsTie D.what₂.embLL (jA μ) (rH D A P1 ψ1 (tp μ)) (rE D A P1 ψ1 (tp μ)) (D.what₂.eOp μ)
  latA : ∀ μ, OLatTie D.what₂.embLL (D.what₂.Mtilde μ) (jA μ) (rNab D A P1 ψ1 (tp μ))
  formsAtBottomLevel : ∀ μ, FormsTie D.what₂.embLL (jA0 μ) (rH D A P0 ψ0 (tp μ)) (rE D A P0 ψ0 (tp μ)) (X0.s.eOp μ)
  latA0 : ∀ μ, OLatTie D.what₂.embLL (X0.s.Mtilde μ) (jA0 μ) (rNab D A P0 ψ0 (tp μ))
  formsL : ∀ (i : Fin D.R.m) μ, FormsTie D.what₂.embLL ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap)
    (lH D A P0 ψ0 i (tp μ)) (lE D A P0 ψ0 i (tp μ)) (D.what₂.eMt μ ((i : ℕ) + 1))
  latL : ∀ (i : Fin D.R.m) μ, OLatTie D.what₂.embLL (D.what₂.MtLat μ ((i : ℕ) + 1))
    ((D.what₂.jMt μ ((i : ℕ) + 1)).comp (eMt i μ).toLinearMap) (lNab D A P0 ψ0 i (tp μ))
  cen : ∀ μ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g : G, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g)) →
    (∀ x, (RowSide.sharp D).cen μ z (jA μ x) = jA μ ((Formalism.L2.Rows.rOp D A P1 ψ1 (tp μ) a).mulVec x)) ∧
    (∀ x, X0.s.cen μ z (jA0 μ x) = jA0 μ ((Formalism.L2.Rows.rOp D A P0 ψ0 (tp μ) a).mulVec x)) ∧
    ∀ (i : Fin D.R.m) x, D.ntypes.cenMt μ ((i : ℕ) + 1) z (D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ x)) =
      D.what₂.jMt μ ((i : ℕ) + 1) (eMt i μ (((A.fam.L i (tp μ)).S.lvlOp (A.fam.L i (tp μ)).r (A.fam.lvlA P0 ψ0).P
        (A.fam.lvlA P0 ψ0).ψ a).mulVec x))

def SameOn {K : Type} {n n' : ℕ} {V : Type} (j : (Fin n → K) → V) (j' : (Fin n' → K) → V) : Prop :=
  n = n' ∧ ∀ x x', (∀ (a : Fin n) (a' : Fin n'), (a : ℕ) = a' → x a = x' a') → j x = j' x'

end General

section Cols

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px)

def tAll (a : I.ι) : R3.TupU I Set.univ := ⟨I.tup a, Or.inr ((R3.tup_mem_tuOf I).2 (Set.mem_univ a))⟩

end Cols

section Forms

open _root_.Formalism.L2.Col

def IsFormOf {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (hX : X.Ok)
    (P : LevFam X.E X.K R.r Pr.vGs) (x : MtildeV W Ch sel mu P) {V : Type} (y : V) : Prop :=
  ∃ (F : (mtildeKGSD W Ch sel mu).EqFun) (h : F.1 ∈ (mtildeGSD W Ch sel mu P).EqFun),
    HEq ((mtildeKGSD W Ch sel mu).res (mtildeKOk W Ch sel mu hX) F) y ∧ x = ⟨F.1, h⟩

end Forms

section Crd

attribute [local instance] GlobalTheory.Mem.Col2.starE

def IsCrd {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι) {V M : Type} [AddCommGroup M] [Module ℂ M]
    (e : Df.MtCx I a ≃ₗ[ℂ] M) (y : V) (v : M) : Prop :=
  ∃ x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I),
    IsFormOf (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x y ∧ v = e (Df.toCx I hX a x)

end Crd

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

abbrev famAll {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :=
  (R3.famR (w.st Z) w.I t.hX Set.univ t.r.z.Xg t.r.z.tr).A


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure RXs {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) : Type 1 where
  all : AllT (w.st Z).toD7 (famAll t) (R3.lev0 w.I) (R3.chr0 w.I) (R3.lev1 w.I) (R3.chr1 w.I) p0 (tAll w.I)
    (t.r.z.R.eG.trans t.r.z.cG)
  jA_use : ∀ s, SameOn (all.jA (t.r.Y.tup s)) (t.r.Y.jA s)
  movedReadingSameMaps_baseReading_agrees : ∀ s, SameOn (all.jA0 (t.r.Y.tup s)) (t.r.Y.jA0 s)
  eMt_use : ∀ i s, SameOn (all.eMt i (t.r.Y.tup s)) (t.r.Y.eMt i s)
  e : ∀ a : w.C.Tup, Df.MtCx w.I a ≃ₗ[ℂ] Z.W.Amb a
  eMt0 : ∀ u F, Df.SameForm w.I w.l u w.I.mu0 F ((Z.W.eMt0 u).symm (e w.C.mu0 F))
  eMtTw : ∀ u (a : w.C.Tup) F, Df.SameForm w.I w.l u a F ((Z.W.eMtTw u a).symm (e a F))
  crd : ∀ (a : w.C.Tup) y, IsCrd w.I t.hX a (e a)
    (R3.rowForm (D := (w.st Z).toD7) (famAll t) (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I a) y) (all.jA a y)
  io : ∀ μ j, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → Z.W.io μ j = 0 ∧ p0.s.io μ j = 0
  sha : GlobalTheory.MemN.ShaOK B.toPre Z.W.shaLen
  laws : Formalism.L2.Pj.LawsCore t.r.z.core.toCore
  canon : t.r.z.core.Q.Canon
  rank : ∀ j, 1 ≤ (t.r.z.core.Q.Dw j).p + (t.r.z.core.Q.Dw j).q
  pb : t.r.z.core.pb = f.P.pb
  std : t.r.z.Std

def RX : RPosition := fun _ _ _ _ _ _ _ _ t => RXs t

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 1000000 in
def ratL {D : D7} (L : LocAll (lay0 D)) (S : RatDat D.ntw) : RatDat (withLoc L).ntw := { S with }


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NAt (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) :
    Type 1 where
  nt : NTrue hL D cf nch tp
  all : NAllC D nch
  chr_eq : (⟨all.cf, all.tp⟩ : Σ c : CharFrame D, TupTied D c nch) = ⟨cf, tp⟩
  host : HostTied D
  frameN : ∀ x, all.gal.fr.jE x = host.fr.j x
  chrN : NCharTied D cf nch tp
  chrGal : NGalChrTied D cf nch tp
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  pq : ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : NX.AdmTw D i k Q ψ),
    (all.exp.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf D Pq Q ∧ (all.exp.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf D Pq (D.ntw.pD i)
  jE_eq : HEq nt.jE all.gal.fr.jE
  mt_eq : HEq (mtL nt.L nt.M) all.gal.mt
  Pq_eq : HEq nt.Pq Pq
  low : 2 ∈ nt.low ∧ AbsolutelyIrreducibleSpan.q0 D ∈ nt.low ∧ (NumberField.discr D.host.E).natAbs.primeFactors ⊆ nt.low ∧
    (Ideal.absNorm D.host.ccK).primeFactors ⊆ nt.low
  split : GlobalTheory.SplitCoef.OSplit D
  ratIn : RatIn nt.D nt.S
  ratIn_hL : ratIn.hL = nt.hL
  ratIn_eig : ratIn.eig = nt.eig
  ratIn_θ : ratIn.θ = nt.θ
  depth : RowDepth nt.D nt.rep

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 1000000 in
structure NRow {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) : Type 1 where
  kKs : Ks →+* ↥D.LL0
  hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x
  nexp : NExpRealS R cG (ratDatR R cG kKs hk)
  hecke : NExpRealH R cG (ratDatR R cG kKs hk) nexp
  grp : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG)
  rowLoc : principalLevelFrame.RowLocPin a.all.gal.lp R.θ Y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
    (fun b => levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (fun _ => R.e0) Y.eFT
  S_eq : HEq (ratL a.nt.L a.nt.S) (ratDatR R cG kKs hk)
  hL_eq : HEq a.nt.hL hecke.hL
  rep_eq : HEq a.nt.rep fun σ : D.what₂.FT => principalLevelFrame.rowRepR R.θ (Y.eFT σ)

end Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure NCore (hL : GlobalTheory.Published.LocalLanglandsGL) {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)}
    (t : RowsT K w Z Wt p0) {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) : Type 1 where
  a : NAt hL (w.D Z) (TC.cf w.I w.l Z) nch n.tp
  row : NRow (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y
  sel : Set.range a.Pq = Set.range w.I.sel

abbrev NExt (hL : GlobalTheory.Published.LocalLanglandsGL) : Type 2 :=
  ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl)
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (_ : ThData (w.D Z)),
    NCore hL t n → Type 1

def NX (hL : GlobalTheory.Published.LocalLanglandsGL) (E : NExt hL) : NCondition := fun K B f T w Z Wt p0 t nch n xd =>
  Σ c : NCore hL t n, E K B f T w Z Wt p0 t nch n xd c

end GlobalTheory.Mem.Top.Bl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.See
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.MainNotions Formalism.L2.Forms NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SAt {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H)
    (F0 : ∀ u, Forms0 D u) : Type 1 where
  P : SPack D F0
  S : SRest P
  t : GA D (D.sp.Y 0)
  c : ℝ
  c_pos : 0 < c
  see : SeeAt R F P.X P.inst t
  ev : EvalTieT (MP R) R.ν0 R.fd0 (EP R F) P.X P.G (iotaX P.X P.inst).toMulEquiv t c
  rowJ : RowJ R eE P.X P.inst P.G t S.j

def SX : SPosition := fun _ _ _ _ w Z _ _ r col =>
  SAt (D := (w.st Z).toD7) r.r.z.R.toRealDat r.r.z.F.lv2 r.r.Y.eE fun u => (col.C.forms u).to0

end GlobalTheory.Mem.Top.Bl

end
end

