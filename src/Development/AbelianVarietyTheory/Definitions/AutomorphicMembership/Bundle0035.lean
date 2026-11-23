module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}


set_option maxHeartbeats 2000000 in
structure ExtN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') : Prop where
  H : HEq z'.core.Q.H z.core.Q.H
  l : HEq z'.core.Q.l z.core.Q.l
  c : HEq z'.core.Q.c z.core.Q.c
  Dw : HEq z'.core.Q.Dw z.core.Q.Dw
  Xo : HEq z'.core.Q.Xo z.core.Q.Xo
  U : HEq z'.core.U z.core.U
  V : HEq z'.core.V z.core.V
  dict : HEq z'.core.dict z.core.dict
  mu : HEq z'.core.mu z.core.mu
  Kf : HEq z'.core.Kf z.core.Kf
  cE : HEq z'.core.cE z.core.cE
  chiW : HEq z'.core.chiW z.core.chiW
  x₀ : HEq z'.core.x₀ z.core.x₀
  iota : HEq z'.core.iota z.core.iota
  ψ : HEq z'.R.ψ z.R.ψ
  θ : HEq z'.R.θ z.R.θ
  βW : HEq z'.R.βW z.R.βW
  βY : HEq z'.R.βY z.R.βY
  nW : HEq z'.R.nW z.R.nW
  βV : HEq z'.R.βV z.R.βV
  ΛV : HEq z'.R.ΛV z.R.ΛV
  ΛW : HEq z'.R.ΛW z.R.ΛW
  Pg : HEq z'.R.Pg z.R.Pg
  eG : HEq z'.R.eG z.R.eG
  Sb : HEq z'.R.Sb z.R.Sb
  BV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').W (z.R.cV i).W ∧ HEq (z'.R.cV i').ρ (z.R.cV i).ρ ∧ HEq (z'.R.vacP i') (z.R.vacP i) ∧
    HEq (z'.R.ioP i') (z.R.ioP i) ∧ HEq (z'.R.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (z'.R.BV i') (z.R.BV i)
  MW : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (z'.R.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
    ∀ φ φ', HEq φ' φ → HEq ((z'.R.FW i').j (w'.st Z').toD7.what₂.embLL (z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1)
      ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)
  forms : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
    ∀ (k : Fin (z.R.nW i)) (k' : Fin (z'.R.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)
  cV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').nW (z.R.cV i).nW ∧ HEq (z'.R.cV i').iW (z.R.cV i).iW
  pb : HEq z'.core.pb z.core.pb
  ΛY : HEq z'.R.ΛY z.R.ΛY
  κ : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.geo.κ i').aP (z.geo.κ i).aP ∧ HEq (z'.geo.κ i').aM (z.geo.κ i).aM ∧ (z'.geo.κ i').n = (z.geo.κ i).n
  ref : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νW i') (z.R.νW i) ∧ HEq (z'.R.fdW i') (z.R.fdW i)
  jL : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ'))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (by exact (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ))


set_option maxHeartbeats 2000000 in
theorem ExtN.ext {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : ExtN z z')
    (h : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)) : Ext z z' :=
  { e with W1 := h }


set_option maxHeartbeats 2000000 in
theorem Ext.extN {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'} (e : Ext z z') : ExtN z z' :=
  { e with }

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Enl0 (B B' : Base) : Prop :=
  B'.toPre = B.toPre ∧ B'.embLL '' (B'.Ks : Set B'.LL) = B.embLL '' (B.Ks : Set B.LL) ∧
    B.embLL '' (B.LL0 : Set B.LL) ⊆ B'.embLL '' (B'.LL0 : Set B'.LL) ∧ Set.range B.embLL ⊆ Set.range B'.embLL

theorem isBaseEnlargementFixedCoefField_of_coeffEnlargement {B B' : Base} (h : Enl B B') : Enl0 B B' := ⟨h.1, h.2.1, h.2.2.1.ge, h.2.2.2⟩

def DatExt0 : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

theorem datExt_of_datExt0 (h : DatExt0) : DatExt := by
  unfold DatExt0 at h
  unfold DatExt
  exact StepW.trans h (StepW.of_all fun _ _ _ _ _ _ _ H B f T w e => H B f T w (isBaseEnlargementFixedCoefField_of_coeffEnlargement e))

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesAdelicDataResizedEq
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.R3.Rw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}




variable {hX : B.fields.Ok} {Wt W₁ : Set B.places.Pl}


theorem ExtModel.sign_at_base_place_eq_embedding (z : Dat (w.st Z) w.I hX T Wt) :
    sg0 (w.st Z).toD7 (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A = (w.st Z).toD7.what₂.embLL :=
  if_pos z.R.hv0




end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
section
noncomputable section

namespace GlobalTheory.Mem.SRe.CarModel

section Pts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_swap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) {n : ℕ}
    [NeZero n] {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅) {y k k' g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    {q : DecoF E n ST SG Q'} (h : IsPtOf hc (y * k) p) (h' : IsPtOf hc (y * k') p) (hq : IsPtOf hc (g * k) q) :
    IsPtOf hc (g * k') q := by
  have e : ∀ a : GL (Fin n) (AfE F E), a * k * (k⁻¹ * k') = a * k' := fun a => by group
  obtain ⟨hz, hr⟩ := ((isPtOf_mul_J0 F E hc n ST SG Q (y * k) (k⁻¹ * k') p p 1).1 h (by rw [e]; exact h')).2 (one_smul _ _).symm
  have := (isPtOf_mul_J0 F E hc n ST SG Q' (g * k) (k⁻¹ * k') q q 1).2.1 hQ hq hz hr
  rw [e] at this
  exact (one_smul _ q : ((1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q') • q = q) ▸ this


set_option maxHeartbeats 2000000 in
theorem reads_le {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (i : ℕ) {Lb Lb'} {U U' : Subgroup (GA B (B.R.N i))}
    {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' st st' k k'} (hy : y' = y)
    (h : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (h' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k')
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (x : U) : ∃ hx : x.1 ∈ U', chi' ⟨x.1, hx⟩ = chi x := by
  subst hy
  rename' y' => y
  obtain ⟨c, -⟩ := h.onto ()
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  obtain ⟨p0, hp0, -⟩ := h.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := (h.pt c).uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have h1 : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [h1]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) (hU x.2)) hk)
  obtain ⟨q₁, hq₁, -⟩ := exists_near (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm 0 hg
  have hq : IsPtOf B.sp.cm (y c * x.1 * k ()) q₁ :=
    (GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw _ _ B.sp.cm _ _ _ _ _ q₁ hQ).2 ⟨hg, hq₁.symm⟩
  have hq' : IsPtOf B.sp.cm (y c * x.1 * k' ()) q₁ := pt_swap B.sp.cm hQ (h.pt c) (h'.pt c) hq
  have hm := (h.lev c x.1 q₁ hq).1 x.2
  have hx : x.1 ∈ U' := (h'.lev c x.1 q₁ hq').2 hm
  obtain ⟨κ, hgam, hκq, -⟩ := hm
  refine ⟨hx, Units.ext ?_⟩
  exact (h'.chr c ⟨x.1, hx⟩ κ hgam (by rw [hκq]; exact hq')).trans (h.chr c x κ hgam (by rw [hκq]; exact hq)).symm

theorem heq_chi {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ}
    (h : ∀ x : U, ∃ hx : x.1 ∈ U', chi' ⟨x.1, hx⟩ = chi x) (h' : ∀ x : U', ∃ hx : x.1 ∈ U, chi ⟨x.1, hx⟩ = chi' x) :
    U' = U ∧ HEq chi' chi := by
  have e : U' = U := le_antisymm (fun x hx => (h' ⟨x, hx⟩).1) (fun x hx => (h ⟨x, hx⟩).1)
  subst e
  exact ⟨rfl, heq_of_eq (MonoidHom.ext fun x => (h x).2)⟩

end Pts

section Std
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.ColAd _root_.Formalism.L2.Col
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}


set_option maxHeartbeats 4000000 in
theorem U_le (Z : w.Lt) (u : B.Word) (F : Forms0 (w.D Z) u) :
    (show Subgroup (GA B (B.R.N 0)) from F.cls0.lev.U) ≤ UAd B.sp.cm (B.R.N 0) := by
  have hg1 : gramN (w.D Z) 0 (Nat.zero_le _) = 1 := ((spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : UPts (sigD (w.D Z)) (gramN (w.D Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (w.D Z).host.F) (w.D Z).host.F) =
      UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((F.cls0.lev.U_eq x).1 hx).1

abbrev Car (B : Base) : Type :=
  Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E) × Σ U : Subgroup (GA B (B.R.N 0)), (U →* ℂˣ)


set_option maxHeartbeats 4000000 in
def car (Z : w.Lt) (u : B.Word)
    (S : StepLevel (w.D Z).host.F (w.D Z).host.E (sigD (w.D Z)) (gramN (w.D Z) 0 (Nat.zero_le _)) ((w.D Z).mem u).A.T (w.D Z).R.f
      (badG (w.D Z))) : Car B := (S.Lb, ⟨S.U, S.chi⟩)


set_option maxHeartbeats 4000000 in
theorem car_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    car Z' u (t'.C.forms u).to0.cls0.lev = car Z u (t.C.forms u).to0.cls0.lev := by
  obtain ⟨k, h⟩ := (t.std u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨k', h'⟩ := (t'.std u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hy := (funext ((t.std u).yE 0 (Nat.zero_le _) (Or.inl rfl))).trans (funext ((t'.std u).yE 0 (Nat.zero_le _) (Or.inl rfl))).symm
  have e := heq_chi (reads_le w.I u 0 hy.symm h h' (U_le Z u (t.C.forms u).to0)) (reads_le w.I u 0 hy h' h (U_le Z' u (t'.C.forms u).to0))
  exact Prod.ext (Submodule.ext fun x => (h'.lb () x).trans (h.lb () x).symm) (Sigma.ext e.1 e.2)

set_option maxHeartbeats 4000000 in
theorem y_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    (t'.C.forms u).to0.cls0.y = ((t.C.forms u).to0.cls0.y) :=
  funext fun c => Subtype.ext (((t'.std u).yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans ((t.std u).yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm)

set_option maxHeartbeats 4000000 in
theorem eY_eq {Z Z' : w.Lt} (t : ColT w Z) (t' : ColT w Z') (u : B.Word) :
    (t'.C.forms u).to0.val0.eY = ((t.C.forms u).to0.val0.eY) :=
  Equiv.ext fun c => Subtype.ext (((t'.std u).eY 0 (Nat.zero_le _) (Or.inl rfl) c).trans ((t.std u).eY 0 (Nat.zero_le _) (Or.inl rfl) c).symm)


set_option maxHeartbeats 4000000 in
theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have e : car (reL Z Zn) u (col'.C.forms u).to0.cls0.lev = car (reL Z Zn) u (F₁ u).cls0.lev :=
    (car_eq col col' u).trans ((congrArg (car Z u) (Eq.symm (h u).left)))
  have e2 := Sigma.ext_iff.1 (congrArg Prod.snd e)
  exact ⟨congrArg Prod.fst e, e2.1, e2.2, (y_eq col col' u).trans ((by with_unfolding_all exact ((h u).2.1.symm :))), (eY_eq col col' u).trans ((by with_unfolding_all exact ((h u).2.2.symm :)))⟩

end Std

section Mv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl Formalism.L2.SG.ColDict Formalism.L2.SG.HidaSetting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {F F' : ∀ u, Forms0 D u}


set_option maxHeartbeats 4000000 in
def trCar (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) : Transport X u (F' u) :=
  { t with
    hc_rep := fun c => by rw [(h u).2.2.2.1]; exact t.hc_rep c
    J_isom := fun c ξ η => by rw [(h u).2.2.2.2]; exact t.J_isom c ξ η }

set_option maxHeartbeats 4000000 in
theorem colDictL_car (h : SameCar F F') {X : HidaSetting D} {u} (t : Transport X u (F u)) (hK : X.LevelSubgroupCharacter) :
    colDictL X (trCar h t) hK = colDictL X t hK := by
  refine LinearMap.ext fun T => funext fun c => funext fun z => ?_
  exact congrArg (fun e => t.J (shP X u T.1 (t.hc c)) (e z)) (congrArg DFunLike.coe (h u).2.2.2.2)

theorem chi_of_heq {G : Type} [Group G] {U U' : Subgroup G} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} (e : U' = U) (h : HEq chi' chi)
    (x : G) (hx : x ∈ U') : chi' ⟨x, hx⟩ = chi ⟨x, e ▸ hx⟩ := by
  subst e
  rw [eq_of_heq h]

set_option maxHeartbeats 4000000 in
theorem lev_car (h : SameCar F F') {X : HidaSetting D} {u} {t : Transport X u (F u)} {hK : X.LevelSubgroupCharacter} (l : LevelMatch X t hK) :
    LevelMatch X (trCar h t) hK := by
  refine ⟨fun x => ?_, fun g y hr => ⟨?_, fun hk hy => ?_⟩⟩
  · rw [(h u).1]; exact l.1 x
  · rw [(h u).2.1]; exact (l.2 g y hr).1
  · rw [chi_of_heq (h u).2.1 (h u).2.2.1]; exact (l.2 g y hr).2 hk _


set_option maxHeartbeats 4000000 in
def packCar (h : SameCar F F') (P : SPack D F) : SPack D F' :=
  { P with
    tr := fun u => trCar h (P.tr u)
    into := fun u T => by rw [colDictL_car]; exact P.into u T
    bij := fun u => by unfold ColDictBij; rw [colDictL_car]; exact P.bij u
    lev := fun u => lev_car h (P.lev u)
    isom := fun u a b => by rw [colDictL_car]; exact P.isom u a b }


set_option maxHeartbeats 4000000 in
def restCar (h : SameCar F F') {P : SPack D F} (S : SRest P) : SRest (packCar h P) where
  hI := S.hI
  autTie := S.autTie
  colPin := fun u x => Subtype.ext ((LinearMap.congr_fun (colDictL_car h (P.tr u) P.Y.hK) _).trans (congrArg Subtype.val (S.colPin u x)))
  j := S.j
  rowPin := S.rowPin
  locTied := S.locTied


set_option maxHeartbeats 4000000 in
def satCar (h : SameCar F F') (p : RowPk D) (s : p.SAt F) : p.SAt F' :=
  { P := packCar h s.P, S := restCar h s.S, t := s.t, c := s.c, c_pos := s.c_pos, see := s.see, ev := s.ev, rowJ := s.rowJ }

end Mv

section Slot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV Formalism.MainNotions Formalism.L2.Forms NumberField
  IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar




variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}




end Slot

end GlobalTheory.Mem.SRe.CarModel

end
end

