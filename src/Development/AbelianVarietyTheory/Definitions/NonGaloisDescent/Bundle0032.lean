module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scale

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks)

def IsScaleAt {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W) (c : ℂ) : Prop :=
  ∀ F : VV D.what₂.LL (FWT.lamV D j),
    harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

variable {Rl}

theorem IsScaleAt.ioP_eq {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W} {c : ℂ} (h : IsScaleAt Rl B u c0 c)
    {H : Submodule ℂ (PolF D (Wc D j).rank (Vc D j).rank)}
    (hinj : ∀ P ∈ H, harmFn (Wc D j).rank B.w B.F.BS P = 0 → P = 0)
    {F : VV D.what₂.LL (FWT.lamV D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ H)
    (hio : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) ∈ H)
    (hPF : harmFn (Wc D j).rank B.w B.F.BS P =
      coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) = c • P :=
  sub_eq_zero.1 (hinj _ (H.sub_mem hio (H.smul_mem c hP)) (by rw [map_sub, map_smul, h F, hPF, sub_self]))

theorem RealPin.phase_mul_thetaKO {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) (i : D.ntw.Tw)
    {j : Fin D.R.m} (b : Bool) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} {w : (Rl.cV j).W}
    {P : PolF D (Wc D j).rank (Vc D j).rank} {c : ℂ} (hP : Rl.ioP j (PiTensorProduct.tprod ℂ u) w = c • P) (ph : ℂ)
    (om : PairRep (Vc D j) (Wc D j)) (s : GA D (Vc D j)) (f : WO (Vc D j) (Wc D j) → ℂ) :
    (fun g => ph * thetaKO om s g (harmVec Rl.toRealDat j u w f)) = (ph * c) • series (ρ.B i j b).F om f s P := by
  have e : harmVec Rl.toRealDat j u w f = (ρ.B i j b).F.fock f (c • P) := by
    rw [← hP, GlobalTheory.ExportSeries.Frame.fock, h.psi, h.inf, h.cartT, h.onbT, funext (h.onbS i j b)]
    rfl
  rw [e, mul_smul, ← map_smul]
  rfl

end Scale

section Phase

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((j : ℕ) + 1) σ = Wc D j)


variable {T j hV} in
theorem isRat_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : IsRat T j hV C κ fun g => a * φ g := by
  obtain ⟨φ', h1, rfl⟩ := h
  obtain ⟨x, rfl⟩ := ha
  refine ⟨C.σ₂ x • φ', GlobalTheory.CoverRead.Test.smul_mem_ratForms C _ _ x h1, ?_⟩
  have key : ∀ {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ), castDict e (z • ψ) = fun g => z * castDict e ψ g := by
    rintro V _ rfl z ψ
    rfl
  exact key hV _ _


variable {T R j hV} in
theorem seriesRatOn_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : SeriesRatOn T R j hV C κ u c0 ph)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : SeriesRatOn T R j hV C κ u c0 (a * ph) := by
  intro s hs f hf w hw
  obtain ⟨h1, h2⟩ := h s hs f hf w hw
  refine ⟨?_, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩
  · simpa only [mul_assoc] using isRat_mul h1 ha
  · simpa only [mul_assoc, mul_left_comm a] using isRat_mul ((h2 δ δc hδ).1 dd hdd) ha
  · simpa only [mul_assoc] using isRat_mul ((h2 δ δc hδ).2 om hom) ha

def IsRatPhase (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (u : ∀ τ, lowT (R.MW j (sg0 D A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (ph : ℂ) : Prop :=
  ∀ C : Cover T ((j : ℕ) + 1) σ, GoodCover T R j C κ.n → (embLL0 D).fieldRange ≤ C.σ₂.fieldRange →
    SeriesRatOn T R j hV C κ u c0 ph

variable {T R j hV}

theorem IsRatPhase.mul {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : IsRatPhase T R j hV κ u c0 ph)
    {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) : IsRatPhase T R j hV κ u c0 (a * ph) :=
  fun C hC hL => seriesRatOn_mul (h C hC hL) (hL ha)

end Phase

section Scalar

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m}
  (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (B : Base (Vc D j) (Wc D j))

def IsRatScalar (ν : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScaleAt Rl B u (c0L j) c ∧
        IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph

variable {T Rl κ v₀ hV B}

theorem IsRatScalar.intro {gramR c0R c0L} (h : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) {c ph : ℂ} (hc : c ≠ 0) (hph : ‖ph‖ = 1)
    (hs : IsScaleAt Rl B u (c0L j) c) (hr : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph) :
    IsRatScalar T Rl κ v₀ hV B (ph * c) :=
  ⟨gramR, c0R, c0L, h, u, hu, c, ph, hc, hph, rfl, hs, hr⟩

theorem IsRatScalar.isScale {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) :
    ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScale Rl v₀ B c := by
  obtain ⟨g, cR, cL, h0, u, hu, c, ph, h1, h2, h3, h4, -⟩ := h
  exact ⟨c, ph, h1, h2, h3, g, cR, cL, h0, u, hu, h4⟩

theorem IsRatScalar.ne_zero {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) : ν ≠ 0 := by
  obtain ⟨c, ph, h1, h2, rfl, -⟩ := h.isScale
  exact mul_ne_zero (fun e => by simp [e] at h2) h1

theorem IsRatScalar.mul {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) (h0 : ‖a‖ = 1) :
    IsRatScalar T Rl κ v₀ hV B (a * ν) := by
  obtain ⟨g, cR, cL, h1, u, hu, c, ph, h2, h3, rfl, h4, h5⟩ := h
  exact ⟨g, cR, cL, h1, u, hu, c, a * ph, h2, by rw [norm_mul, h0, h3, one_mul], (mul_assoc _ _ _).symm, h4, h5.mul ha⟩

end Scalar

end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
section
noncomputable section

namespace GlobalTheory.CoefDuty

open Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting

structure OPin {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (a : NAt hL D cf nch tp) : Prop where
  large : Large D
  inner : ∀ i : D.nd.Loc, ClassSum (a.all.gal.mt.loc i)
  lab : GlobalTheory.SerSys.LabTie a.nt.D fun k => @GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩
  gen : ∀ k, a.nt.A.grp.ζ k = @GlobalTheory.GLq.LabelDatum.gen _ ⟨a.nt.D.host.g_prime k⟩
    (@GlobalTheory.Mem.TypePl.labDat (a.nt.D.host.g k) ⟨a.nt.D.host.g_prime k⟩)

def OExt (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ _ _ _ _ _ _ _ _ _ _ _ c => ULift.{1} (PLift (OPin c.a))

end GlobalTheory.CoefDuty

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

def eKs : S.Ks ≃+* T0.Q.c.F := (YS.fi (NX.idxOf D 1)).eK

theorem eKs_LL (a : S.Ks) : algebraMap T0.Q.c.F D.what₂.LL (eKs YS a) = algebraMap S.Ks D.what₂.LL a := (YS.fi _).eK_LL a

def sideK (i : D.ntw.Tw) (b : Bool) : T0.Q.c.F →+* FractionRing (D.ntw.O i) :=
  (NX.ιK S i b).comp (eKs YS).symm.toRingHom

theorem sideK_eKs (i : D.ntw.Tw) (b : Bool) (a : S.Ks) : sideK YS i b (eKs YS a) = NX.ιK S i b a :=
  congrArg (NX.ιK S i b) ((eKs YS).symm_apply_apply a)

def cuspOf (j : Fin D.R.m) : NX.FmK S ((j : ℕ) + 1) ≃+ Cu T0 κ j :=
  AddEquiv.trans (N := (Rl.FW j).WK)
    { toFun := fun x => ⟨(YS.fi j).e (Subtype.val x), ((YS.fi j).wk _).1 (Subtype.property x)⟩
      invFun := fun y => ⟨(YS.fi j).e.symm y.1, ((YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext ((YS.fi j).e.symm_apply_apply _)
      right_inv := fun y => Subtype.ext ((YS.fi j).e.apply_symm_apply _)
      map_add' := fun x y => Subtype.ext ((YS.fi j).e.map_add _ _) }
    (fw.e j).symm.toAddEquiv

theorem e_cuspOf (j : Fin D.R.m) (x : NX.FmK S ((j : ℕ) + 1)) :
    (fw.e j (cuspOf YS fw j x) : Fin (Rl.nW j) → D.what₂.LL) = (YS.fi j).e (Subtype.val x) :=
  congrArg Subtype.val ((fw.e j).apply_symm_apply _)

theorem cuspOf_smul (j : Fin D.R.m) (a : S.Ks) (x : NX.FmK S ((j : ℕ) + 1)) :
    cuspOf YS fw j (a • x) = eKs YS a • cuspOf YS fw j x := by
  refine (fw.e j).injective (Subtype.ext ?_)
  rw [e_cuspOf, (fw.e j).map_smul, Submodule.coe_smul, e_cuspOf, ← algebraMap_smul D.what₂.LL (eKs YS a), eKs_LL,
    ← (YS.fi j).e.map_smul, algebraMap_smul]
  rfl

theorem cuspOf_mem_sec (j : Fin D.R.m) (x : NX.FmK S ((j : ℕ) + 1)) :
    (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n :=
  cusp_le_sec _ _ _ _ _ (cuspOf YS fw j x).2

theorem evW_eq_phiC (j : Fin D.R.m) (hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j)
    (hev : fw.Evaluates) (x : NX.FmK S ((j : ℕ) + 1)) :
    GlobalTheory.SeriesTie.evW YS v₀ j (Subtype.val x) = phiC T0 hV (wtA (κ j)) (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := by
  have h := hev j (sg0 D A3.A) (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1) hV (cuspOf YS fw j x)
  refine Eq.trans ?_ h
  change _ = (Rl.HW j _).e ((Rl.FW j).j _ (fw.e j (cuspOf YS fw j x) : Fin (Rl.nW j) → D.what₂.LL)) (v₀ j _)
  rw [e_cuspOf]
  rfl

theorem realRd_eq_phiC {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j) (hev : fw.Evaluates) (a : NX.KB S i b)
    (x : NX.FmK S ((j : ℕ) + 1)) :
    GlobalTheory.SeriesTie.realRd YS v₀ hρ i j b ν
                 ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _)) =
      (ν⁻¹ * ρ.e i b a) • phiC T0 hV (wtA (κ j)) (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := by
  rw [GlobalTheory.SeriesTie.realRd_tmul, evW_eq_phiC YS fw j hV hev]

def charAt (P : PlE D.host) : ℕ := ringChar (𝓞 D.host.E ⧸ P.asIdeal)

theorem charAt_mem (P : PlE D.host) : (charAt P : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem charAt_prime (P : PlE D.host) : (charAt P).Prime := by
  have := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  exact (CharP.char_is_prime_or_zero (𝓞 D.host.E ⧸ P.asIdeal) _).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 D.host.E ⧸ P.asIdeal) _)

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)

def embC : T0.Q.c.F →+* ℂ_[D.ntw.l i] := iC.comp (sideK YS i b)

def placeC : HeightOneSpectrum (𝓞 T0.Q.c.F) := placeAt (embC YS iC b)

abbrev FrC (j : ℕ) : Type := FrPt (T0.Q.Xo j) T0.Q.c (PAt (embC YS iC b))

abbrev Pts (j : ℕ) : Type := PtC (T0.Q.Xo j) T0.Q.c (embC YS iC b)

def kurAt : Subfield (FractionRing (D.ntw.O i)) := (kurC (embC YS iC b)).comap iC


variable {iC b} in
def valAt (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b →+ ℂ_[D.ntw.l i] :=
  TensorProduct.liftAddHom (R := S.Ks) (M := NX.KB S i b) (N := NX.FmK S ((j : ℕ) + 1))
    { toFun := fun a =>
        { toFun := fun x => iC a * valC z (cuspOf YS fw j x : T0.R ((j : ℕ) + 1))
          map_zero' := by rw [map_zero]; exact (congrArg _ (valC_zero z)).trans (mul_zero _)
          map_add' := fun x y => by rw [map_add (f := _), ← mul_add]; exact congrArg _ (valC_add z _ _) }
      map_zero' := by ext x; exact (congrArg (· * _) (map_zero iC)).trans (zero_mul _)
      map_add' := fun a a' => by ext x; exact (congrArg (· * _) (map_add iC a a')).trans (add_mul _ _ _) }
    fun c a x => by
      change iC ((show FractionRing (D.ntw.O i) from NX.ιK S i b c) * (show FractionRing (D.ntw.O i) from a)) * _ = iC a * valC z (cuspOf YS fw j (c • x) : T0.R _)
      rw [cuspOf_smul, Submodule.coe_smul, valC_smul, map_mul, ← sideK_eKs YS, mul_comm (iC (sideK YS i b _)), mul_assoc]
      rfl

variable {iC b}

theorem valAt_tmul (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)) :
    valAt YS fw j z (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _) = iC a * valC z (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := rfl

theorem valAt_smul (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) (a : FractionRing (D.ntw.O i))
    (x : NX.Fm S i ((j : ℕ) + 1) b) : valAt YS fw j z (a • x) = iC a * valAt YS fw j z x := by
  have key : ∀ (a : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)),
      valAt YS fw j z (a • x) = iC a * valAt YS fw j z x := fun a x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]; exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
    | add x y hx hy =>
      rw [smul_add]
      exact (map_add _ _ _).trans (by rw [hx, hy, ← mul_add]; exact congrArg _ (map_add _ _ _).symm)
    | tmul a' f =>
      rw [TensorProduct.smul_tmul', valAt_tmul, valAt_tmul, ← mul_assoc]
      exact congrArg (· * _) (map_mul iC a a')
  exact key a x

def wtChar (κj : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {j : ℕ} {φ : T0.Q.c.F →+* ℂ_[D.ntw.l i]} (t : Ix (T0.Q.Dw j) → (PAt φ)ˣ) :
    ℂ_[D.ntw.l i] := toCp φ (wchar (ex (T0.Q.Dw j) κj n) t)

theorem valAt_frBor (j : Fin D.R.m) {z z' : FrC YS iC b ((j : ℕ) + 1)} {t : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ}
    (h : FrBor t z z') (x : NX.Fm S i ((j : ℕ) + 1) b) :
    valAt YS fw j z' x = wtChar (wtA (κ j)) (κ j).n t * valAt YS fw j z x := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c).1
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z' x = wtChar (wtA (κ j)) (κ j).n t * valAt YS fw j z x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
    | add x y hx hy => exact (map_add _ _ _).trans (by rw [hx, hy, ← mul_add]; exact congrArg _ (map_add _ _ _).symm)
    | tmul a f =>
      rw [valAt_tmul, valAt_tmul, valC, hL.wt _ _ _ (cuspOf_mem_sec YS fw j f) _ t z z' (hL.test _ _) (hL.test _ _) h, map_mul,
        mul_left_comm]
      rfl
  exact key x


variable (S) in
def ratForms (j : ℕ) (b : Bool) (L : Subfield (FractionRing (D.ntw.O i))) : AddSubgroup (NX.Fm S i j b) :=
  AddSubgroup.closure {x | ∃ a ∈ L, ∃ f : NX.FmK S j, x = (show NX.KB S i b from a) ⊗ₜ[S.Ks] f}

theorem tmul_mem_ratForms {j : ℕ} {L : Subfield (FractionRing (D.ntw.O i))} {a : NX.KB S i b} (ha : a ∈ L) (f : NX.FmK S j) :
    (a ⊗ₜ[S.Ks] f : NX.KB S i b ⊗[S.Ks] _) ∈ ratForms S j b L := AddSubgroup.subset_closure ⟨a, ha, f, rfl⟩

theorem smul_mem_ratForms {j : ℕ} {L : Subfield (FractionRing (D.ntw.O i))} {a : FractionRing (D.ntw.O i)} (ha : a ∈ L)
    {x : NX.Fm S i j b} (hx : x ∈ ratForms S j b L) : a • x ∈ ratForms S j b L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', f, rfl⟩ := hx
    exact tmul_mem_ratForms (L.mul_mem ha ha') f
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem span_ratForms (j : ℕ) (L : Subfield (FractionRing (D.ntw.O i))) :
    Submodule.span (FractionRing (D.ntw.O i)) (ratForms S j b L : Set (NX.Fm S i j b)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S j,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (ratForms S j b L : Set (NX.Fm S i j b)) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a f =>
      have h := Submodule.smul_mem _ (show FractionRing (D.ntw.O i) from a)
        (Submodule.subset_span (R := FractionRing (D.ntw.O i)) (tmul_mem_ratForms (b := b) L.one_mem f))
      have e : (a • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] f) : NX.KB S i b ⊗[S.Ks] NX.FmK S j) = a ⊗ₜ[S.Ks] f := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      exact e ▸ h
  exact key x

variable (iC b) (j : Fin D.R.m)

def urBall (B : ℝ) : Set (NX.Fm S i ((j : ℕ) + 1) b) :=
  {x | x ∈ ratForms S _ b (kurAt YS iC b) ∧ ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valAt YS fw j z.1 x‖ ≤ B}

def Detects : Prop :=
  ∀ x : NX.Fm S i ((j : ℕ) + 1) b, (∀ z : Pts YS iC b ((j : ℕ) + 1), valAt YS fw j z.1 x = 0) → x = 0

def SupDescent : Prop := NX.Bsup S i ((j : ℕ) + 1) b = Submodule.span (D.ntw.O i) (urBall YS fw iC b j 1)

def HeckeIs (k : ℕ) (P : PlE D.host) (u : ℂ_[D.ntw.l i]) : Prop :=
  ∀ (z : Pts YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z.1 → FrC YS iC b ((j : ℕ) + 1)),
    (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (quot C)) → ∀ f : D.nexp.Fm i ((j : ℕ) + 1) b,
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.hkF i _ b k P f)) =
        u * ∑ᶠ C, valAt YS fw j (quot C) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)

def HeckeGeo : Prop :=
  ∀ k P, HkIdx i k P → ∃ s : T0.Q.c.F, ‖embC YS iC b s‖ = 1 ∧ HeckeIs YS fw iC b j k P (embC YS iC b s)

def HeckeStable : Prop := ∀ k P, HkIdx i k P → ∀ (z : Pts YS iC b ((j : ℕ) + 1)) (C : HkKer P.asIdeal (charAt P) k z.1),
  ∃ z' : Pts YS iC b ((j : ℕ) + 1), IsHkQuot P.asIdeal (charAt P) k z.1 C z'.1


omit j in
def KerCard (j k : ℕ) (P : PlE D.host) (n : ℕ) : Prop :=
  ∀ (b : Bool) (z : Pts YS iC b j), Nonempty (Fin n ≃ HkKer P.asIdeal (charAt P) k z.1)

def HeckeCount : Prop := ∀ k P, HkIdx i k P → ∃ n, KerCard YS iC ((j : ℕ) + 1) k P n

end Side

end GlobalTheory.GeoTie

end
end

