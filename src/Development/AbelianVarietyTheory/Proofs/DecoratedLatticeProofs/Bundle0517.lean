module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdBNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStep
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberData


open Formalism.MainNotions.S in
theorem dataNW_of_val {C : Formalism.MainNotions.Inhab.FC} {cD ch : ℝ} (hC : Std C) {D : D7} (L : SizeData₂ D)
    (hV : Val C cD ch L) (hS : SizesAt L) (hR : ∀ u, GlobalTheory.Core.Rk.RankMu D u) : GlobalTheory.Core.Deg.DataNW D := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hk0 : 0 < D.R.k := by omega
  have hSc := Sc_eq' L
  have e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := fun u τ => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]
  have e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := fun τ => vOne_succ τ 0 (by omega)
  have hCc : L.Cc = 2 := hV.Cc_eq.trans hC.2.1
  have hdu : ∀ u, 0 < D.duS u := fun u => by
    have h := hR u
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
    have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := sub_pos.2 (one_lt_pow₀ hT (by omega))
    have h0 : (0 : ℝ) < D.duS u := by rw [h]; positivity
    exact_mod_cast h0
  refine ⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8,
    fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu,
    Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1,
    discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),
    fun u => ne_of_mod (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le (T_mod D u)⟩
  · intro u τ
    rw [e1, e2, ← hSc]
    by_cases ht : Formalism.MainNotions.S.IsTop D τ
    · obtain ⟨t, ht⟩ := ht
      have h1 := (L.top_u τ t hk0 ht).1
      have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
      have h3 := (L.aT_win t).1
      have h4 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS
      have h5 := L.Sc_pos
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      rw [h1]
      linarith
    · have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1
      push_cast at this
      exact this
  · intro u τ ht
    have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2
    push_cast at this
    rw [hCc] at this
    rw [e1, e2]
    linarith
  · intro u τ ht
    have hv := hV.hc.1 τ ⟨D.R.k - 2, by omega⟩
    have hu := (hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2
    have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
    have hv' := vOne_succ τ (D.R.k - 2) (by omega)
    rw [← e] at hv'
    rw [uOne_last u τ, hv', hv, hu]
    norm_num
  · intro τ ht
    obtain ⟨t, ht⟩ := ht
    have hm0 : 0 < D.R.m := by omega
    have eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]
    have et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 := by
      unfold bTop
      rw [uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]
      ring
    have h1 := L.top_b τ t hm0 ht
    obtain ⟨b1, hb, htop, -, -⟩ := hV.hc.2.2.1
    have hb0 := (hb τ ⟨0, hm0⟩).1
    have hbt := htop τ t ht
    have hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
      rw [hb0, hbt]
      push_cast
      ring
    have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
    have hb'0 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)
    have hx1 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1
    have hbT := L.bT_ge t
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    rw [eb, et]
    constructor <;> linarith

theorem val_congr {C C' : Formalism.MainNotions.Inhab.FC} {cD cD' ch ch' : ℝ} {D : D7} {L : SizeData₂ D} (h1 : C = C') (h2 : cD = cD')
    (h3 : ch = ch') (h : Val C cD ch L) : Val C' cD' ch' L := by
  subst h1 h2 h3
  exact h

end GlobalTheory.Fam.MemberData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DecoratedLatticeOfAdelicMatrixEqRowPoint
section
noncomputable section

namespace GlobalTheory.TopVal.DecoPt

section General

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hasRes_red {P : HeightOneSpectrum (𝓞 E)} {a : E} (ha : IntAt P a) :
    HasRes P (algebraMap E _ a) (redP P a) := by
  obtain ⟨r, s, hs, h⟩ := id ha
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (redP P a)
  refine ⟨t, ht, ?_⟩
  have h1 := reduction_spec P hs h
  rw [← ht, ← map_mul, eq_comm, Ideal.Quotient.eq] at h1
  have h2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 h1
  have h3 : P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
    le_antisymm (HeightOneSpectrum.valuation_le_one (K := E) P s)
      (not_lt.1 fun hl => hs ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).1 hl))
  have h4 : P.valuation E (algebraMap (𝓞 E) E s * (a - algebraMap (𝓞 E) E t)) < 1 := by
    rw [mul_sub, h, ← map_mul, ← map_sub]
    exact h2
  rw [map_mul, h3, one_mul] at h4
  rw [← map_sub, valued_algebraMap]
  exact h4

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)}

theorem adAt_pull {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (x : Sp E n) (i : Fin n) :
    adAt F P.1 (GlobalTheory.Mem.Col2.pullV g x i) = algebraMap E _ ((p.fr P).symm x i) := by
  have e : ratM P.1 (p.fr P) = locM P.1 g := Matrix.ext fun i j => (h.fr P i j).symm
  have h1 := ratM_mulVec (P := P.1) (p.fr P) ((p.fr P).symm x)
  rw [LinearEquiv.apply_symm_apply, e] at h1
  have h2 := congrFun (congrArg (fun v => locM P.1 g⁻¹ *ᵥ v) h1) i
  simp only [Matrix.mulVec_mulVec] at h2
  rw [← locM_mul, inv_mul_cancel, locM_one, Matrix.one_mulVec] at h2
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.Mem.Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE, locM, Matrix.map_apply]

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST (uSG SG Q) ∅ :=
  ⟨(forgetFr p, fun _ => 1), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_noFr {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) : IsPtOf hc g (noFr p) := by
  refine ⟨h.uni, h.lat, h.f, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  show HasRes _ _ ((forgetDeco p).be w x i)
  by_cases hw : w.1 ∈ SG
  · rw [forgetDeco_be_of_mem p w hw]
    exact h.be ⟨w.1, hw⟩ x hx i
  · have hs : (p.fr (rightOf w hw)).symm x ∈ stdAt E n w.1 := by
      refine (p.2 (rightOf w hw) _).1 ?_
      show p.fr (rightOf w hw) ((p.fr (rightOf w hw)).symm x) ∈ _
      rw [LinearEquiv.apply_symm_apply]
      exact le_locP _ _ hx
    have e : frBe w.1 (p.fr (rightOf w hw)) x = redV w.1 ((p.fr (rightOf w hw)).symm x) := if_pos hs
    rw [forgetDeco_be_of_not p w hw, e, adAt_pull h (rightOf w hw) x i]
    exact hasRes_red (mem_stdAt.1 hs i)

theorem decoOf_eq_forgetFr [NeZero n] {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    decoOf ST (uSG SG Q) g = forgetFr p :=
  Subtype.ext ((rlc_decoOf_val hc n ST (uSG SG Q) h.uni).trans (near_of_isPtOf (isPtOf_noFr h) 0).deco)

end General

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_eq_toRow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X), I.Ok → ∀ (a : I.ι) (y : GlobalTheory.Mem.Col2.TC.GA B (B.R.N B.R.m - 1)) (p : GlobalTheory.Mem.Col2.XPt (B.primes X) B.R I.sel (I.tup a)), GlobalTheory.Mem.Col2.TC.PtOf y p → GlobalTheory.TopVal.latOf I a y = GlobalTheory.Mem.Col2.toRow I.sel (I.tup a) p := by
  intro B X I _ a y p h
  letI := GlobalTheory.Mem.Col2.starE B
  exact decoOf_eq_forgetFr (F := B.fields.F) (E := B.fields.E) h

end GlobalTheory.TopVal.DecoPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal

namespace GlobalTheory.TopVal

def DatVal {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {G : Type} [Group G] [Fintype G]
    {Pl0 T : Type} {A : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [aK : Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) A Ks) (tup : T → I.ι) : Prop :=
  ∃ c : Val B →ₛₗ[B.embLL] R.cX.W,
    (∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
      GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = R.cX.ρ γ.1 (c v)) ∧
    ∀ (t : T) (φ : Frm I (tup t)) (x : A.fam.amb.FR t), IsRes φ x →
      ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') y, HasMat h y → IsUni B y →
        (R.HX t).e (R.jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h) = c (val φ (latOf I (tup t) y))

theorem matEq_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hm : HasMat h y) :
    GlobalTheory.Mem.R3.MatEq (R3.matIn D.sp.X' 1 ((finHom D.sp.X').rangeRestrict h)) y := by
  refine ⟨Formalism.L2.Forms.rankP D, fun i j i' j' hi hj => ?_⟩
  have e1 : finCongr (Formalism.L2.Forms.rankP D) i = i' := Fin.ext hi
  have e2 : finCongr (Formalism.L2.Forms.rankP D) j = j' := Fin.ext hj
  rw [← e1, ← e2, ← hm.2 i j]
  unfold R3.matIn
  rw [mul_one]
  rfl


set_option maxHeartbeats 1000000 in
theorem datVal_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := t.r.z.alg) t.r.z.R.toRealDat t.r.Y.tup := by
  obtain ⟨c, h1, h2, -, -⟩ := hs.1
  have h3 := t.r.z.pins.char.base.models.jX
  have h4 := t.r.z.lev.beta.2
  refine ⟨c, fun γ γE g hr hm v => h1 γ γE g hr hm v, fun s => ?_⟩
  have h5 : w.I.tup (t.r.Y.tup s) = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have key : ∀ (a : w.I.ι), w.I.tup a = s.1 → ∀ (φ : Frm w.I a) (x : (R3.famT t).A.fam.amb.FR s), IsRes φ x →
      ∀ (h : GA (w.D Z) (w.D Z).sp.X') y, HasMat h y → IsUni B y →
        t.r.z.R.B.jR s x ((finHom (w.D Z).sp.X').rangeRestrict h) = c (val φ (latOf w.I a y)) := by
    intro a ha
    obtain ⟨s, hs'⟩ := s
    change w.I.tup a = s at ha
    subst ha
    rintro φ x ⟨ok, hx⟩ h y hm hu
    have hx' : ((by with_unfolding_all exact ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a)).res ok φ :)) : (R3.famT t).A.fam.amb.FR ⟨w.I.tup a, hs'⟩) = x := by
      apply eq_of_heq
      exact (by with_unfolding_all exact (hx :))
    have hM := matEq_of_hasMat hm
    have e := h2 B.sp.cm ⟨w.I.tup a, hs'⟩ ⟨⟨ok⟩, φ⟩ ((finHom (w.D Z).sp.X').rangeRestrict h) ⟨y, hu⟩ (by rw [h4]; exact hM)
    have e2 := decoPt_mk B.sp.cm (B.R.N B.R.m - 1) ∅ (rowSG (B.primes w.px) w.I.sel (w.I.tup a)) ⟨y, hu⟩
    rw [← hx']
    refine Eq.trans ((by with_unfolding_all exact (e :))) (congrArg (fun d => c (val φ d)) e2)
  intro φ x hx h y hm hu
  exact (congrFun (h3 s x) _).trans (key _ h5 φ x hx h y hm hu)


set_option maxHeartbeats 1000000 in
theorem datVal_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := a.x.alg) a.x.R.toRealDat a.x.Y.tup := by
  have h := datVal_rows K B f T w Z Wt ex.p0 t hs
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (c :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))


end GlobalTheory.TopVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.BaseLevel

open NumberField IsDedekindDomain GlobalTheory.Mem.Col2 Formalism.L2.Forms GlobalTheory.SeeSaw GlobalTheory.SeeSaw.TopLevel

theorem levFn_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r t s : ℕ} (h : r ≤ n)
    (β) {SG Q : Finset (Pl E)} (P : LevelP SG r ℂ) (cg cg' : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ) (xq : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ)
    (e : ∀ c, c < s → ∀ PP ∈ SG, cg (c + 1) PP = cg' (c + 1) PP) (g) :
    levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg, xq⟩ g = levFn (F := F) β ⟨r, h, t, s, SG, Q, P, cg', xq⟩ g := by
  unfold levFn
  congr 2
  refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c hc => ?_
  exact congrArg (fun f : (kP PP)ˣ →* ℂˣ => f _) (e c (Finset.mem_range.1 hc) PP hPP)

theorem isRes_unique {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem isRes_chiC (h : I.Ok) (j : Fin B.R.m) (PP : Pl (I.rec7 l Z).host.E) (hw : PP ∈ (B.primes X).vGs) :
    IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (chiC I j PP)⁻¹ := by
  intro a k u hk hu
  have ht := (h.ch_tied.mu0 j).atg ⟨PP, hw⟩ k a u hk hu
  have e : ∀ (j : Fin B.R.m) (P : HeightOneSpectrum (𝓞 B.fields.E)) (hw : P ∈ (B.primes X).vGs),
      Formalism.L2.Col.chiP I.Ch P j = I.Ch.chi j ⟨P, hw⟩ := by
    intro j P hw
    unfold Formalism.L2.Col.chiP
    rw [dif_pos hw]
    simp [Formalism.L2.Col.chiAt, Formalism.L2.Col.extChi]
  refine Units.ext (Eq.trans ?_ ht.symm)
  have e2 := (chiC_apply I j PP u).trans (congrArg (fun f : _ →* B.LLˣ => B.embLL ((f u : B.LLˣ) : B.LL)) (e j PP hw))
  exact (Units.val_inv_eq_inv_val _).trans ((congrArg (·⁻¹) e2).trans
    ((map_inv₀ B.embLL _).symm.trans (congrArg B.embLL (Units.val_inv_eq_inv_val _).symm)))


set_option maxHeartbeats 2000000 in
theorem topLev_datY (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (cg : ℕ → ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl B.fields.E, (kP PP)ˣ →* ℂˣ)
    (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.fields.Kˣ) : B.fields.K))
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ (B.primes X).vGs, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' 1 (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr (B.primes X).vGs ∅ P' cg ξ Frm.B)) := by
  have hK := hF.what₂
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I ok pins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  obtain ⟨c', -⟩ := F.clsP.y_bij.2 (Quotient.mk'' 1)
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hR := rd_all I hK c'
  have hLb : F.clsP.lev.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  have key := @lev_iff B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ F.clsP.lev hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL hR
    P' (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hH hchi
    (fun i PP a => by
      have e : Formalism.L2.Col.chiP I.Ch PP.1 = Formalism.L2.Col.chiAt I.Ch PP := dif_pos PP.2
      show B.embLL ((Formalism.L2.Col.chiP I.Ch PP.1 i a : B.LLˣ) : B.LL) = _
      rw [e])
  have hc : ∀ c, c < B.R.m → ∀ PP ∈ (B.primes X).vGs, cg (c + 1) PP = chiC I (c + 1 - 1) PP := fun c hc PP hPP =>
    inv_injective (isRes_unique (D := I.rec7 l Z) (hcg ⟨c, hc⟩ PP hPP) (isRes_chiC I l Z ok ⟨c, hc⟩ PP hPP))
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => ?_⟩
  · obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
    exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩
  · refine Eq.trans ?_ ((key _ κ.1 hκ.2).2 κ.2)
    exact congrArg Units.val (levFn_congr (F := B.fields.F) hr 1 P' cg (fun i => chiC I (i - 1)) (fun PP => (ξ PP)⁻¹) hc _)


set_option maxHeartbeats 2000000 in
theorem topLev_levPOf (ok : I.Ok) (pins : TC.Pins B X) (v : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem v).C.cls i → Ch i}
    (F : FormsTiedSym (I.rec7 l Z) v Ch chOf) (hF : I.StdF l Z v F) (hr : (I.rec7 l Z).R.r ≤ (I.rec7 l Z).sp.X'.rank)
    (Pg Q : Finset (Pl (I.rec7 l Z).host.E)) (β : GL (Fin (I.rec7 l Z).sp.X'.rank) (EAf (I.rec7 l Z)))
    (hPg : Pg = (B.primes X).vGs) (hQ : Q = ∅) (hβ : β = 1) (eG : R3.Gc B X ≃* G0 Pg (I.rec7 l Z).R.r)
    (hG : ∀ (g : R3.Gc B X) (P : Pl (I.rec7 l Z).host.E) (h : P ∈ (B.primes X).vGs) (h' : P ∈ Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩)
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ (j : Fin B.R.m), ∀ PP ∈ Pg, IsRes (D := I.rec7 l Z) (I.C.mu0 j) PP (cg ((j : ℕ) + 1) PP)⁻¹) :
    GlobalTheory.Core.Rk.Top.TopLev F.clsP
      (levS (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B))
      (levChi (I.rec7 l Z).sp.X' β (datY (D := I.rec7 l Z) _ B.R.r B.R.t B.R.m hr Pg Q
        (levPOf (D := I.rec7 l Z) eG B.embLL (R3.lev1 I) (R3.chr1 I)) cg ξ Frm.B)) := by
  subst hPg hQ hβ
  have he : ∀ g w, eG.symm g w = g w := fun g w =>
    (hG (eG.symm g) w.1 w.2 w.2).symm.trans (congrFun (eG.apply_symm_apply g) w)
  refine topLev_datY I l Z ok pins v F hF hr _ cg ξ (fun g => ?_) (fun g hg => ?_) hcg
  · exact ⟨fun h w => he g w ▸ h w (Set.mem_univ w), fun h w _ => (he g w).symm ▸ h w⟩
  · have e := Formalism.L2.Col.LevFam.chr_apply (X := B.fields) I.Ps ⟨eG.symm g.1, g.2⟩
    refine (congrArg (fun x : B.fields.Kˣ => B.embLL (x : B.fields.K)) e).trans ?_
    show B.embLL ((∏ w, _ : B.fields.Kˣ) : B.fields.K) = _
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    exact congrArg (fun x => B.embLL (((I.Ps w).lam x : B.fields.Kˣ) : B.fields.K)) (Subtype.ext (he g.1 w))

def PairDataBaseTupleLevelEqualsClassLevel {D : D7} {O : Obj D} (x : R3.TwIn O.ex) {u : D.what₂.Word} (K₀ : ClsPTied u) : Prop :=
  ∀ t : x.T, x.Y.tup t = D.what₂.mu0 →
    GlobalTheory.Core.Rk.Top.TopLev K₀ (levS _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))
      (levChi _ x.R.βX (datXP x.R.toRealDat (x.R.toRealDat.levR x.F.lv2 true) t))




end GlobalTheory.Fam.BaseLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  first | exact @GlobalTheory.LevPrimeMid.lawLevelPrime_double | exact GlobalTheory.LevPrimeMid.lawLevelPrime_double | (intros; apply GlobalTheory.LevPrimeMid.lawLevelPrime_double <;> assumption)
end

