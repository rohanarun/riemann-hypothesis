module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaDataLevelForms
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCoverBound
section
open NumberField

namespace GlobalTheory.CovTop

open GlobalTheory.BigTop Formalism.IndefR.FWT

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem rho_mem_WK (p : PtAt ex Csz) (i : Fin D.R.m) (g) (f) (hf : f ∈ (p.R.toRealDat.FW i).WK) :
    (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).WK := by
  by_cases hk : ActKeeps (κ := p.κ) p.O i
  · obtain ⟨c, hc⟩ := (p.fw.e i).surjective ⟨f, hf⟩
    obtain ⟨_, h2⟩ := (p.rhoGeo i).1 hk g c
    rw [hc] at h2
    rw [← h2]
    exact Subtype.property _
  · rw [(p.rhoGeo i).2 hk g]
    exact hf

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuples
section
noncomputable section

namespace GlobalTheory.LiftSpanClauses

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.OneMapTuples GlobalTheory.OneMapAll
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

open GlobalTheory.PinnedClassSum GlobalTheory.GeoLevel GlobalTheory.Member Formalism.L2.Host


set_option maxHeartbeats 2000000 in
theorem clsEx_of_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsFam → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → GlobalTheory.OneMapTuples.ClsEx O (κ i) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hF ⟨tie⟩ _ i Tp tup O hLL hO t x _
  have hT := tie.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hr : 1 ≤ D.R.r := by
    have h1 := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2.1
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hσ : GoodEmb T.Q.c O.s0 := rfl
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  obtain ⟨hd, hA₂, hnab⟩ := hO.cov t
  obtain ⟨-, -, hxi, ⟨e, -, hφ⟩, hMb, hQ, -⟩ := hO.tuple t
  obtain ⟨c0, ⟨m, hm, hc0⟩, hv⟩ := hO.cxi
  obtain ⟨n, hn, ho⟩ := hL.xi_fin (tup t)
  obtain ⟨xi', hx1, -, hx3, hx4⟩ := GlobalTheory.TupleCover.exists_xi D (Wc D i) (R.xi (tup t)) (R.xiH (tup t)) (hL.xi _) n hn ho
    (hL.xi_triv _) (hL.xi_tame _)
  have hxx : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) =
      xi' (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) := fun g => by
    obtain ⟨z, hz⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    exact Units.ext ((hxi g z hz).trans (hx1 g z hz).symm)
  have hxN : ∀ g : GA D (Wc D i), O.xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) ^ (m * n) = 1 := fun g => by
    rw [hxx, mul_comm, pow_mul, hx4, one_pow]
  have hcN : c0 ^ (m * n) = 1 := by rw [pow_mul, hc0, one_pow]
  obtain ⟨gramR, c0R, c0L, hfam⟩ := hF.tie
  obtain ⟨ψ, hψ⟩ := exists_psi (Wc D i) (O.dδ t) (iotaW T i) hio.emb (hpq.trans (rank_Wc i).symm) hpos hd (R.Q (tup t)) hQ
    (R.xiR (tup t)) fun P hP z =>
      hLL (GlobalTheory.RationalValues.xiR_mem R hL hF.pl_onto hF.muVal hfam.ok i (tup t) P hP z)
  have htie : (O.dδ t).PsiTie ψ := by
    refine psiTie_of_values (Wc D i) (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      (fun γ hγ => (hxx γ).trans (hx3 γ hγ)) _ _ c0 hcN (hv t) ψ fun k s u hu₀ hu hk hlift => ?_
    obtain ⟨y, -, hdet⟩ := exists_int_matrix (hL.βW i) hu
    have hres : ∀ P : R.Q (tup t), ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc (resS D.host.F P.1) y) : (kP P.1)ˣ) : kP P.1) =
        resS D.host.F P.1 y.1.det := fun P => ((resS D.host.F P.1).map_det _).symm
    obtain ⟨z, hz, hval⟩ := exists_root_value (O.dδ t).l₂ hu₀ (hL.xi (tup t)) (hL.xi_tame _) (R.Q (tup t)) (R.xiR (tup t))
      (hL.xiR _) (fun P hP => (hd.2.2.2.1.le.trans Ideal.mul_le_right).trans (hQ P hP)) (fun P => (hL.Q_ram _ P).1) _ hdet _ hres
    exact (hψ k s u _ hk hlift hdet _ hres).trans (hval.symm.trans (hxi u z hz).symm)
  have hτ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos
    omega)
  obtain ⟨τ₀⟩ := hτ
  have hnV : (κ i).n = (Vc D i).rank := (tie.kap i τ₀).2.2.trans (D.sp.V_rank _ hj.1 hj.2).symm
  have hlast : (κ i).LastPos := fun τ k hk => by
    rw [(tie.kap i τ).1 k, show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
    refine GlobalTheory.LiftWeight.one_le_aPl_last D i τ _ _ ?_ hk
    simp only [Ranks.sigW]
    omega
  obtain ⟨-, cga, -, -, hrange, -⟩ := hO.io
  exact GlobalTheory.ClsVal.exists_cusp_isThClsD_unique GlobalTheory.ChartFree.chartIndep _ _ _ _ _ O.c' _ (O.dδ t) _ _ hr
    (fun σ hσ' => GlobalTheory.OneMapAll.isUnf_unfExt O.hle σ (fun _ => rfl) (hT.unf _ hj (σ.comp (incF T.Q.c O.c' O.hle)) hσ')) hT.pins.2.1.2
    (fun _ => ⟨hd, hA₂, hnab⟩)
    (GlobalTheory.OneMapTuples.unitC_of_cXiAt D _ _ (Wc D i) _ _ _ _ _ (O.dδ t) (rank_Wc i) _ hio hpos _ hx₀ hd hA₂ (O.xi t) _ (Nat.mul_pos hm hn) hxN
      _ _ c0 hcN (hv t))
    ψ htie _ (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.bad t) (O.vol t) (O.ep t) _ O.io (wtA (κ i)) (hnV ▸ dom_wtA (κ i))
    (GlobalTheory.lastPos_wtA_of_pins D T.Q hT.pins _ hj _ hlast)
    (fun k => datEq_of_values (Vc D i) (Wc D i) (R.βV i) (R.βW i) (hL.βW i) e (O.dδ t) hd _ hio R.Pg (R.Q (tup t))
      (fun P hP => hMb.le.trans (Ideal.prod_le_inf.trans (Finset.inf_le hP))) hQ _ (O.φ t) _ (hO.w t k)
      (fun z => (hφ z).1) (fun z => (hφ z).2) ψ hψ)
    (hO.reps t).1 hrange.le x

end Cls

section Retie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem placeEx_core {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La} (hP : ThPinsR R i jL σ' v₀ c0' ι M Mh lev)
    (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c0' := by
  obtain ⟨_, _, _, hT, hc⟩ := hP.c0
  exact GlobalTheory.RationalValues.placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}


set_option maxHeartbeats 1600000 in
theorem exists_retie_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hP : O.Pins κ v₀ ι x₀)
    (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
    (hlev : LevIs R i ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id)) {gramR c0R c0L}
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L) :
    ∃ O' : OMDat C R i Tp tup, O'.c' = O.c' ∧ O'.Pins κ v₀ ι x₀ ∧ O'.lev = lev ∧ CoefficientBaseChange R i O'.jL (inC O'.c') (c0L i) O'.c0' := by
  classical
  obtain ⟨c1, hc1⟩ := exists_coef_ext (W := (R.cV i).W) O.jL hP.lift.field (lamV D i) (c0L i)
  choose h J' h1 h2 h3 h4 using fun t => (hP.tuple t).reps
  have hL : ThPinsR R i O.jL (inC O.c') v₀ c1 ι C.Q.l.M (Mfr C.Q.l) lev :=
    ⟨hP.lift.field, hP.lift.std, hP.lift.v0, ⟨_, _, _, hT, hc1⟩, hlev⟩
  have h0 : ∀ t y, (∀ k, (R.HV i (tup t)).e y (fin _ (h t k)) = 0) → onQ (Wc D i) (R.thF i (tup t) y v₀) = 0 := fun t y hy => by
    have e1 := h3 t y 0 fun k => (hy k).trans (map_zero _).symm
    have e2 := h3 t 0 0 fun k => by rw [map_zero]; exact (map_zero _).symm
    rw [← e1, e2, map_zero]
    rfl
  refine ⟨{ O with
    c0' := c1, lev := lev
    thAd := fun t x => if hx : ∃ y, Place R i (tup t) (h t) c1 y x then onQ (Wc D i) (R.thF i (tup t) hx.choose v₀) else 0
    Plc := fun t x => ∃ x₀, Place R i (tup t) (h t) c1 (jVx R i (tup t) x₀) x }, rfl,
    ⟨hL, fun t => ⟨⟨h t, J' t, h1 t, placeEx_core R F hR i _ _ hL _ _, fun y x hy => ?_, fun x => Iff.rfl⟩,
      (hP.tuple t).B, (hP.tuple t).xi, (hP.tuple t).phi, (hP.tuple t).half⟩,
      ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).1⟩,
      hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩, rfl, hc1⟩
  have hx : ∃ y, Place R i (tup t) (h t) c1 y x := ⟨y, hy⟩
  refine (dif_pos hx).trans ?_
  have h5 := h0 t (hx.choose - y) fun k => by
    rw [map_sub, Pi.sub_apply, hx.choose_spec k, hy k, sub_self]
  rw [map_sub] at h5
  exact sub_eq_zero.1 h5

end Retie

def PointIdentCore : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0

section Guard

open GlobalTheory.LiftSpan

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 2000000 in
theorem liftsSpan_of_guard_core (hPI : PointIdentCore) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hR : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀))
    (hpb : T.pb = R.C.P.pb) (hio : IoExt R) (hO : OMPins T R κ v₀ O i) (hex : PinsExist T R κ v₀ i) (hG : QGuard R)
    (hspan : ClassSumsSpan (O i) (κ i)) : LiftsSpan R i (v₀ i (sg0 D A)) := by
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, -, hU⟩ := hPI D G Pl0 T0 A T R F κ v₀ hR h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hle₀, hP₀⟩ := hex hG
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := exists_retie_core O₀ hR
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := e₁ ▸ hle₀
  obtain ⟨c0, -, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  exact liftsSpan_of_ptIdent hP hspan hP₁ hlev₁ (clsEx_of_core D G Pl0 T0 A T R κ v₀ hR.lev hR.fam hW hpb i _ _ O₁ hle₁ hP₁)
    (ne_zero_of_root hr₁) (hU _ _ (O i) hO.1.ge hP rfl hc c0 hx) (hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁)

end Guard

end GlobalTheory.LiftSpanClauses

namespace GlobalTheory.LiftSpanClauses

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem liftsSpan_all_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hsz hC h1 h2 hW hio hO h0 hG
  obtain ⟨fw⟩ := id hW
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hC.lev (hO.2.tuple ()).half
  have hex : GlobalTheory.OneMapTuples.PinsExist T R κ v₀ i := fun hG' => by
    obtain ⟨O', a, b, -⟩ := GlobalTheory.PinnedTuples.exists_pins_of_base D G Pl0 T0 A T R κ v₀ O hC.lev hC.grp.chiW hC.fam hC.models
      hC.thP.vP h1 h2 hW i hO hG'
    exact ⟨O', a, b⟩
  exact liftsSpan_of_guard_core _root_.GlobalTheory.PtIdCore.point_identity_core T R F κ v₀ O i hC h1 h2 hW hpb hio hO hex hG
    (GlobalTheory.ClassSumSpanCore.classSumsSpan_core D G Pl0 T0 A T R F κ v₀ O hsz hC hW hio i hO h0)

end GlobalTheory.LiftSpanClauses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueMatrixDatumFourierExpansionGaussSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ResidueFourier

section Local

variable {k : Type} [Field k] [Fintype k]

theorem sum_char_trace {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (w : Matrix (Fin n) (Fin r) k) :
    ∑ x : Matrix (Fin r) (Fin n) k, ψ (Matrix.trace (x * w)) =
      if w = 0 then ((Nat.card k : ℂ) ^ (n * r)) else 0 := by
  let L : Matrix (Fin r) (Fin n) k →+ k :=
    AddMonoidHom.mk' (fun x => Matrix.trace (x * w)) (fun a b => by rw [Matrix.add_mul, Matrix.trace_add])
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom L)
  have h2 : ψ.compAddMonoidHom L = 0 ↔ w = 0 := by
    constructor
    · intro h0
      ext i j
      by_contra hne
      refine hψ hne ?_
      ext t
      have := DFunLike.congr_fun h0 (Matrix.single j i t)
      change ψ (Matrix.trace (Matrix.single j i t * w)) = 1 at this
      rw [Matrix.trace_single_mul, smul_eq_mul] at this
      rw [AddChar.mulShift_apply, mul_comm]
      exact this
    · rintro rfl
      ext x
      change ψ (Matrix.trace (x * (0 : Matrix (Fin n) (Fin r) k))) = 1
      simp
  refine Eq.trans h ?_
  by_cases hw : w = 0
  · rw [if_pos (h2.2 hw), if_pos hw, Nat.card_eq_fintype_card]
    have : Fintype.card (Matrix (Fin r) (Fin n) k) = Fintype.card k ^ (n * r) := by
      change Fintype.card (Fin r → Fin n → k) = _
      simp [pow_mul]
    rw [this]; push_cast; rfl
  · rw [if_neg (fun h => hw (h2.1 h)), if_neg hw]

theorem inversion {n r : ℕ} {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) (f : Matrix (Fin n) (Fin r) k → ℂ)
    (u : Matrix (Fin n) (Fin r) k) :
    f u = ∑ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) := by
  have hc : ((Nat.card k : ℂ) ^ (n * r)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have h1 : ∀ x : Matrix (Fin r) (Fin n) k,
      (((Nat.card k : ℂ) ^ (n * r))⁻¹ * ∑ v, f v * ψ (Matrix.trace (-x * v))) * ψ (Matrix.trace (x * u)) =
      ∑ v, ((Nat.card k : ℂ) ^ (n * r))⁻¹ * f v * ψ (Matrix.trace (x * (u - v))) := fun x => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [mul_assoc, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← Matrix.trace_add, Matrix.mul_sub, Matrix.neg_mul,
      neg_add_eq_sub]
  simp only [h1]
  rw [Finset.sum_comm, Finset.sum_eq_single u]
  · rw [← Finset.mul_sum, sum_char_trace hψ, if_pos (sub_self u)]
    field_simp
  · intro v _ hv
    rw [← Finset.mul_sum, sum_char_trace hψ, if_neg (fun h => hv (sub_eq_zero.1 h).symm), mul_zero]
  · simp

def embTop (n : ℕ) {r : ℕ} (g : Matrix (Fin r) (Fin r) k) : Matrix (Fin n) (Fin r) k :=
  fun i j => if h : i.val < r then g ⟨i.val, h⟩ j else 0

omit [Fintype k] in
theorem topL_embTop {n r : ℕ} (h : r ≤ n) (g : Matrix (Fin r) (Fin r) k) : topL r (embTop n g) = g := by
  ext i j
  have : i.val < n := lt_of_lt_of_le i.2 h
  simp [topL, embTop, this]

omit [Fintype k] in
theorem lowZero_embTop {n r : ℕ} (g : Matrix (Fin r) (Fin r) k) : LowZero r (embTop n g) := by
  intro i j hi _
  simp [embTop, not_lt.2 hi]

omit [Fintype k] in
theorem embTop_topL {n r : ℕ} {u : Matrix (Fin n) (Fin r) k} (hu : LowZero r u) : embTop n (topL r u) = u := by
  ext i j
  by_cases hi : i.val < r
  · simp [topL, embTop, hi]
  · simp [embTop, hi, hu i j (not_lt.1 hi) j.2]

omit [Fintype k] in
theorem trace_embTop {n r : ℕ} (h : r ≤ n) (x : Matrix (Fin r) (Fin n) k) (g : Matrix (Fin r) (Fin r) k) :
    Matrix.trace (x * embTop n g) = Matrix.trace (topL r x * g) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_add]
  have h2 : ∀ i : Fin r, i.val < r + t := fun i => lt_of_lt_of_le i.2 h
  simp [embTop, topL, h2]
  rfl

theorem transform {n r : ℕ} (h : r ≤ n) {ψ : AddChar k ℂ} (hψ : ψ.IsPrimitive) {ξ : kˣ →* ℂˣ} (hξ : ξ ≠ 1)
    (x : Matrix (Fin r) (Fin n) k) :
    ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      (∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (g : Matrix (Fin r) (Fin r) k))) *
      (if h : IsUnit (topL r x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) := by
  obtain ⟨h0, h1⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ r hψ hξ
  have step : ∑ v : Matrix (Fin n) (Fin r) k,
      (if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) * ψ (Matrix.trace (x * v)) =
      ∑ g : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) *
        ψ (Matrix.trace (topL r x * (g : Matrix (Fin r) (Fin r) k))) := by
    symm
    apply Finset.sum_of_injOn (fun g : GL (Fin r) k => embTop n (g : Matrix (Fin r) (Fin r) k))
    · intro a _ b _ hab
      have := congrArg (topL r) hab
      simp only [topL_embTop h] at this
      exact Units.ext this
    · intro a _
      simp
    · intro u _ hu
      rw [dif_neg, zero_mul]
      rintro ⟨hl, hd⟩
      exact hu ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, by simp, embTop_topL hl⟩
    · intro g _
      have hx : IsUnit (topL r (embTop n (g : Matrix (Fin r) (Fin r) k))).det := by
        rw [topL_embTop h]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      have hdet : hx.unit = Matrix.GeneralLinearGroup.det g := Units.ext (by simp [topL_embTop h])
      rw [dif_pos ⟨lowZero_embTop _, hx⟩, trace_embTop h, hdet, zpow_neg_one, Units.val_inv_eq_inv_val]
  rw [step]
  by_cases hy : IsUnit (topL r x).det
  · have hm := (Matrix.isUnit_iff_isUnit_det _).2 hy
    have hdet : Matrix.GeneralLinearGroup.det (hm.unit : GL (Fin r) k) = hy.unit :=
      Units.ext (by simp [Matrix.GeneralLinearGroup.det])
    have key := h1 hm.unit
    rw [hdet] at key
    simp only [IsUnit.unit_spec, one_mul] at key
    rw [key, dif_pos hy, mul_comm]
  · have hz : (topL r x).det = 0 := by simpa using hy
    rw [h0 _ hz, dif_neg hy, mul_zero]

end Local

theorem dite_prod {ι : Type} (Q : Finset ι) (p : ι → Prop) (f : ∀ i, p i → ℂ) :
    (if h : ∀ i ∈ Q, p i then ∏ i ∈ Q.attach, f i.1 (h i.1 i.2) else 0) =
      ∏ i ∈ Q.attach, if h : p i.1 then f i.1 h else 0 := by
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (dif_pos (h i.1 i.2)).symm
  · push_neg at h
    obtain ⟨i, hi, hp⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_attach Q ⟨i, hi⟩) (dif_neg hp)).symm

theorem omegaQ_fourier : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∃ c : (∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) → ℂ, (∀ u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP), omegaQ Q r ξ (-1) u = ∑ x, c x * ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (x PP * u PP.1))) ∧ ∀ (x : ∀ PP : ↥Q, Matrix (Fin r) (Fin n) (kP PP.1)) (y : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP)), (∀ PP : ↥Q, y PP.1 = x PP) → c (-x) = (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) * omegaFlat Q r ξ y := by
  intro D _ Q n r hrn ψP ξ hψ hξ
  let f : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP) → ℂ := fun PP v =>
    if h : LowZero r v ∧ IsUnit (topL r v).det then ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0
  let c : ∀ PP : Pl D.host.E, Matrix (Fin r) (Fin n) (kP PP) → ℂ := fun PP x =>
    ((Nat.card (kP PP) : ℂ) ^ (n * r))⁻¹ * ∑ v, f PP v * ψP PP (Matrix.trace (-x * v))
  refine ⟨fun x => ∏ PP ∈ Q.attach, c PP.1 (x PP), fun u => ?_, fun x y hxy => ?_⟩
  · have h1 : omegaQ Q r ξ (-1) u = ∏ PP ∈ Q.attach, f PP.1 (u PP.1) := by
      unfold omegaQ
      convert dite_prod Q (fun PP => LowZero r (u PP) ∧ IsUnit (topL r (u PP)).det)
        (fun PP h => ((ξ PP h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ))
    have h2 : ∀ PP : ↥Q, f PP.1 (u PP.1) = ∑ x, c PP.1 x * ψP PP.1 (Matrix.trace (x * u PP.1)) := fun PP => by
      letI := Ideal.Quotient.field PP.1.asIdeal
      exact inversion (k := kP PP.1) (hψ PP.1 PP.2) (f PP.1) (u PP.1)
    rw [h1]
    simp only [h2, ← Finset.prod_mul_distrib, Finset.attach_eq_univ]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  · have h1 : omegaFlat Q r ξ y = ∏ PP ∈ Q.attach, if h : IsUnit (topL r (y PP.1)).det then ((ξ PP.1 h.unit : ℂˣ) : ℂ) else 0 := by
      unfold omegaFlat
      convert dite_prod Q (fun PP => IsUnit (topL r (y PP)).det) (fun PP h => ((ξ PP h.unit : ℂˣ) : ℂ))
    rw [h1, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    rw [hxy PP, mul_assoc]
    simp only [c, Pi.neg_apply, neg_neg]
    congr 1
    letI := Ideal.Quotient.field PP.1.asIdeal
    convert transform (k := kP PP.1) hrn (hψ PP.1 PP.2) (hξ PP.1 PP.2) (x PP)

end GlobalTheory.ResidueFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_det_ne {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

end GlobalTheory.MassLinkSD
end
end

