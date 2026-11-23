module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReproducingPolynomialValueAtOneMaxCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealQuotientMinorEqConstSmulComplementMinor
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaLevelVPCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.LevelLawCore

theorem omega_level_vP_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Vc D i)), VStd D i → k ∈ GfC (Vc D i) → ∀ hk : fin (Vc D i) k ∈ levJ R i t, R.ωP i t (k, 1) (R.vP i t) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t k _ hf hk
  have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
      (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
  have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hf, hl.1, Subgroup.mem_bot.1 hl.2⟩
  have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
    ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
  refine (_root_.GlobalTheory.VecInv.omega_lifts_vP R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 k 1 hκ hκ').trans ?_
  exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
    (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm

end GlobalTheory.AdTh.LevelLawCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowOfBaseTupleIdentityRowSpan
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)


set_option maxHeartbeats 1000000 in
theorem pins_merge_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {ι x₀}
    (hsrc : ∀ j, (src j).Pins κ v₀ ι x₀)
    (hlift : ThPinsR R i jL₃ (inC c₃) v₀ c0₃ ι C.Q.l.M (Mfr C.Q.l) lev)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c fun g => (lev g, LinearMap.id))
    (hio : IoLFRec c₃ (fun τ => embF c₃ (tauE D τ)) (lamV D i) (wtA κ) io₃ hw₃)
    (hh : ∀ j, ∃ J', RepsR R i (tup j) (h j) ((src j).bad ()) J' ((src j).Lh ()) ((src j).gam ()) ((src j).vol ()))
    (c0 : ℂ) (hc0 : ∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) (cs : J → ℂ) (hu : ∀ j, (u j : ℂ) * cs j = c0)
    (hcs : ∀ j, CXiAt (Wc D i) (rank_Wc i) (inC (src j).c') ((src j).dδ ()) ((src j).U₂ ()) ((src j).dict₂ ()) ι x₀
      ((src j).xi ()) (cs j)) :
    (merge src c₃ h₃ hs jL₃ hV₃ c0₃ lev io₃ hw₃ u h v₀).Pins κ v₀ ι x₀ := by
  have hu0 : ∀ j, u j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, e⟩ := hc0
    rw [← hu j, h0] at e
    simp [hm.ne'] at e
  refine ⟨hlift, fun j => ⟨?_, ((hsrc j).tuple ()).B, ((hsrc j).tuple ()).xi, ((hsrc j).tuple ()).phi, ((hsrc j).tuple ()).half⟩,
    ⟨hact, (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).1⟩, fun j => (hsrc j).bad (), fun j => (hsrc j).reps (),
    fun j => ⟨fun k => congrArg (incF _ c₃ (hs j)) (((hsrc j).ep ()).1 k), epIs_map (hs j) ((hsrc j).ep ()).2⟩, hio,
    fun j k q => phiHat_covBC (hs j) _ (u j) _ _ q ((hsrc j).w () k q),
    fun j => covPin_covBC (hs j) _ (hu0 j) ((hsrc j).cov ()), ?_, fun j => (hsrc j).model₂ ()⟩
  · obtain ⟨J', hr⟩ := hh j
    obtain ⟨_, _, _, hT, hc⟩ := hlift.c0
    exact ⟨h j, J', repsR_map _ hr,
      GlobalTheory.RationalValues.placeEx R i jL₃ (inC c₃) (tup j) (h j) c0₃ hMo.jV hT hc hL hW hF.pl_onto hF.muVal,
      thAdIs_thAdOf R i (tup j) (h j) c0₃ hMo.HV hr.2.2.1 hr.2.2.2.2.2.1 v₀, fun _ => Iff.rfl⟩
  · refine (cXiVal_iff _ _ _ _ _ _ _ _ _).2 ⟨c0, hc0, fun j => ?_⟩
    rw [← hu j]
    exact GlobalTheory.OneMapAll.cXiAt_covBC D _ _ _ _ _ _ _ _ (hs j) _ _ _ (u j) _ _ _ _ _ _ ((hsrc j).cov ()).1.2.2.2.2.2.2.2.1 (hcs j)

end Merge

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

variable {T R κ v₀}


set_option maxHeartbeats 1600000 in
theorem exists_extension_of_clauses (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    {i : Fin D.R.m} {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (hO' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ (M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0)) (h₁ : O.c'.F ≤ M.c'.F), M.lev = O.lev ∧
      M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
      ∀ x, O.Plc () x → ∃ x', M.Plc none x' ∧ M.thAd none x' = O.thAd () x ∧
        ∀ f ∈ sec _ O.c' (wtA (κ i)) (Vc D i).rank, IsSum O () x f → IsSum M none x' (rulBC h₁ f) := by
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₃, h', haF, hbF⟩ := exists_coeff_roots O'.c' ha hb
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := by
    rw [sOv_eq, ← sOv_eq T.toCore O.c' O.hle]; exact O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.IoExtend.exists_ioLFRec_over _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) (v₀ i (sg0 D A)) c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge_of_clauses src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h (v₀ i (sg0 D A)) hL hW hF hMo
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 h₀ c0₃ (jVx R i A.μ0 y) x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  refine ⟨x', ⟨y, hy'⟩, (thAdIs_thAdOf R i A.μ0 h₀ c0₃ hMo.HV hr₀.2.2.1 hr₀.2.2.2.2.2.1 _ _ _ hy').trans
    (hth₀ _ _ hy).symm, fun f hf hfx => ?_⟩
  exact isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
    (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx

variable (T R κ v₀)

theorem oneMapRowR_of_clauses (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hF : R.IsFam) (hMo : R.IsModels)
    (hpins : OMPins T R κ v₀ O i) (htie : PhaseTie T R κ v₀ O ph i)
    (hrow0 : OneMapRow0 T R κ v₀ O i) (hex : PinnedDataExist T R κ v₀ i) (hid : IdentityRow T R κ v₀ i)
    (hspan : ClassSumsSpan (O i) (κ i)) : OneMapRowR T R κ v₀ O ph i := by
  refine ⟨hrow0, fun hG => ?_⟩
  obtain ⟨O', hLL', hP'⟩ := hex hG
  have hP := hpins.2
  rw [show O'.s0 = T.σ₀ from sOv_eq _ _ _] at hP'
  rw [show (O i).s0 = T.σ₀ from sOv_eq _ _ _] at hP
  obtain ⟨M, h₁, hlev, hM, hext⟩ := exists_extension_of_clauses hL hW hF hMo (O i) O' (hpins.1.le.trans hLL') hP hP'
  have hLM : D.what₂.embLL.toRatAlgHom.fieldRange ≤ M.c'.F := hpins.1.ge.trans h₁
  rw [← show M.s0 = T.σ₀ from sOv_eq _ _ _] at hM
  obtain ⟨cc', ph', hrow⟩ := hid _ _ M hLM hM
  exact ⟨comap M some, hLM, pins_comap some hM, oneMapOf_comap some
    (oneMapOf_of_extends (O i) M none h₁ hlev hM hext hspan (T.cE ((i : ℕ) + 1)) (htie hrow0) hrow)⟩

end Row

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfold

theorem exists_fin_mul_real {D : D7} (V : HSp D) (u : GA D V) : ∃ k ∈ GfC V, ∃ a ∈ GinfC V, u = k * a ∧ fin V k = fin V u := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V u)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 u.2).2⟩
  let k' : GA D V := ⟨k, hk⟩
  have e : finHom V k' = finHom V u := k2
  refine ⟨k', k1, k'⁻¹ * u, ?_, (mul_inv_cancel_left _ _).symm, Subtype.ext e⟩
  show finHom V (k'⁻¹ * u) = 1
  rw [map_mul, map_inv, e, inv_mul_cancel]

theorem integrand_right {H G' Gf W X : Type} [Group H] [Group G'] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (p : H →* Gf) (L : W →ₗ[ℂ] (X → ℂ)) (f : Gf → W)
    (u k a : H) (hu : u = k * a) (c : ℂˣ) (hk : ρ k⁻¹ = 1) (ha : p a = 1) (hf : ∀ z, f (z * p k) = (c : ℂ) • f z)
    (hLk : ∀ w, om (k, 1) (L w) = (c : ℂ)⁻¹ • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (x : H) (g : G') :
    om (x * u, g) (L (ρ (x * u)⁻¹ (f (p (x * u))))) = om (x, g) (L (ρ x⁻¹ (f (p x)))) := by
  subst hu
  have e1 : (x * (k * a), g) = (x, g) * (k, (1 : G')) * (a, (1 : G')) := by simp [mul_assoc]
  have e2 : ρ a * ρ (x * (k * a))⁻¹ = ρ x⁻¹ := by
    rw [← map_mul, show a * (x * (k * a))⁻¹ = k⁻¹ * x⁻¹ by group, map_mul, hk, one_mul]
  rw [e1, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa, ← Module.End.mul_apply (ρ a), e2, hLk,
    map_mul p, map_mul p, ha, mul_one, hf, map_smul (ρ x⁻¹), map_smul L, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]

theorem form_right {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (k : J) (z : H) :
    f (z * k) = (χ k : ℂ) • f z := by
  have := hf 1 z k
  rwa [map_one, map_one, one_mul] at this

theorem integral_theta {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 ((levEnv S β L).χ ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0


end GlobalTheory.LiftUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierLeftIsometryL2Statement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_left_isometry_l2 : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL (κ' := κ') A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.DoublingEvaluationL2.partL_lintegral_sq | exact GlobalTheory.DoublingEvaluationL2.partL_lintegral_sq | (intros; apply GlobalTheory.DoublingEvaluationL2.partL_lintegral_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierRightIsometryL2Statement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fourier_right_isometry_l2 : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partR (κ := κ) A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ', ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partR (κ := κ) A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.DoublingEv.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | exact GlobalTheory.DoublingEv.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA | (intros; apply GlobalTheory.DoublingEv.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicTemperedDistPoisson
section
open scoped Classical

namespace GlobalTheory.IntComb

noncomputable def dotForm (n : ℕ) : LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply (n : ℕ) (x y : Fin n → ℝ) : dotForm n x y = ∑ i, x i * y i := rfl

theorem dotForm_nondegenerate (n : ℕ) : (dotForm n).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have := hx (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this
  · intro y hy
    funext i
    have := hy (Pi.single i 1)
    simpa [dotForm_apply, Pi.single_apply] using this

noncomputable abbrev intLat (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem mem_intLat {n : ℕ} (x : Fin n → ℝ) :
    x ∈ intLat n ↔ ∃ k : Fin n → ℤ, x = fun i => (k i : ℝ) := by
  rw [intLat, (Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x]
  simp only [Pi.basisFun_repr, Set.mem_range, eq_intCast]
  constructor
  · intro h
    choose k hk using h
    exact ⟨k, funext fun i => (hk i).symm⟩
  · rintro ⟨k, rfl⟩ i
    exact ⟨k i, rfl⟩

noncomputable def intLatEquiv (n : ℕ) : (Fin n → ℤ) ≃ intLat n :=
  Equiv.ofBijective (fun k => ⟨fun i => (k i : ℝ), (mem_intLat _).2 ⟨k, rfl⟩⟩)
    ⟨fun k k' h => by
      funext i
      have : ((k i : ℤ) : ℝ) = (k' i : ℝ) := congrFun (congrArg Subtype.val h) i
      exact_mod_cast this,
     fun l => by
      obtain ⟨k, hk⟩ := (mem_intLat l.1).1 l.2
      exact ⟨k, Subtype.ext hk.symm⟩⟩

theorem dirac_comb_unique : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  intro n T htr hmod
  obtain ⟨c, hc⟩ := GlobalTheory.LatticeComb.comb_unique (Fin n → ℝ) (dotForm n) (dotForm_nondegenerate n)
    (intLat n) 0 T
    (fun l hl f f' hf => by
      obtain ⟨k, rfl⟩ := (mem_intLat l).1 hl
      exact htr k f f' hf)
    (fun μ hμ f f' hf => by
      have hi : ∀ i, ∃ z : ℤ, μ i = z := by
        intro i
        obtain ⟨z, hz⟩ := hμ (Pi.single i 1) ((mem_intLat _).2 ⟨Pi.single i 1, by
          funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]⟩)
        refine ⟨z, ?_⟩
        rw [← hz, dotForm_apply]
        simp [Pi.single_apply]
      choose m hm using hi
      have hμm : μ = fun i => (m i : ℝ) := funext hm
      subst hμm
      have h0 : dotForm n 0 (fun i => (m i : ℝ)) = 0 := by simp
      rw [h0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      refine hmod m f f' fun x => ?_
      rw [hf x, dotForm_apply]
      congr 3
      push_cast
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
  refine ⟨c, fun f => ?_⟩
  rw [hc f, ← (intLatEquiv n).tsum_eq]
  simp only [zero_add]
  rfl

end GlobalTheory.IntComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyCoeffVectorsLieInFiniteDimensionalSmooth
section
namespace GlobalTheory.PsCo.Pc3

theorem uFin : UFin := GlobalTheory.T.uniformFiniteness_of_reproducingPolynomial_averaging _root_.GlobalTheory.PsCo.Pc3.fock_reproducing_formula _root_.GlobalTheory.PsCo.PolyAvg.polyAvg

end GlobalTheory.PsCo.Pc3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealQuotientMinorEqConstSmulComplementMinorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor : ∀ (D : D7) {a a' d : ℕ} (had : a + a' = d) (n₀ : D.what₂.Tau → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : PolF D d a →ₗ[ℂ] Pr) (q' : PolF D d a' →ₗ[ℂ] Pr) (σ : (D.what₂.Tau → Matrix (Fin d) (Fin d) ℂ) → Module.End ℂ Pr),
    0 < a → 0 < a' → Nontrivial Pr → Function.Surjective q → Function.Surjective q' →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a) ℂ) (P : PolF D d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin a') ℂ) (P : PolF D d a'),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) P) = GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a') (Fin a') ℂ)) • q' P) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a d n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ).map (starRingEnd ℂ)) P) = σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q P)) →
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin d) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) a' d n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) (q' P)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D a d n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  first | exact @GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | exact GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl | (intros; apply GlobalTheory.SchurQuot.quot_minor_eq_const_smul_compl <;> assumption)
end

