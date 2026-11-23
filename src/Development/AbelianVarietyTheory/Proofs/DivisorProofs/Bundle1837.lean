module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointFactorIntegralSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.point_factor_integral_subalgebra : ∀ (K B E : Type) [Field K] [CommRing B] [CommRing E]
    [Algebra K B] [Algebra K E] (i : E →ₐ[K] B), Function.Injective i →
    (∀ b : B, _root_.IsIntegral K b → b ∈ i.range) → ∀ (T : Scheme.{0}) (p : T ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)
    [IsFinite p] (t : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp B ⟶ T), t ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K B) →
    ∃ u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp E ⟶ T, u ≫ p = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K E) ∧ t = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i.toRingHom ≫ u := by
  intro K B E _ _ _ _ _ i hi hint T p _ t ht
  have : IsAffine T := isAffine_of_isAffineHom p
  set e := T.isoSpec
  let φ := Spec.preimage (e.inv ≫ p)
  let α := Spec.preimage (t ≫ e.hom)
  have hφ : Spec.map φ = e.inv ≫ p := Spec.map_preimage _
  have hα : Spec.map α = t ≫ e.hom := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have hcomp : φ ≫ α = CommRingCat.ofHom (algebraMap K B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, hφ]
    simpa [Category.assoc] using ht
  have hαφ : α.hom.comp φ.hom = algebraMap K B := by
    rw [← CommRingCat.hom_comp, hcomp, CommRingCat.hom_ofHom]
  have hmem : ∀ a, α.hom a ∈ i.range := by
    intro a
    apply hint
    obtain ⟨P, hP, hPa⟩ := hfin.to_isIntegral a
    refine ⟨P, hP, ?_⟩
    have h2 := congrArg α.hom hPa
    rw [Polynomial.hom_eval₂, map_zero, hαφ] at h2
    exact h2
  let eqv := AlgEquiv.ofInjective i hi
  let β : Γ(T, ⊤) →+* E := eqv.symm.toRingHom.comp (α.hom.codRestrict i.range hmem)
  have hiβ : ∀ a, i (β a) = α.hom a := by
    intro a
    change i (eqv.symm ⟨α.hom a, hmem a⟩) = α.hom a
    rw [← AlgEquiv.ofInjective_apply i hi]
    exact congrArg Subtype.val (eqv.apply_symm_apply _)
  have hβφ : β.comp φ.hom = algebraMap K E := by
    ext k
    apply hi
    rw [RingHom.comp_apply, hiβ, ← RingHom.comp_apply, hαφ]
    exact (i.commutes k).symm
  refine ⟨Spec.map (CommRingCat.ofHom β) ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap K E))
    congr 1
    ext x
    exact congrArg (fun f : K →+* E => f x) hβφ
  · change t = Spec.map (CommRingCat.ofHom i.toRingHom) ≫ _
    rw [← Category.assoc, ← Spec.map_comp]
    have hβα : CommRingCat.ofHom β ≫ CommRingCat.ofHom i.toRingHom = α := by
      ext x; exact hiβ x
    rw [hβα, hα, Category.assoc, e.hom_inv_id, Category.comp_id]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares

namespace GlobalTheory.ShareOn.Reading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main2
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


open GlobalTheory.OnTies in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem reading_of_runModel (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m) {C : Type}
    [Finite C] [MulAction p.P.Gp C] (M : TwoLevels D.host.E D.R.r p.P.Gp C) (ka : Wt M.Ψ D.R.r)
    (hb0 : 0 < badN D) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hM : RunModel p r h i M ka) :
    M.Ψ.card = D.R.f ∧ ∃ (ρ : Representation ℂ p.P.Gp (M.cusp ka)) (σ : D.what₂.LL →+* ℂ)
      (f : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[σ] M.cusp ka),
      IsPullRep M ka ρ ∧ (∀ g v, ρ g (f v) = f ((p.R.toRealDat.FW i).ρ g v)) ∧
      (LinearIndependent ℂ fun k => f (Pi.single k 1)) ∧ Submodule.span ℂ (Set.range f) = ⊤ := by
  refine ⟨card_of_runModel hM, ?_⟩
  obtain ⟨v, e, ha, hb, hc, -⟩ := hM
  obtain ⟨act, hact, hcu⟩ := h.action v i

  let Rd : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i) →ₛₗ[(r.used v).full.σ₀] M.cusp ka :=
    LinearMap.codRestrict (M.cusp ka) (rdLin h ha) fun F => Submodule.subset_span ⟨_, GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms h ha hb F, rfl⟩
  have hRd : ∀ F, ((Rd F : M.cusp ka) : C → M.dom → ℂ) = rdLin h ha F := fun F => rfl
  letI : Algebra (r.used v).full.J.Q.c.F D.what₂.LL := p.alg
  obtain ⟨σ, hσ⟩ := exists_ext_embedding (K := (r.used v).full.J.Q.c.F) (LL := D.what₂.LL) (r.used v).full.σ₀
  let cu := cuspTo (h.laws v).p (fw2 p) i
  have hcuW : ∀ F, cu F ∈ ((R2 p).FW i).WK := fun F => ((fw2 p).e i _).2
  have hcuinj : Function.Injective cu := by
    intro F G hFG
    have h1 := Subtype.ext hFG
    have h2 := ((fw2 p).e i).injective h1
    exact Submodule.inclusion_injective _ h2
  have hsurj : ∀ w ∈ ((R2 p).FW i).WK, ∃ F, cu F = w := by
    intro w hw
    refine ⟨⟨(((fw2 p).e i).symm ⟨w, hw⟩).1, by
      rw [cutR_eq _ (inR_succ i)]; exact (((fw2 p).e i).symm ⟨w, hw⟩).2⟩, ?_⟩
    show ((((fw2 p).e i) _ : ((R2 p).FW i).WK) : Fin _ → D.what₂.LL) = w
    exact congrArg Subtype.val (LinearEquiv.apply_symm_apply ((fw2 p).e i) ⟨w, hw⟩)
  obtain ⟨m, b', hbW, hbK, hspK, hbL, hspL⟩ := (fw2 p).ks i
  choose bC hbC using fun k => hsurj (b' k) (hbW k)
  have hbC' : (fun k => cu (bC k)) = b' := funext hbC
  have hbs : Submodule.span (recB (h.laws v).p.toLawsCore).KO (Set.range bC) = ⊤ := by
    rw [eq_top_iff]
    intro F _
    have h1 : cu F ∈ Submodule.span p.T.Q.c.F (Set.range b') := by rw [hspK]; exact hcuW F
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    have h2 : cu (∑ k, (show (recB (h.laws v).p.toLawsCore).KO from cf k) • bC k) = cu F := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hcf]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbC k]
      rfl
    rw [← hcuinj h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hbi : LinearIndependent D.what₂.LL (fun k => cu (bC k)) := by rw [hbC']; exact hbL
  have hbt : Submodule.span D.what₂.LL (Set.range fun k => cu (bC k)) = ⊤ := by rw [hbC']; exact hspL
  have hK : LinearIndependent (recB (h.laws v).p.toLawsCore).KO bC := by
    apply LinearIndependent.of_comp cu
    show LinearIndependent _ (fun k => cu (bC k))
    rw [hbC']; exact hbK
  have hR : LinearIndependent ℂ (fun k => Rd (bC k)) :=
    LinearIndependent.of_comp (M.cusp ka).subtype (_root_.GlobalTheory.ShareOn.Reading.rdLin_linearIndependent h ha m bC hK)
  have hRs : Submodule.span ℂ (Set.range Rd) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    have hy' : y ∈ (Submodule.span ℂ (Set.range Rd)).map (M.cusp ka).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      unfold TwoLevels.cusp at hy
      refine Submodule.span_le.2 ?_ hy
      rintro _ ⟨G, hG, rfl⟩
      obtain ⟨m', α, Fs, hGe⟩ := _root_.GlobalTheory.ShareOn.Reading.rdFun_onto h ha hb hb0 hn G hG
      have hGs : M.res G = ∑ k, α k • rdLin h ha (Fs k) := by
        funext c x
        simp only [TwoLevels.res, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rdLin_apply]
        exact hGe c x.1 x.2
      rw [hGs]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fs k, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := hy'
    have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
    rw [← hz']; exact hz
  obtain ⟨f, ρ, hfcu, hint, hind, hspan⟩ := _root_.GlobalTheory.SemilinearReading.exists_semilinear_extension_rep (r.used v).full.σ₀ σ hσ cu bC hbs hbi hbt Rd hR hRs ((R2 p).FW i).ρ
  have hρR : ∀ g F, ρ g (Rd F) = Rd (act g F) := by
    intro g F
    rw [← hfcu, ← hfcu, hint, hcu g F]
  obtain ⟨a, hpull⟩ := hc
  refine ⟨ρ, σ, f, ⟨a, fun g G hG c x => ?_⟩, hint, hind, hspan⟩
  obtain ⟨m', α, Fs, hGe⟩ := _root_.GlobalTheory.ShareOn.Reading.rdFun_onto h ha hb hb0 hn G hG
  have hy : (⟨M.res G, Submodule.subset_span ⟨G, hG, rfl⟩⟩ : M.cusp ka) = ∑ k, α k • Rd (Fs k) := by
    apply Subtype.ext
    funext c' x'
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TwoLevels.res, hRd,
      rdLin_apply]
    exact hGe c' x'.1 x'.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum]
  simp only [map_smul, hρR, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hRd,
    rdLin_apply]
  rw [TwoLevels.pull, hGe (g • c) _ (_root_.GlobalTheory.TwoLevelsDom.lact_tr_mem_dom M g c x.1 x.2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := hpull (Fs k) g c x.1 x.2 (psi_eq ha c) (psi_eq ha (g • c))
  rw [rdLin_apply]
  unfold rdFun rdR
  rw [hact g⁻¹ (Fs k)]
  refine (congrArg (α k * ·) hk).trans ?_
  ring
end Main2

end GlobalTheory.ShareOn.Reading
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictToBase
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BaseRestrict

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseA (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) : FamIn D.what₂.LL G Pl0 Unit D.R.m := A.comap (fun _ : Unit => A.μ0) ()

def baseF (F : Face D A) : Face D (baseA A) where
  P0 := F.P0
  ψ0 := F.ψ0
  P1 := F.P1
  ψ1 := F.ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

section Any

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def baseR (R : RealDat D A Ks) : RealDat D (baseA A) Ks :=
  R.comap (fun _ : Unit => A.μ0) () (fun _ => ()) R.twPl R.FW R.kap (fun i _ => R.lam i A.μ0) R.err0

variable {R : RealDat D A Ks}

set_option maxHeartbeats 2000000 in
theorem core_base {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.Hk3.Core (baseR R) (baseF F) := by
  obtain ⟨hlev, hgrp, hfam, hmod, hch, hth⟩ := h
  refine ⟨LevCh.comap_is hlev (f := fun _ : Unit => A.μ0) (fun _ _ _ => rfl) rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ q => hgrp.red_R A.μ0 q, fun i _ q => hgrp.red_L i A.μ0 q, hgrp.levels, hgrp.record, hgrp.chiW⟩
  · obtain ⟨g, c0R, c0L, ht⟩ := hfam.tie
    exact ⟨⟨g, c0R, c0L, ht.comap (fun _ : Unit => A.μ0) ()⟩, hfam.Sb, fun _ PP => hfam.roots A.μ0 PP, hfam.pl_onto,
      fun _ P => hfam.degR A.μ0 P, fun i _ P => hfam.degL i A.μ0 P, fun i _ P hP => hfam.muVal i A.μ0 P hP,
      fun P hP => hfam.etaVal P hP⟩
  · exact ⟨hmod.inf, hmod.vpos, hmod.cX, hmod.cV, hmod.prX, fun _ => hmod.HX A.μ0, fun i _ => hmod.HV i A.μ0, hmod.HE, hmod.HW,
      hmod.gE, hmod.gW, fun _ x => hmod.jX A.μ0 x, fun i _ x => hmod.jV i A.μ0 x, fun _ j h2 => hmod.νY A.μ0 j h2,
      fun _ => hmod.νY' A.μ0, hmod.ν0, fun _ => hmod.νX A.μ0, fun i _ => hmod.νV i A.μ0, hmod.νW, hmod.BV, hmod.order⟩
  · exact ⟨fun _ k hk => hch.ωY A.μ0 k hk, fun _ => hch.ωX A.μ0, fun _ k hk => hch.vY A.μ0 k hk, fun _ => hch.vX A.μ0,
      fun _ k hk P => hch.ptY A.μ0 k hk P, fun _ P => hch.ptX A.μ0 P, fun _ k hk => hch.ItY A.μ0 k hk, fun _ => hch.ItX A.μ0,
      fun _ => hch.ioY A.μ0, fun _ => hch.ioX A.μ0, fun _ => hch.Th A.μ0⟩
  · exact ⟨fun i _ => hth.ωP i A.μ0, fun i _ => hth.vP i A.μ0, fun i _ P => hth.pt_theta i A.μ0 P, fun i _ => hth.ioP i A.μ0,
      fun i _ => hth.thF_mem i A.μ0, fun i _ => hth.thF i A.μ0, fun i _ => hth.thG i A.μ0⟩

theorem ioExt_base (h : IoExt R) : IoExt (baseR R) := h

theorem qGuard_base (h : QGuard R) : QGuard (baseR R) := ⟨fun _ => h.1 A.μ0, fun _ => h.2 A.μ0⟩

theorem baseOf_base {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (baseR R) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩

theorem twLev_base {χ : Formalism.L2.Host.HChar D.host.E} {xi : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)}
    {xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (h : TwConj.TwLev R χ xi Q xiR) : TwConj.TwLev (baseR R) χ xi Q xiR :=
  ⟨h.xi, h.xi_fin, h.xi_triv, h.xi_tame, h.Q_pl, h.Q_off,
    fun p hp => (h.Q_de p hp).imp fun _ h' => ⟨fun _ => h'.1 A.μ0, h'.2⟩,
    h.Q_ram, h.xiR, h.roots, h.muVal, h.half, h.guard⟩

end Any

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}


set_option maxHeartbeats 2000000 in
def fwBase (t : FWTie T R κ v₀) : FWTie T (baseR R) κ v₀ where
  alg_eq := t.alg_eq
  e := t.e
  ks := t.ks
  kap := t.kap
  pt := t.pt
  nrm_eq := t.nrm_eq
  laws := t.laws
  chiR := t.chiR
  hv₀ := t.hv₀
  x0 := t.x0
  ev0 := t.ev0
  ev := t.ev


set_option maxHeartbeats 2000000 in
def omBase {i : Fin D.R.m} (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    OMDat T.toCore (baseR R) i Unit (fun _ => (baseA A).μ0) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := O.dδ
  Cl' := O.Cl'
  fCl := O.fCl
  bad := O.bad
  Lh := O.Lh
  La := O.La
  Nc := O.Nc
  gam := O.gam
  vol := O.vol
  ep := O.ep
  B := O.B
  epF := O.epF
  io := O.io
  hw := O.hw
  φ := O.φ
  w := O.w
  U₂ := O.U₂
  dict₂ := O.dict₂
  xi := O.xi
  thAd := O.thAd
  Plc := O.Plc

variable {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 4000000 in
theorem omPins_base {i : Fin D.R.m} (h : OMPins T R κ v₀ O i) : OMPins T (baseR R) κ v₀ (fun i => omBase (O i)) i := by
  have hP := h.2
  have h1 := hP.lift
  have h2 := hP.tuple
  refine ⟨h.1, ⟨h1.field, h1.std, h1.v0, ?_, h1.lev⟩,
    fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    hP.act, hP.bad, hP.reps, hP.ep, hP.io, hP.w, hP.cov, hP.cxi, hP.model₂⟩
  obtain ⟨g, c, c', h3, h4⟩ := h1.c0
  exact ⟨g, c, c', h3.comap (fun _ : Unit => A.μ0) (), h4⟩

set_option maxHeartbeats 4000000 in
theorem oneMapOf_base {i : Fin D.R.m} (cc ph) :
    (omBase (O i)).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph ↔ (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) cc ph := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem phaseTie_base {ph : Fin D.R.m → ℂ} {i : Fin D.R.m} (h : PhaseTie T R κ v₀ O ph i) :
    PhaseTie T (baseR R) κ v₀ (fun i => omBase (O i)) ph i :=
  fun ⟨cc, p, h'⟩ => (oneMapOf_base _ _).2 (h ⟨cc, p, (oneMapOf_base _ _).1 h'⟩)

set_option maxHeartbeats 4000000 in
theorem ext_base (j : Fin D.R.m) : TwConj.Ext T R κ v₀ O j (baseR R) v₀ (fun i => omBase (O i)) :=
  ⟨fun _ h => ⟨h.core, h.host, h.curve, h.split, h.chi⟩, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩


set_option maxHeartbeats 2000000 in
theorem restrict_to_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∃ (A0 : FamIn D.what₂.LL G Pl0 Unit D.R.m) (R0 : RealDat D A0 T.Q.c.F) (F0 : Face D A0)
      (v0 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R0.MW i σ).Vec) (O0 : ∀ i, OMDat T.toCore R0 i Unit (fun _ => A0.μ0)),
      GlobalTheory.BigOn.Exp.TwConj.Laws T R0 F0 κ v0 O0 ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R0 v0 O0 ∧ (∀ t, R0.xiH t = 1) ∧
      ∀ (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E)) (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
        GlobalTheory.BigOn.Exp.TwConj.TwLev R χ xi Q xiR → GlobalTheory.BigOn.Exp.TwConj.TwLev R0 χ xi Q xiR := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B h
  obtain ⟨h1, -, ⟨h3⟩, h4, h5, h6, h7, h8⟩ := h
  exact ⟨baseA A, baseR R, baseF F, v₀, fun i => omBase (O i),
    ⟨core_base h1, inferInstance, ⟨fwBase h3⟩, ioExt_base h4, qGuard_base h5, omPins_base h6, phaseTie_base h7, baseOf_base h8⟩,
    ext_base j, fun _ => h1.lev.xi_base, fun _ _ _ _ h => twLev_base h⟩

end GlobalTheory.BaseRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerModelComplexConjugateNegForm
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.ConjSchr

variable {D : D7}

theorem symplO_negS (S T : HSp D) (x y : WO S T) :
    symplO (GlobalTheory.ChiGrid.negSp S) T x y = -symplO S T x y := by
  simp only [symplO, hO, GlobalTheory.ChiGrid.negSp_gram, GlobalTheory.CjNeg.inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

def cjF {X : Type} (g : X → ℂ) : X → ℂ := fun w => starRingEnd ℂ (g w)

theorem heisO_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (x : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ S T x (cjF g) = cjF (heisO ψ (GlobalTheory.ChiGrid.negSp S) T x g) := by
  funext w
  simp only [cjF, heisO, map_mul, GlobalTheory.CjNeg.conj_psi hψ, GlobalTheory.CjNeg.symplOH_negS, neg_neg]

theorem cjF_cjF {X : Type} (g : X → ℂ) : cjF (cjF g) = g := by
  funext w; simp [cjF]

def conjLin {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun g := cjF (T (cjF g))
  map_add' g h := by
    have : cjF (g + h) = cjF g + cjF h := by funext w; simp [cjF]
    funext w; simp [this, cjF]
  map_smul' c g := by
    have : cjF (c • g) = starRingEnd ℂ c • cjF g := by funext w; simp [cjF]
    funext w; simp [this, cjF]

theorem conjLin_apply {X : Type} (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (g : X → ℂ) :
    conjLin T g = cjF (T (cjF g)) := rfl

theorem isSBHalf_cjF {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (cjF Φ) := by
  obtain ⟨hs, k, hk, hinv, hsupp⟩ := h
  refine ⟨fun t ht => hs t ?_, k, hk, fun u hu hue t => ?_, fun t ht => hsupp t ?_⟩
  · intro h0; apply ht; simp [cjF, h0]
  · simp only [cjF, hinv u hu hue t]
  · intro h0; apply ht; simp [cjF, h0]

theorem isPlaceModel_conjLin {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {e : AE D}
    {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO (GlobalTheory.ChiGrid.negSp S) T) (heisO ψ (GlobalTheory.ChiGrid.negSp S) T) e Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (cjF f₀) (conjLin T₀) := by
  constructor
  · intro Φ hΦ x hx
    have e1 := h.trans _ (isSBHalf_cjF hΦ) x hx
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => Φ (t + x)) = fun t => cjF Φ (t + x) := rfl
    rw [e2, e1]
  · intro Φ hΦ y hy
    have e1 := h.modul _ (isSBHalf_cjF hΦ) y hy
    rw [conjLin_apply, conjLin_apply, heisO_conj hψ]
    have e2 : cjF (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO (GlobalTheory.ChiGrid.negSp S) T t y) * cjF Φ t := by
      funext t; simp only [cjF, map_mul, GlobalTheory.CjNeg.conj_psi hψ, symplO_negS]
    rw [e2, e1]
  · have e2 : cjF ((1 : ℂ) • halfInd e Λ) = (1 : ℂ) • halfInd e Λ := by
      funext t; simp only [cjF, one_smul, halfInd]; split_ifs <;> simp
    rw [conjLin_apply, e2, h.vac]

end GlobalTheory.ConjSchr

open GlobalTheory.ConjSchr in
theorem GlobalTheory.ConjSchr.conj_schroedinger_neg : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A WW : HSp D) (e : AE D) (ΛA : Set (Fin A.rank → D.host.E))
  (ΛW : Set (Fin WW.rank → D.host.E)) (vac Φ f : WO A WW → ℂ),
  IsThetaAt ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO ψ (GlobalTheory.Grid.neg A) WW) e (latO (GlobalTheory.Grid.neg A) WW ΛA ΛW fun _ => True) 1 vac Φ f →
  ∃ Tm : (WO A WW → ℂ) →ₗ[ℂ] (WO A WW → ℂ),
    IsPlaceModel ψ (symplO A WW) (heisO ψ A WW) e (latO A WW ΛA ΛW fun _ => True) 1 (fun w => starRingEnd ℂ (vac w)) Tm ∧
      (fun w => starRingEnd ℂ (f w)) = Tm (fun w => starRingEnd ℂ (Φ w)) := by
  intro D ψ hψ A WW e ΛA ΛW vac Φ f hT
  have hL : latO (GlobalTheory.Grid.neg A) WW ΛA ΛW (fun _ => True) = latO A WW ΛA ΛW (fun _ => True) :=
    GlobalTheory.CoreRowLat.latO_negSp A WW ΛA ΛW _
  obtain ⟨⟨T₀, h0⟩, hall⟩ := hT
  have hf : f = T₀ Φ := hall T₀ h0
  rw [hL] at h0
  refine ⟨conjLin T₀, isPlaceModel_conjLin hψ h0, ?_⟩
  show cjF f = conjLin T₀ (cjF Φ)
  rw [conjLin_apply, cjF_cjF, hf]
end
end

