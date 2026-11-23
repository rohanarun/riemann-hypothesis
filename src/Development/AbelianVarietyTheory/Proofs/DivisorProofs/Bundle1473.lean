module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1431
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime genVal)

open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp resPt ptOf_resPt valR_ne_zero_iff LinSys)
open GlobalTheory.FlatLine (idem evR_idem idem_mem_suppOn)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Generic

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem asIdeal_spMap_closedPoint {A K : Type} [CommRing A] [Field K] (φ : A →+* K) :
    ((spMap φ (IsLocalRing.closedPoint K) : Sp A) : PrimeSpectrum A).asIdeal = RingHom.ker φ := by
  show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem specializes_ptY_genFr (h : GenFrEx Xo c) {L : Type} [Field L] [Algebra c.F L] (Q : FrPt Xo c L)
    (hQ : LiesOn Z Q) : ptOf (X.ptY (genFr h Z)) ⤳ ptOf (X.ptY Q) := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h L Q
  have hsp : ptOf (X.ptY (genFr h C.Z)) ⤳ ptOf (X.ptY Q) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [X.ptY_frBor C.bor, ← X.ptY_frMap C.gen, ← X.ptY_frBor hb, ← X.ptY_frMap hz, ptOf_comp, ptOf_comp]
    refine Specializes.map ?_ (X.ptY C.y).continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    show ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal ≤
      ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal
    rw [asIdeal_spMap_closedPoint, asIdeal_spMap_closedPoint]
    refine le_of_eq_of_le ((RingHom.injective_iff_ker_eq_bot _).1 ?_) bot_le
    exact Subtype.val_injective
  have hZ : C.Z = Z := by
    have h1 : ptOf (X.ptY Q) ∈ X.π ⁻¹ᵁ barComp Y Z := (le_iff_ptOf_mem _ _).1 ((ptY_le_iff X Z Q).2 hQ)
    have h2 := hsp.mem_open (Opens.isOpen _) h1
    have hl : LiesOn Z (genFr h C.Z) := (ptY_le_iff X Z _).1 ((le_iff_ptOf_mem _ _).2 h2)
    by_contra hne
    have h3 := GlobalTheory.AllWt.evC_eq_zero h hne (idem_mem_suppOn Z)
    rw [evC, evR_idem hl (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)] at h3
    exact one_ne_zero h3
  exact hZ ▸ hsp

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem exists_lift_genFr (h : GenFrEx Xo c) :
    ∃ z : Sp (Om Z) ⟶ M.X, z ≫ toFlag M = X.ptY (genFr h Z) ∧ ⊤ ≤ z ⁻¹ᵁ M.off := by
  have h1 : ⊤ ≤ X.ptY (genFr h Z) ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) := (ptY_le_iff X Z _).2 (GlobalTheory.AllWt.liesOn_genFr h Z)
  have hr : Set.range (X.ptY (genFr h Z)) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩; exact ⟨⟨_, h1 (Set.mem_univ s)⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY (genFr h Z) := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := fun s _ => by
    show (w ≫ inc₀ X Z) s ∈ flagOpen X
    rw [hw, ← X.pt_inc]
    exact (top_le_inc X) (Set.mem_univ _)
  obtain ⟨z, hz, -⟩ := M.existsUnique_lift w hU
  refine ⟨z, by rw [toFlag, ← Category.assoc, hz, hw], fun s _ => ?_⟩
  rw [M.off_eq]
  show (z ≫ M.σ) s ∈ U₀ X Z
  rw [hz]
  exact hU (Set.mem_univ s)

theorem isGenericPoint_of_lift (h : GenFrEx Xo c) {z : Sp (Om Z) ⟶ M.X} (hz : z ≫ toFlag M = X.ptY (genFr h Z))
    (hO : ⊤ ≤ z ⁻¹ᵁ M.off) : IsGenericPoint (ptOf z) Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← M.dense.closure_eq]
  refine closure_minimal (fun y hy => ?_) isClosed_closure
  refine specializes_iff_mem_closure.1 ?_
  have hy' : y ∈ M.opn := hy
  have hyU : M.σ y ∈ U₀ X Z := hy'
  have hF : toFlag M y ∈ flagOpen X := hyU
  have hY : toFlag M y ∈ X.π ⁻¹ᵁ barComp Y Z := (M.σ y).2
  have hO' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ flagOpen X := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hF
  obtain ⟨_, hch⟩ := exists_chartFr _ hO'
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
  have hk' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hk
  obtain ⟨Q, hQ⟩ := hch k hk'
  have e : resPt y ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  have hQZ : LiesOn Z Q := by
    refine (ptY_le_iff X Z Q).1 ((le_iff_ptOf_mem _ _).2 ?_)
    rw [← e, ptOf_comp, ptOf_resPt]
    exact hY
  have sp := specializes_ptY_genFr X Z h Q hQZ
  rw [← hz, ← e, ptOf_comp, ptOf_comp, ptOf_resPt] at sp
  have : IsOpenImmersion (M.opn.ι ≫ M.σ) := by
    rw [← morphismRestrict_ι]
    have := M.iso
    infer_instance
  have hg : IsOpenImmersion (M.opn.ι ≫ toFlag M) := by
    rw [toFlag, ← Category.assoc]
    infer_instance
  have hz' : ptOf z ∈ M.opn := by
    have := (le_iff_ptOf_mem _ _).1 hO
    rwa [M.off_eq] at this
  have sp' : (⟨ptOf z, hz'⟩ : M.opn) ⤳ ⟨y, hy'⟩ :=
    (M.opn.ι ≫ toFlag M).isOpenEmbedding.isInducing.specializes_iff.1 sp
  exact sp'.map continuous_subtype_val

end Generic

section Coords

variable {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem val_restr' {k : Type} [CommRing k] {T : Scheme.{0}} {p : T ⟶ Sp k} {B : LB T} {O O' : T.Opens} (h : O' ≤ O)
    {A : Type} [CommRing A] (x : Sp A ⟶ T) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem valR_eq_evalPt {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) (O : T.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (f : Γ(T, O)) : valR x O f = evalPt x O h f := dif_pos h

theorem chartFr_congr {S : Type} [CommRing S] [Algebra c.F S] {k : X.F.J} {z z' : Sp S ⟶ X.YY} (e : z = z')
    {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} {hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k} {Q : FrPt Xo c S} (h : X.F.ChartFr k z hz Q) :
    X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem exists_chart_val (h : GenFrEx Xo c) {P : WtPar Dw} (R : Choice X Z U P) (hfree : FreeOnOpen X Z U P.u₁)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R.toModif = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : R.L.ι) (a : Om Z), ptOf z ∈ R.L.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U P.u₁) (w : space X Z U P.u₁),
      restr le_top w.1 = cuspSec X Z U P.u₁ g →
      valR z (R.L.U i) ((toSec (R.Δ₁.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z P.u₁).pull R.σ).U (flagIdx R.toModif P.u₁ k) := (R.com.mem _ _ _).2 hk
  have hi : ptOf z ∈ R.L.U (flagIdx R.toModif P.u₁ k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (R.Δ₁.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen R.Δ₁.t hn).1 ((R.Δ₁.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw P.u₁ 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R.toModif P.u₁ k, n), (valR z _ (R.Δ₁.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (R.L.U (flagIdx R.toModif P.u₁ k, n)) ((toSec (R.Δ₁.lift w)).f (flagIdx R.toModif P.u₁ k, n)) =
      H0.val z _ hTop hi' (R.Δ₁.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R.toModif P.u₁ k, n) hTop hi' (toSec (R.Δ₁.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z P.u₁) R.σ) R.Δ₁.isLB).val_mul (ofSec R.str ⊤ R.Δ₁.t) (R.Δ₁.lift w)
    (flagIdx R.toModif P.u₁ k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U P.u₁ g) = H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ R.Δ₁.t) = valR z _ (R.Δ₁.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← R.Δ₁.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (R.Δ₁.incl ⊤ (R.Δ₁.lift w)) = valR z _ (R.Δ₁.t.f n) * H0.val z _ hTop hi' (R.Δ₁.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

end Coords

theorem compPresents_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), GlobalTheory.CompHt.CompPresents U x V dict Z (GlobalTheory.AllWt.wtOf Dw P.u₁ 0) (h.data f₁ f₂ th k).toHermSys := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  refine ⟨(dimFlag_eq Dw).symm, f₁.b, f₁.isFrame, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr R.toModif hG
  have hgen := isGenericPoint_of_lift R.toModif hG hz hO
  have hV := (R.isAlgebraicData R.Δ₁ h.ext₁.equiv f₁ (dense_U₀ X Z) h.conn h.one_le k.abelian₂).variety
  have : IsIntegral (h.data f₁ f₂ th k).toHermSys.toLinSys.Y := hV.isIntegral
  have hstr : z ≫ (h.data f₁ f₂ th k).toHermSys.toLinSys.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag R.toModif ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG R h.free₁ hz hO
  obtain ⟨b, hb, hb', -⟩ := (h.data f₁ f₂ th k).toHermSys.toLinSys.exists_frame_change z i hi
  refine GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic c.F (Om Z) _ ⟨z, hstr⟩ hgen (b⁻¹ * a) _
    (mul_ne_zero (inv_ne_zero hb) ha) (funext fun j => ?_)
  have e₁ := hb' ((h.data f₁ f₂ th k).toHermSys.toLinSys.b j)
  have e₂ := hv (f₁.b j) (h.ext₁.equiv (f₁.b j)) (h.ext₁.restr_equiv _)
  have e₃ := e₁.symm.trans e₂
  show (h.data f₁ f₂ th k).toHermSys.toLinSys.val z _ = (b⁻¹ * a) * genVal Z (f₁.b j).1
  rw [mul_assoc, ← e₃, inv_mul_cancel_left₀ hb]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSections
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BertiniTop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem bertini : Quoted → Bertini := by
  intro hq F _ _ T hG hB δ f hf
  obtain ⟨-, hdeg, hdim⟩ :=
    GlobalTheory.ImageDegree.degree_image_eq_topSelf hq F T.toLinSys hG.alg.variety hG.alg.bpf hB
  have hprime : T.imageIdeal.IsPrime := HeightExists.isPrime_imageIdeal (S := T.toLinSys) hG.alg.variety
  have hhom : ∀ a ∈ T.imageIdeal, ∀ n : ℕ, homogeneousComponent n a ∈ T.imageIdeal := by
    intro a ha n
    have h := T.toLinSys.isHomogeneous_imageIdeal n ha
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin T.N) F) a n : MvPolynomial (Fin T.N) F) =
      homogeneousComponent n a from MvPolynomial.decomposition.decompose'_apply a n] at h
  have hδ : (δ : ℤ) = T.del := by
    rw [GlobalTheory.ChowDegree.degree_eq_hilbertDegree_of_isChowForm F T.D T.N δ T.imageIdeal f hf hprime hhom]
    exact hdeg
  refine ⟨hδ, ?_⟩
  obtain ⟨d₁, g₁, hg₁, hg₁I, hg₁v⟩ := _root_.GlobalTheory.BoundaryForm.exists_form_vanishing F T hG hB
  obtain ⟨d₂, g₂, hg₂, hg₂I, hg₂f⟩ := _root_.GlobalTheory.BirFiniteFibre.exists_form_finite_fibres F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨Q₁, hQ₁, hQ₁v⟩ := _root_.GlobalTheory.HSShort.exists_elim_form_of_field F T.D T.N (d₁ + d₂) T.imageIdeal (g₁ * g₂) hG.alg.variety.one_le hprime hhom
    hdim (hg₁.mul hg₂) fun h => (hprime.mem_or_mem h).elim hg₁I hg₂I
  obtain ⟨Q₂, hQ₂, -, hQ₂n⟩ :=
    GlobalTheory.PencilDisc.exists_poly_noSquare F T.D T.N δ f hf.isChowFormInt.pos hf.homog hf.irred
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun E _ _ s hs => ?_⟩
  have hs' : aeval (fun p : Fin T.D × Fin T.N => algebraMap E (AlgebraicClosure E) (s p.1 p.2)) (Q₁ * Q₂) ≠ 0 := by
    have h := MvPolynomial.aeval_algebraMap_apply (AlgebraicClosure E)
      (fun p : Fin T.D × Fin T.N => s p.1 p.2) (Q₁ * Q₂)
    exact fun h0 => hs ((map_eq_zero (algebraMap E (AlgebraicClosure E))).1 (h.symm.trans h0))
  rw [map_mul] at hs'
  have hns : NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) :=
    hQ₂n _ _ (right_ne_zero_of_mul hs')
  obtain ⟨hfin, hopen⟩ := _root_.GlobalTheory.HSShort.Supp.finite_and_inOpen F T hG δ f hf (g₁ * g₂)
    (fun K _ _ x hx => by rw [map_mul, hg₁v K x hx, zero_mul])
    (fun K _ _ y => (hg₂f K y).subset fun x hx => ⟨right_ne_zero_of_mul (by simpa only [map_mul] using hx.1), hx.2⟩)
    E s hns.1 fun x hx h0 => by
      refine left_ne_zero_of_mul hs' (hQ₁v (AlgebraicClosure E) (fun i j => algebraMap E _ (s i j)) _
        (hG.alg.bpf.coords_ne_zero _) (fun a ha => ?_) h0 ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx))
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 ha
      rwa [LinSys.baseHom_ptOver] at this
  exact _root_.GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare F T hG δ f hf hδ E s hfin hopen hns

end GlobalTheory.BertiniTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAll
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodCpt

theorem pow_mem_of_mem {K : Type} [Field K] (O : Subring K) {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, M i j ∈ O) : ∀ k : ℕ, ∀ i j, (M ^ k) i j ∈ O := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp [O.one_mem, O.zero_mem]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact O.sum_mem fun m _ => O.mul_mem (ih i m) (hM m j)

theorem gram_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin n => ((g.map f) ^ ((i : ℕ) + j)).trace) =
      (Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace).map f := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← Matrix.map_pow, Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  intro E _ _ _ hU n γ hs
  set g : Matrix (Fin n) (Fin n) E := γ.1.val with hgdef
  set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j : Fin n => (g ^ ((i : ℕ) + j)).trace with hGdef
  have hd : G.det ≠ 0 := GlobalTheory.T.det_trace_pow_matrix_ne_zero_of_separable g hs
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E (g i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    exact fun i j => GlobalTheory.LocRatPt.eventually_valuation_le_one _
  filter_upwards [h1, GlobalTheory.LocRatPt.eventually_valuation_le_one (E := E) G.det⁻¹] with w hg hdi
  set f : E →+* w.adicCompletion E := algebraMap E (w.adicCompletion E)
  set gw : Matrix (Fin n) (Fin n) (w.adicCompletion E) := g.map f with hgw
  have hgwO : ∀ i j, gw i j ∈ Ov E w := fun i j => GlobalTheory.LocRatPt.algebraMap_mem_Ov (hg i j)
  have hsep : gw.charpoly.Separable := by rw [hgw, Matrix.charpoly_map]; exact hs.map
  have hGw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace) = G.map f := gram_map f g
  have hdet : (G.map f).det = f G.det := (RingHom.map_det f G).symm
  have hdw : (Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det ≠ 0 := by
    rw [hGw, hdet]; exact (map_ne_zero f).2 hd
  have hdwi : ((Matrix.of fun i j : Fin n => (gw ^ ((i : ℕ) + j)).trace).det)⁻¹ ∈ Ov E w := by
    rw [hGw, hdet, ← map_inv₀]; exact GlobalTheory.LocRatPt.algebraMap_mem_Ov hdi
  have hloc : (locPt w γ).1.1 = gw := by rw [GlobalTheory.LocRatPt.locPt_val hU]; rfl
  have key : ∀ s : UL n w, s * locPt w γ = locPt w γ * s →
      (∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ k : ℤ, ∀ i j, a * (s ^ k).1.1 i j ∈ Ov E w) →
      ∀ i j, s.1.1 i j ∈ Ov E w := by
    rintro s hs' ⟨a, ha, hb⟩
    set x : Matrix (Fin n) (Fin n) (w.adicCompletion E) := s.1.1 with hx
    have hxc : x * gw = gw * x := by
      have := congrArg (fun u : UL n w => u.1.1) hs'
      simpa [hloc] using this
    have hpow : ∀ k : ℕ, (s ^ (k : ℤ)).1.1 = x ^ k := by
      intro k; rw [zpow_natCast]; simp [hx]
    obtain ⟨c, hcx⟩ := _root_.GlobalTheory.SepCommutant.exists_eq_sum_pow_of_commute gw x hsep hxc
    refine _root_.GlobalTheory.TraceGram.entry_mem_of_trace_gram (Ov E w) gw x c hcx hgwO (fun j => ?_) hdw hdwi
    refine _root_.GlobalTheory.trace_mem_of_pow_bdd E w n _ a ha fun k i l => ?_
    have hcm : Commute x (gw ^ (j : ℕ)) := (Commute.pow_right hxc (j : ℕ))
    rw [hcm.mul_pow, ← pow_mul, Matrix.mul_apply, Finset.mul_sum]
    refine (Ov E w).sum_mem fun m _ => ?_
    rw [← mul_assoc, ← hpow]
    exact (Ov E w).mul_mem (hb _ i m) (pow_mem_of_mem _ gw hgwO _ m l)
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, hc⟩
  have ht' : t * locPt w γ = locPt w γ * t := ht
  obtain ⟨a, ha, hb⟩ := _root_.GlobalTheory.BddCpt.bdd_entries_of_isCompact_closure_zpowers E n w t hc
  have e1 := key t ht' ⟨a, ha, hb⟩
  have e2 := key t⁻¹ ((show Commute t (locPt w γ) from ht').inv_left).eq
    ⟨a, ha, fun k i j => by rw [_root_.inv_zpow']; exact hb (-k) i j⟩
  rw [SetLike.mem_coe, KL, Subgroup.mem_subgroupOf]
  exact GlobalTheory.LocRatPt.mem_GLint_of_entries e1 (fun i j => by simpa using e2 i j)

end GlobalTheory.BCT.GoodCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactStandardParabolicUnipotentRadicalWittFr
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

noncomputable section
namespace GlobalTheory.CuspCocpt
open GlobalTheory.StdPar GlobalTheory.Cusp

theorem cocompact_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ S : Finset (Fin r), GlobalTheory.Cusp.Cocompact (ratPts σ J) (GlobalTheory.StdPar.unip σ J X S) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S
  by_cases hS0 : S = ∅
  · subst hS0
    rw [unip_empty]
    refine ⟨Set.univ, ?_, fun u => ⟨1, Subgroup.one_mem _, Set.mem_univ _⟩⟩
    exact Set.Subsingleton.isCompact fun a _ b _ => Subsingleton.elim a b
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  have hσ := sigma_sigma h
  have hs : m.val + 1 ≤ r := m.2
  have hS : ∀ i : Fin r, i.val < m.val + 1 ↔ ∃ k ∈ S, i ≤ k := fun i =>
    ⟨fun hi => ⟨m, hm, Fin.le_def.2 (Nat.lt_succ_iff.1 hi)⟩,
      fun ⟨k, hk, hik⟩ => Nat.lt_succ_iff.2 (le_trans (Fin.le_def.1 hik) (Fin.le_def.1 (hm' k hk)))⟩
  have e := (GlobalTheory.TieStd.stdPar_eq_flag F E σ h n J hJ r X Y hW S (m.val + 1) hs hS
    (fun i => (S.filter (· < Fin.castLE hs i)).card) fun _ => rfl).1
  have hC : IsIsoCols σ J (X.submatrix id (Fin.castLE hs)) := isIsoCols_of_isWittFrame hW hσ hJ hs
  exact e ▸ cocompact_unipFlag hJ hσ hC _

end GlobalTheory.CuspCocpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformSchwartzCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.ThetaTrContF

theorem continuous_thetaTrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc

end GlobalTheory.ThetaTrContF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_differential_kernel_zero_germs : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  first | (exact @GlobalTheory.KerGermInj.eq_zero) | (exact GlobalTheory.KerGermInj.eq_zero) | (intros; apply GlobalTheory.KerGermInj.eq_zero  <;> assumption)
end

