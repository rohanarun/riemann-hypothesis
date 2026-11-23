module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstVariableSupportFiniteCellsAtTwistPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QFinSupp

theorem locK_congr {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle} (Q : QAt v χ) (j d d' : ℕ) (e : d = d')
    (h1 : j + d = Q.s + 1) (h2 : j + d' = Q.s + 1) :
    (Q.T.lev j d h1).J.map (Q.gl j d h1) = (Q.T.lev j d' h2).J.map (Q.gl j d' h2) := by
  subst e; rfl

theorem cells_at : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r) (a : GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∃ T : Finset (GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k), ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ g ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v), ∀ h₁ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v), ∀ x, flatBF (t.sBF j (σ + 1) h) (t.om j (g * (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a, h₁ * (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ τ ∈ T, ∃ r, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) r ∈ jacGrp (c.jac j (σ + 1) h).d ∧ ∃ κ ∈ ((F.Q i).T.lev (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega)).J, x = r * τ * κ := by
  intro D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨T, hT⟩ := GlobalTheory.T.seeSaw_twistPlace_finitely_many_cells D c v t w F hc ht hv hW hF j σ h i a
  refine ⟨T, fun Ψ₁ hΨ g hg h₁ hh x hne => ?_⟩
  obtain ⟨f₁, hf₁, e⟩ := _root_.GlobalTheory.TwistPlaceSplit.main D c v t w F hc hv hF j (by omega) i Ψ₁ hΨ
  rw [e] at hne
  exact hT f₁ hf₁ g hg h₁ hh x hne

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ T₁ : Finset (GA D (c.V (j + 1))), (∀ q ∈ T₁, q ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ Ψ₁, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → ∀ α, ∀ g ∈ (w.ε j α).support, ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h) (t.om j (g, x) (comb c.ψ _ _ (w.eQ j) Ψ₁)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q) ∧ ∃ q ∈ T₁, ∃ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, x = r * q * k := by
  intro D c v t w F hc ht hv hW hF j σ h
  classical
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_finite_local_support_exchangeData_twistPlaces D c v t w F hF j σ h
  choose T hT using fun i a => cells_at D c v t w F hc ht hv hW hF j σ h i a
  obtain ⟨P, hPH, hPat, hPdec⟩ := GlobalTheory.T.twistPlaces_group_eq_product_local_groups D c v t w F hF j σ h
  refine ⟨(Fintype.piFinset fun i => (A i).biUnion (T i)).image P, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    exact hPat y
  · intro Ψ₁ hΨ α g hg x hx hne
    obtain ⟨a, ha⟩ := hA α g hg
    obtain ⟨y, rfl, hy⟩ := hPdec x hx
    have key := fun i => hT i (a i) Ψ₁ hΨ _ (ha i).2 _ (hy i) (y i) (by simpa only [inv_mul_cancel_right] using hne)
    choose τ hτ r hr κ hκ hyeq using key
    have hyy : y = r * τ * κ := funext hyeq
    refine ⟨P r, hPH _ r hr, hPat r, P τ, Finset.mem_image.2 ⟨τ, Fintype.mem_piFinset.2 fun i =>
      Finset.mem_biUnion.2 ⟨a i, (ha i).1, hτ i⟩, rfl⟩, P κ, hPH _ κ fun i => ?_, by rw [hyy, map_mul, map_mul]⟩
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [GlobalTheory.QuotientFiniteLevel.locK, locK_congr (F.Q i) (j + 1) _ (2 * σ + 2) (by have := (F.Q i).hs; omega) _ (by have := (F.Q i).hs; omega)]
    exact Subgroup.mem_map_of_mem _ (hκ i)

end GlobalTheory.QFinSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormKeepsAdelicLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.TransLaw

theorem trc_apply' {D : D7} {V : HSp D} (c : GA D V →₀ ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc c f x = ∑ g ∈ c.support, c g * f (x * g) := by
  simp [trc, rTrans, Finset.sum_apply]

theorem list_prod_right {G : Type} [Group G] (F : G → ℂ) (L : List G) (hL : ∀ a ∈ L, ∀ z, F (z * a) = F z) (z : G) :
    F (z * L.prod) = F z := by
  induction L generalizing z with
  | nil => simp
  | cons a L ih =>
    rw [List.prod_cons, ← mul_assoc, ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (z * a), hL a List.mem_cons_self]

theorem list_prod_chi {G : Type} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (L : List G)
    (hL : ∀ a ∈ L, ∃ h : a ∈ U, χ ⟨a, h⟩ = 1) : ∃ h : L.prod ∈ U, χ ⟨_, h⟩ = 1 := by
  induction L with
  | nil => exact ⟨U.one_mem, χ.map_one⟩
  | cons a L ih =>
    obtain ⟨ha, hχa⟩ := hL a List.mem_cons_self
    obtain ⟨hP, hχP⟩ := ih (fun b hb => hL b (List.mem_cons_of_mem _ hb))
    refine ⟨by rw [List.prod_cons]; exact U.mul_mem ha hP, ?_⟩
    have e : (⟨(a :: L).prod, by rw [List.prod_cons]; exact U.mul_mem ha hP⟩ : U) = ⟨a, ha⟩ * ⟨L.prod, hP⟩ := by
      apply Subtype.ext; simp [List.prod_cons]
    rw [e, map_mul, hχa, hχP, one_mul]

set_option maxHeartbeats 1000000 in
theorem rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is) (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ)
    (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j) (b : Ch j) (y : (I.chain l u a).Y j) :
    (∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ g, A.rd θ j hj b φ y (γ * g) = A.rd θ j hj b φ y g) ∧
    (∀ κ : A.U j b, ∀ g, A.rd θ j hj b φ y (g * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y g) ∧
    (∀ k ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ y' : (I.chain l u a).Y j,
      IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
      ∀ g, A.rd θ j hj b φ y (g * k) = A.rd θ j hj b φ y' g) := by
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY
    ⟨A.kb j, hA.reads j hj⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨hL, hK, hR, -⟩ := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj b).lev {c // A.chOf j c = b}
      (A.K j hj b).y (A.K j hj b).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF b) ⟨y.1, y.2⟩
  refine ⟨fun γ hγ g => hL γ hγ g, fun κ g => ?_, fun k hk y' hy g => hR k hk ⟨y'.1, y'.2⟩ hy g⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U j hj b κ.1).1 κ.2
  rw [hA.chi j hj b κ κ' hκ']
  exact hK κ.1 hκf κ' hκ' g

end GlobalTheory.AdForm.TransLaw


open GlobalTheory.AdForm.TransLaw in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.AdForm.trc_rd_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ b y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X j), ∀ (e : {e // A.chOf j e = b}), ∀ g ∈ GinfC ((I.rec7 l Z).sp.X j), ∀ (κ : A.U j b) (y' : (I.chain l u a).Y j),
        IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) g) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ →
        trc c (A.rd θ j hj b φ y) (γ * (A.h j b e * g) * κ.1) = (A.chi j b κ : ℂ) * trc c (A.rd θ j hj b φ y') (A.h j b e) := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ K _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv b y γ hγ e g0 hg0 κ y' hy
  obtain ⟨hLy, hKy, hRy⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y
  have hT' := hT
  obtain ⟨⟨eι, -⟩, -⟩ := hT'
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  obtain ⟨hstab, hdec⟩ := _root_.GlobalTheory.AdForm.twLev_prime I hok hpins l Z u a Ch A hA K ι p β Q L hT Finset.univ.toList
    (Finset.nodup_toList _) (fun i => Finset.mem_toList.2 (Finset.mem_univ _)) j hj b
  obtain ⟨gs, hgs, κ', hκ'off, hκeq⟩ := hdec κ.1 κ.2
  set s := (Finset.univ.toList.map fun i => (β j i).gl (gs i)).prod with hs
  obtain ⟨hsU, hχs⟩ := list_prod_chi (A.U j b) (A.chi j b) (Finset.univ.toList.map fun i => (β j i).gl (gs i)) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab i (gs i) (hgs i))
  have hκ'U : κ' ∈ A.U j b := by
    have : κ' = s⁻¹ * κ.1 := by rw [hκeq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]; exact (A.U j b).mul_mem ((A.U j b).inv_mem hsU) κ.2
  have hχκ : A.chi j b κ = A.chi j b ⟨κ', hκ'U⟩ := by
    have e1 : κ = (⟨s, hsU⟩ : A.U j b) * ⟨κ', hκ'U⟩ := Subtype.ext hκeq
    rw [e1, map_mul, hχs, one_mul]
  set F := trc c (A.rd θ j hj b φ y) with hF

  have hcomm : ∀ g' ∈ c.support, κ' * g' = g' * κ' := fun g' hg' =>
    ((GlobalTheory.FinPlLoc.part_grp (fun x => ∃ i, x = (p i).v) ((I.rec7 l Z).sp.X j)).2.1 g' (hc g' hg') κ' hκ'off).symm

  have step1 : ∀ x, F (x * κ.1) = (A.chi j b κ : ℂ) * F (x * s) := by
    intro x
    rw [hF, trc_apply', trc_apply', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g' hg' => ?_
    rw [hκeq, ← mul_assoc, mul_assoc (x * s), hcomm g' hg', ← mul_assoc, hKy ⟨κ', hκ'U⟩, hχκ]
    ring

  have step2 : ∀ x, F (x * s) = F x := by
    intro x
    refine list_prod_right F _ ?_ x
    intro a' ha' z
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha'
    exact congrFun (hinv b y i (gs i) (hgs i)) z

  have step3 : F (γ * (A.h j b e * g0)) = trc c (A.rd θ j hj b φ y') (A.h j b e) := by
    rw [hF, trc_apply', trc_apply']
    refine Finset.sum_congr rfl fun g' hg' => ?_
    have hfin : g' ∈ GfC ((I.rec7 l Z).sp.X j) := GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hc g' hg')
    rw [mul_assoc γ, hLy γ hγ, mul_assoc, ← GlobalTheory.FinTranslate.comm_fin_real _ hfin hg0, ← mul_assoc,
      hRy g0 hg0 y' hy]
  rw [step1, step2, step3]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesMemWeylModule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TransAct


set_option maxHeartbeats 1000000 in
theorem trc_val_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ e : (I.stp u a j).Cl, (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e ∈ ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj c hc φ hφ hinv e
  have hR := (_root_.GlobalTheory.ChartReps.twDat_reps I hI hP l Z u a Ch A hA j hj (A.chOf j e)).1
  have key : ∀ g, (fun z : (I.chain l u a).Y j =>
      A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) ∈
      ValC (Gr B.fields.emb B.embLL (B.R.N j)) (Col2.lamT (B.hcW u) j) := by
    intro g
    obtain ⟨γ, hγ, e', g', hg', κ, hκ, hdec⟩ := hR.dec (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)
    let U : (I.rec7 l Z).what₂.Tau → GL (Fin (B.R.N j)) ℂ := fun τ =>
      ((Matrix.isUnit_iff_isUnit_det _).2 (RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) g' τ)).unit
    have hfun : (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) =
        (A.chi j (A.chOf j e) ⟨κ, hκ⟩ : ℂ) • GlobalTheory.Mem.ColAd.lT (Gr B.fields.emb B.embLL (B.R.N j)) U (φ e'.1) := by
      funext z
      rw [hdec]
      exact (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j e) z γ hγ e' g' hg' ⟨κ, hκ⟩
        (GlobalTheory.Mem.ColAd.frL (Gr B.fields.emb B.embLL (B.R.N j)) U z) (fun τ => rfl)
    rw [hfun]
    exact Submodule.smul_mem _ _ (GlobalTheory.Mem.ColAd.lT_mem _ _ U (hφ e'.1).1)
  have hsum : (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) =>
      trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e =
      ∑ g ∈ c.support, c g • (fun z : (I.chain l u a).Y j =>
        A.rd θ j hj (A.chOf j e) φ z (A.h j (A.chOf j e) ⟨e, rfl⟩ * g)) := by
    funext z
    simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (key g)

end GlobalTheory.AdForm.TransAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCombinationScalarFormValuesStabilizerInvariant
section
namespace GlobalTheory.AdForm.StabTrans
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Col2.BwLat GlobalTheory.LvT.Built.ValLat Formalism.HermitianLatticesTheory GlobalTheory.Mem.Col2.ValTie

theorem chi_stab {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch)
    (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
      (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (k : Ch → GA B (B.R.N i))
    (hR : I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
      (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k)
    (c : (I.stp u a i).Cl) (s : (I.stp u a i).Stab c) (κ : (K (chOf c)).lev.U)
    (hy : (fun g y x : GA B (B.R.N i) => y = g * y * x) (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
          ((I.stp u a i).gam c.1 s.1)) ((K (chOf c)).y ⟨c, rfl⟩).1 κ.1) :
    ((K (chOf c)).lev.chi κ : ℂ) = B.embLL ((I.stp u a i).chr c.1 s.1 : B.LLˣ) := by
  have h0 := (hR.pt c).of_extTo (I.Q_subset_SQ a) ((LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a))
  have h1 := RatMove.isPtOf_ratAd _ _ B.sp.cm _ _ _ _ s.1.1⁻¹ _ _ h0
  have h2 := lev_part_smul _ _ s.1 ((I.stp u a i).rep c).1.1 (congrArg (fun q => q.1.1) s.2)
  have h3 : ∀ g y x k : GA B (B.R.N i), y = g * y * x → g⁻¹ * (y * k) = y * x * k := fun g y x k h => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
  have h4 : ratAd B.host.F (s.1.1⁻¹) = (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
      ((I.stp u a i).gam c.1 s.1))⁻¹ := by
    rw [ratAd, map_inv, map_inv]
    rfl
  rw [h4, h3 _ _ _ _ hy, ← h2] at h1
  exact hR.chr c κ (1, s.1.2) (map_one (_root_.Formalism.L2.Col.ufGL B.fields.E (B.R.N i))) h1

end GlobalTheory.AdForm.StabTrans

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.KJInf
open scoped TensorProduct Pointwise
open GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StabTrans
open Formalism.L2.Theta

theorem finM_mul' {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem rTrans_mul {G : Type} [Monoid G] (a b : G) (F : G → ℂ) : rTrans (a * b) F = rTrans a (rTrans b F) := by
  funext x
  simp only [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans (1 : G) F = F := by
  funext x
  simp only [rTrans, mul_one]

theorem rTrans_list_prod {G α : Type} [Monoid G] (f : α → G) (F : G → ℂ) (h : ∀ i, rTrans (f i) F = F) :
    ∀ L : List α, rTrans (L.map f).prod F = F
  | [] => by simpa using rTrans_one F
  | i :: L => by
    rw [List.map_cons, List.prod_cons, rTrans_mul, rTrans_list_prod f F h L, h i]

end GlobalTheory.AdForm.StabTrans


set_option maxHeartbeats 12000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.AdForm.trans_stab : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (c : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →₀ ℂ),
      (∀ g ∈ c.support, g ∈ grpAt _ fun x => ∃ i, x = (p i).v) → ∀ φ ∈ (I.fm l u a).Fi j,
      (∀ b y i g, g • Q j i = Q j i → rTrans ((β j i).gl g) (trc c (A.rd θ j hj b φ y)) = trc c (A.rd θ j hj b φ y)) →
      ∀ (e : (I.stp u a j).Cl) (s : (I.stp u a j).Stab e), (I.stp u a j).tr B.fields.emb B.embLL e.1 s.1 ((fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e) = (fun (e : (I.stp u a j).Cl) (z : (I.chain l u a).Y j) => trc c (A.rd θ j hj (A.chOf j e) φ z) (A.h j (A.chOf j e) ⟨e, rfl⟩)) e := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj c hc φ hφ hinv e s
  let eY : (I.chain l u a).Y j ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) j hj :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hR := hA.reads j hj
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a j hj (A.bad j) (Ch j) (A.chOf j) (A.K j hj) eY ⟨A.kb j, hR⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  obtain ⟨Ψ, hΨ, he⟩ := Submodule.mem_map.1 (hF (A.chOf j e))
  have hAd : Ψ ∈ AdFun (A.K j hj (A.chOf j e)).lev (embT (I.rec7 l Z)) := (Submodule.mem_inf.1 hΨ).1
  have hfun : (fun (c : {c // A.chOf j c = A.chOf j e}) (z : Frames (gramC (gramN (I.rec7 l Z) j hj) (embT (I.rec7 l Z)))) =>
      φ c.1 ⟨z.1, z.2⟩) = fun c => Ψ ((A.K j hj (A.chOf j e)).y c) := he.symm
  have rdΨ : ∀ (w : (I.chain l u a).Y j) (g0 : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), g0 ∈ GfC _ →
      ∀ x : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hj) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F),
      x.1.1 = finM _ (rankN (I.rec7 l Z) j hj) g0 →
      A.rd θ j hj (A.chOf j e) φ w g0 = Ψ x ⟨w.1, w.2⟩ := by
    intro w g0 hg0 x hx
    have hval := (GlobalTheory.AdForm.rdS_val (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X j) (B.R.N j) (rankN (I.rec7 l Z) j hj)
      (gramN (I.rec7 l Z) j hj) rfl (B.T u) (I.rec7 l Z).R.f (A.bad j) (A.K j hj (A.chOf j e)).lev _
      (A.K j hj (A.chOf j e)).y (A.K j hj (A.chOf j e)).y_bij Ψ hAd ⟨w.1, w.2⟩ g0).2.2 x ⟨w.1, w.2⟩ hx (fun τ => by
        have h1 := GlobalTheory.AdForm.ChartVal.infM_fin' θ _ (rankN (I.rec7 l Z) j hj) g0 hg0 τ
        show w.1 τ = infM θ _ _ g0 τ * w.1 τ
        erw [h1, Matrix.one_mul])
    show rdS θ _ (rankN (I.rec7 l Z) j hj) (A.K j hj (A.chOf j e)).lev (A.K j hj (A.chOf j e)).y
      (fun c z => φ c.1 ⟨z.1, z.2⟩) ⟨w.1, w.2⟩ g0 = _
    rw [hfun]
    exact hval
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = Formalism.L2.Col.embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  refine ((GlobalTheory.Mem.Col2.ValTie.stab_inv_iff (E := B.host.E) (F := B.host.F) (sg := sigD (I.rec7 l Z)) (J := gramN (I.rec7 l Z) j hj) (I.stp u a j) B.fields.emb B.embLL e (A.K j hj (A.chOf j e)).lev hemb
    ((A.K j hj (A.chOf j e)).y ⟨e, rfl⟩).1 ((A.K j hj (A.chOf j e)).stabI ⟨e, rfl⟩) (hR.stab e)
    ((A.K j hj (A.chOf j e)).stabI_range ⟨e, rfl⟩)
    (GlobalTheory.AdForm.StabTrans.chi_stab I hI l Z u a j hj (A.chOf j) (A.K j hj) (A.kb j) hR e)
    _ (fun z => ⟨z.1, z.2⟩) (fun _ => rfl)).2 ?_) s
  intro γ hγ κ hy z z' hz

  clear hF hV he hΨ
  obtain ⟨⟨eι, -⟩, -⟩ := id hT
  haveI : Fintype ι := Fintype.ofEquiv _ eι.symm
  classical
  have hJnd : (Finset.univ : Finset ι).toList.Nodup := Finset.nodup_toList _
  have hJall : ∀ i, i ∈ (Finset.univ : Finset ι).toList := fun i => Finset.mem_toList.2 (Finset.mem_univ i)
  obtain ⟨hlev1, hlev2⟩ := _root_.GlobalTheory.AdForm.twLev_prime I hI hP l Z u a Ch A hA k ι p β Q L hT _ hJnd hJall j hj (A.chOf j e)
  obtain ⟨kA, hkAf, hkAe⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)
    ⟨κ.1, (((A.K j hj (A.chOf j e)).lev.U_eq κ.1).1 κ.2).1⟩
  have hkAU : kA ∈ A.U j (A.chOf j e) := (hA.U j hj _ kA).2 ⟨hkAf, κ, hkAe.symm⟩
  obtain ⟨g, hg, κ', hκ'off, hdec⟩ := hlev2 kA hkAU
  have hPK : ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod ∈
      (A.chi j (A.chOf j e)).ker.map (A.U j (A.chOf j e)).subtype := by
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨h, h1⟩ := hlev1 i (g i) (hg i)
    exact ⟨⟨_, h⟩, h1, rfl⟩
  obtain ⟨P0, hP0chi, hP0e⟩ := Subgroup.mem_map.1 hPK
  rw [MonoidHom.mem_ker] at hP0chi
  set P := ((Finset.univ : Finset ι).toList.map fun i => (β j i).gl (g i)).prod with hPdef
  have hP0e' : P0.1 = P := hP0e
  have hκ'U : κ' ∈ A.U j (A.chOf j e) := by
    have : κ' = P0.1⁻¹ * kA := by rw [hdec, hP0e']; group
    rw [this]
    exact mul_mem (inv_mem P0.2) hkAU
  obtain ⟨κ'', hκ''⟩ := ((hA.U j hj _ κ').1 hκ'U).2
  have hchi : ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) = ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) := by
    rw [← hA.chi j hj _ ⟨kA, hkAU⟩ κ hkAe.symm, ← hA.chi j hj _ ⟨κ', hκ'U⟩ κ'' hκ'']
    have e1 : (⟨kA, hkAU⟩ : A.U j (A.chOf j e)) = P0 * ⟨κ', hκ'U⟩ := Subtype.ext (by
      show kA = P0.1 * κ'
      rw [hP0e', hdec])
    rw [e1, map_mul, hP0chi, one_mul]

  obtain ⟨-, -, hAtF, -, hcm, -, -, hOff, -⟩ := GlobalTheory.FinPl.SetCut.grp_split (I.rec7 l Z) ((I.rec7 l Z).sp.X j) (Finset.univ.image fun i => (p i).v)
  have hPQ : (fun x => ∃ i, x = (p i).v) = (· ∈ (Finset.univ.image fun i => (p i).v)) := by
    funext x
    apply propext
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hκ'at : κ' ∈ grpAt ((I.rec7 l Z).sp.X j) (· ∉ (Finset.univ.image fun i => (p i).v)) := by
    have h1 : κ' ∈ GfC _ ⊓ grpOff ((I.rec7 l Z).sp.X j) (fun x => ∃ i, x = (p i).v) :=
      ⟨((hA.U j hj _ κ').1 hκ'U).1, hκ'off⟩
    rw [hOff] at h1
    have hPQn : (fun x => ¬ ∃ i, x = (p i).v) = (· ∉ (Finset.univ.image fun i => (p i).v)) :=
      funext fun x => congrArg Not (congrFun hPQ x)
    rw [hPQn] at h1
    exact h1
  have hcomm : ∀ g' ∈ c.support, g' * κ' = κ' * g' := fun g' hg' => hcm g' (hPQ ▸ hc g' hg') κ' hκ'at
  have hsuppF : ∀ g' ∈ c.support, g' ∈ GfC ((I.rec7 l Z).sp.X j) := fun g' hg' => hAtF (hPQ ▸ hc g' hg')
  have hPf : P ∈ GfC ((I.rec7 l Z).sp.X j) := hP0e' ▸ ((hA.U j hj _ P0.1).1 P0.2).1
  have hhe := hA.h j hj (A.chOf j e) ⟨e, rfl⟩
  have term : ∀ g' ∈ c.support, A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * g') =
      ((A.K j hj (A.chOf j e)).lev.chi κ'' : ℂ) * A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩ (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g') := by
    intro g' hg'
    obtain ⟨x1, hx1⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * g')
    obtain ⟨x2, hx2⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
      (A.h j (A.chOf j e) ⟨e, rfl⟩ * P * g')
    have a1 := rdΨ ⟨z.1, z.2⟩ _ (mul_mem hhe.1 (hsuppF g' hg')) x1 hx1
    have a2 := rdΨ ⟨z'.1, z'.2⟩ _ (mul_mem (mul_mem hhe.1 hPf) (hsuppF g' hg')) x2 hx2
    rw [a1, a2]
    refine hAd γ hγ x2 x1 κ'' ?_ z z' hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx1, hx2, hκ'']
    have hyv := congrArg Units.val hy
    erw [Units.val_mul, Units.val_mul] at hyv
    have hk : kA * g' = P * g' * κ' := by rw [hdec, mul_assoc, ← hcomm g' hg', ← mul_assoc]
    have e2 := congrArg (finM ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj)) hk
    simp only [StabTrans.finM_mul'] at e2 ⊢
    conv_lhs => rw [hhe.2, hyv, ← hhe.2]
    erw [← hkAe]
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← e2]
    try rfl
  have hinvP := congrFun (StabTrans.rTrans_list_prod (fun i => (β j i).gl (g i)) (trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩))
    (fun i => hinv _ _ i (g i) (hg i)) (Finset.univ : Finset ι).toList) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hPdef] at hinvP
  show trc c (A.rd θ j hj (A.chOf j e) φ ⟨z.1, z.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩) =
    ((A.K j hj (A.chOf j e)).lev.chi κ : ℂ) * trc c (A.rd θ j hj (A.chOf j e) φ ⟨z'.1, z'.2⟩) (A.h j (A.chOf j e) ⟨e, rfl⟩)
  rw [← hinvP, hchi]
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' hg' => ?_
  rw [term g' hg']
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem GlobalTheory.Unf.iteratedUnfolding_of_descent : ∀ D : D7, Descent D → IT D :=
  fun D hD => _root_.GlobalTheory.Unf.iter_of_doubleStep_lastLaw D (_root_.GlobalTheory.Unf.doubleStep_of_descent D hD) (_root_.GlobalTheory.Unf.LastSteps.lastLaw D)
end

