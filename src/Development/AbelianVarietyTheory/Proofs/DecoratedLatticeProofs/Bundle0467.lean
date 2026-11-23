module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChiPowOfLevG
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodLawMovedLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TopInv

theorem multT_right {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (θ : D.what₂.Tau → Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) (x : (⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) →ₗ[ℂ] GA D V → ℂ) (hx : x ∈ MultT θ M J χ)
    (v : ⨂[ℂ] (τ : D.what₂.Tau), ↥(M.sm τ)) : ∀ k ∈ J, ∀ g, x v (g * k) = χ k * x v g := by
  rw [mem_multT] at hx
  intro k hk g
  have key : ∀ T ∈ Mult θ M J χ, ∀ w, T w (g * k) = χ k * T w g := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hT.lev w k hk g
    | zero => intro w; simp
    | add T T' _ _ h h' => intro w; simp [h, h', mul_add]
    | smul c T _ h => intro w; simp [h]; ring
  obtain ⟨T, rfl⟩ : ∃ T, x = PiTensorProduct.lift T := ⟨_, (PiTensorProduct.lift.apply_symm_apply x).symm⟩
  rw [LinearEquiv.symm_apply_apply] at hx
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r w => simp [key _ hx w]; ring
  | add a b ha hb => simp [ha, hb, mul_add]

theorem rd_right {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (_root_.GlobalTheory.ChartReps.twDat_reps I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.AdForm.rd_charts I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ0 * (A.h j b c * k0) * κ0 * κ.1 = γ0 * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd γ0 hγ0 c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

end GlobalTheory.AdForm.TopInv


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.AdForm.TopInv.law_top : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ (f : CXP R P t) v y β (x : GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), ∀ κ ∈ UT, trc (k.eT n hn β) (f.1 v) (x * κ) * k.rd n β ψ y ((g.oT n hn).emb (x * κ, 1)) = trc (k.eT n hn β) (f.1 v) x * k.rd n β ψ y ((g.oT n hn).emb (x, 1)) := by
  intro B X I hOk hP l Z u G _ _ Pl0 Tt F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hT bad K eW hRd heW hbT hLev htl n hn ψ hψ f v y β x κ hκ
  subst hn
  unfold PinChL at hCh
  have hm : (I.rec7 l Z).R.m ≤ B.R.m := le_rfl
  rw [hT.eT, trc_single_apply, trc_single_apply]
  have hκ' := (hT.lev κ).1 hκ
  obtain ⟨κ', hκ'm⟩ := (hLev.1 κ).1 hκ'
  have hchi := hLev.2 κ κ' hκ'm
  have hx := f.2
  dsimp only [CXP] at hx
  have hr := multT_right _ _ _ _ _ hx v
  have hf := hr _ hκ' (x * g.bT)
  have e : x * g.bT * (g.bT⁻¹ * κ * g.bT) = x * κ * g.bT := by group
  rw [e] at hf
  obtain ⟨hU, hchiU, hnorm⟩ := (GlobalTheory.AdForm.rd_emb_evz I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hT.emb bad K hRd (ι _ β)).1 (GlobalTheory.AdForm.LevChiTop.chi_pow_of_levG K hLev) κ κ' hκ'm
  have hψF : ψ ∈ (I.fm l u a).Fi _ := ((hCh.ram _ hm ψ).1 hψ).1.1
  have hemb : (g.oT _ rfl).emb (x * κ, 1) = (g.oT _ rfl).emb (x, 1) * ((g.oT _ rfl).emb.comp (MonoidHom.inl _ _)) κ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hq : ∀ z, k.rd (I.rec7 l Z).R.m β ψ y z = A.rd R.θ _ hm (ι _ β) ψ y z := fun z => congrFun (hCh.rdq _ hm β ψ y) z
  have hr2 : A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1) * ((g.oT (I.rec7 l Z).R.m rfl).emb.comp (MonoidHom.inl _ _)) κ) = ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1)) :=
    rd_right I hOk hP l Z u a Ch₀ A hCh.is R.θ hX.inf _ hm ψ hψF _ y _ ⟨_, hU⟩
  have hc : ((A.chi (I.rec7 l Z).R.m (ι _ β) ⟨_, hU⟩ : ℂˣ) : ℂ) = ((K.lev.chi κ' : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hchiU
  rw [hemb, hq, hq, hr2, hc, hf, hchi]
  have h1 : star ((K.lev.chi κ' : ℂˣ) : ℂ) * ((K.lev.chi κ' : ℂˣ) : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm]; simp
  linear_combination (ε * f.1 v (x * g.bT) * A.rd R.θ _ hm (ι _ β) ψ y ((g.oT (I.rec7 l Z).R.m rfl).emb (x, 1))) * h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastPeriodTailEqLoweredEvaluationPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm


open _root_.Formalism.L2.Col in
theorem tailTop_eq_of_pin : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → (∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c)) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ n (hn : n = (I.rec7 l Z).R.m), ∀ ψ ∈ k.Ram n, ∀ f : CXP R P t, (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * ∑ β ∈ @Finset.univ (k.Ch n) (k.fin n), ∑ c : (I.fm l u a).clsP, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f ((realOf u R g s J).low n hn fun z => k.rd n β ψ (((realOf u R g s J).fr n).symm z) ((g.oT n hn).emb (h c, 1))) = k.cP * (tupOf R P u g t r k tl).tail n hn ψ f := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w hCh UT ε hTop bad K eW hRP heW hbT hLev hG h hh hst G' hG' n hn ψ hψ f
  subst hn
  have hC : PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK := hCh
  have hIs : A.Is := hC.is
  have hψF : ψ ∈ (I.fm l u a).Fi B.R.m := ((hC.ram B.R.m le_rfl ψ).1 hψ).1.1
  have hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1 := N_m_succ B.R

  obtain ⟨Lz, hLz⟩ : ∃ Lz, Lz = (I.per l u a).lowerMap ((I.per l u a).evz ψ) := ⟨_, rfl⟩
  have hlow : ∀ c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)),
      Lz c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) y :=
    fun c y => hLz ▸ (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.2.2 a _ c y
  have heL : ∀ c, eW Lz c = fun y => lowOf I l Z u (fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩) ⟨y.1, y.2⟩ := by
    intro c; funext y
    rw [heW Lz c y ⟨y.1, y.2⟩ rfl]
    exact hlow c ⟨y.1, y.2⟩

  have hw : ∀ c, eW Lz c ∈ LinearMap.range j := by
    intro c
    rw [hj.range]
    have hv0 := GlobalTheory.EvzVal.evz_mem_valC I hI hP l Z u a ψ hψF c
    have hv1 := (GlobalTheory.TrueBranch.branching_true_columns I hI hP l Z u hN).2.1.1 _ hv0
    obtain ⟨Pp, hPp, hEq⟩ := hv1
    rw [heL c]
    exact ⟨Pp, hPp, funext fun y => congrFun hEq ⟨y.1, y.2⟩⟩
  obtain ⟨G'', hR'', htl⟩ := hG ψ f
  have hper : (I.per l u a).Ptil ψ (G' f) = tl ψ f := by
    rw [htl]
    have := GlobalTheory.Fam.Check.ReadsG.period_eq K eW j g.bT (hG' f) hR'' Lz hw
    rw [hLz] at this
    exact this

  have hsum : ∀ β : k.Ch B.R.m, ∑ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
      (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) = ε * tl ψ f := by
    intro β
    have hev : ∀ c y, A.rd R.θ B.R.m le_rfl (ι B.R.m β) ψ y ((g.oT B.R.m rfl).emb (h c, 1)) = (I.per l u a).evz ψ c y :=
      fun c y => (GlobalTheory.AdForm.rd_emb_evz I hI hP l Z u a Ch₀ A hIs R.θ hX.inf _ hTop.emb bad K hRP (ι B.R.m β)).2 ψ hψF c (h c) (hh c) y
    have hterm : ∀ c, ((stabOrd UT (h c) : ℕ) : ℂ)⁻¹ * ellTop R P eW ε G' c f
        (lowOf I l Z u (fun z => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1)))) =
        ε * (I.per l u a).period (eW.symm (Pi.single c (eW Lz c))) (G' f) := by
      intro c
      have hne : (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.card_pos (α := (I.fm l u a).stabilizer₂ c)).ne'
      have e2 : (fun z : FrN (I.rec7 l Z) (B.R.N B.R.m) => k.rd B.R.m β ψ ⟨z.1, z.2⟩ ((g.oT B.R.m rfl).emb (h c, 1))) =
          fun y' => (I.per l u a).evz ψ c ⟨y'.1, y'.2⟩ := by
        funext z
        exact (congrFun (hC.rdq B.R.m le_rfl β ψ _) _).trans (hev c _)
      rw [e2, ellTop_apply, hst c, heL c]
      field_simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← map_sum]
    have e3 : ∑ c, Pi.single c (eW Lz c) = eW Lz := Finset.univ_sum_single _
    rw [e3, LinearEquiv.symm_apply_apply, ← hper, hLz]
    rfl
  have hsub : Subsingleton (k.Ch B.R.m) :=
    ⟨fun β β' => hC.live.inj B.R.m ((GlobalTheory.AdForm.TwTest.subsingleton_top hIs).elim _ _)⟩
  rw [hTop.cP]
  have htail : ∀ hm, (tupOf R P u g t r k tl).tail _ hm ψ f = tl ψ f := fun _ => rfl
  rw [htail]
  refine (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (Finset.sum_congr rfl fun β _ => hsum β)).trans ?_
  have e1 : ∀ {α : Type} (inst : Fintype α), (∀ a b : α, a = b) → α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = x := by
    intro α inst hs a x
    haveI : Unique α := ⟨⟨a⟩, fun b => hs _ _⟩
    exact Fintype.sum_unique _
  have e0 : ∀ {α : Type} (inst : Fintype α), IsEmpty α → ∀ x : ℂ,
      @Finset.sum α ℂ _ (@Finset.univ α inst) (fun _ => x) = 0 := by
    intro α inst hE x
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rcases isEmpty_or_nonempty (k.Ch B.R.m) with hE | hne
  · have h0 : ψ = 0 := by
      funext c
      obtain ⟨β, -⟩ := hC.live.last (A.chOf B.R.m c)
      exact (hE.false β).elim
    have h1 : tl ψ f = 0 := by
      rw [← hper, h0]
      show ((I.per l u a).period ((I.per l u a).lowerMap ((I.per l u a).evz 0))) (G' f) = 0
      simp only [map_zero, LinearMap.zero_apply]
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e0 _ hE _)).trans (by rw [h1]; ring)
  · obtain ⟨β₀⟩ := hne
    exact (congrArg (fun S => (GlobalTheory.SeeSaw.volLev g.volT UT : ℂ) * S) (e1 _ (fun a b => hsub.elim a b) β₀ _)).trans (by ring)

end GlobalTheory.AdForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticePairCharacterIndicatorTransformEqCosetInd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

noncomputable section
namespace GlobalTheory.KapStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (L T : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (s : k), s ≠ 0 → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = s * (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ r)) → ∀ (a : (n → k) → ℂ) (c : SB (Matrix n Unit k)), (∀ M, c.1 M = a (s⁻¹ • fun r => M r ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) FL (GlobalTheory.LocMod.Frame.ofFinPl β) c = colFun β ζ a := by
  intro D k _ _ _ _ p L T n _ _ β ζ s hs FL hFL a c hc
  classical
  funext y
  rw [GlobalTheory.LocMod.Witness.ext_apply, hc, colFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zcol, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, map_sum, map_mul, hFL, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show s⁻¹ * (β.b' r i * p.pr (y i j) * (s * p.pr (incA D (ζ j)))) = _
  field_simp

theorem rowExt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (T L : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p T n) (ζ₀ : Fin L.rank → D.host.E), IsLineVec L ζ₀ → ∀ (FL : GlobalTheory.LocMod.Frame k L.rank Unit), (∀ r, FL.β r () = (GlobalTheory.LocMod.Place.ofSplitPt p).pr (ζ₀ r)) → ∀ (b : (n → k) → ℂ) (Φ : SB (Matrix Unit n k)), (∀ M, Φ.1 M = b (M ())) → GlobalTheory.LocMod.Witness.ext (GlobalTheory.LocMod.Place.ofSplitPt p) (GlobalTheory.LocMod.Frame.ofFinPl β) FL Φ = rowFun β ζ₀ b := by
  intro D k _ _ _ _ p T L n _ _ β ζ hζ FL hFL b Φ hΦ
  classical
  funext x
  rw [GlobalTheory.LocMod.Witness.ext_apply, hΦ, rowFun]
  refine if_congr Iff.rfl ?_ rfl
  congr 1
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set f := GlobalTheory.LocMod.Witness.prH P with hf
  have hfa : ∀ a, f a = p.pr (incA D a) := fun _ => rfl
  set h : D.host.E := star ζ ⬝ᵥ Matrix.mulVec L.gram ζ with hh
  have h0 : f h ≠ 0 := (map_ne_zero f).2 hζ.2
  set u : Fin L.rank → k := fun j => f ((Matrix.vecMul (star ζ) L.gram) j) with hu
  have hu1 : ∑ j, u j * f (ζ j) = f h := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hh, Matrix.dotProduct_mulVec, dotProduct, map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_mul f _ _).symm
  have hγ : ∀ j, FL.γ () j = (f h)⁻¹ * u j := fun j => by
    have h1 : ∀ i, f (ζ i) * FL.γ () j = (1 : Matrix _ _ k) i j := fun i => by
      rw [← FL.βγ, Matrix.mul_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact congrArg (· * _) (hFL i).symm
    have h2 : u j = f h * FL.γ () j := by
      rw [← hu1, Finset.sum_mul]
      simp only [mul_assoc, h1, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h2, inv_mul_cancel_left₀ h0]
  funext r
  simp only [GlobalTheory.LocMod.Place.down, GlobalTheory.FinPl.ExtZero.zrow, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, hγ, Matrix.map_apply]
  show _ = (f h)⁻¹ * ∑ i, p.pr (∑ j, incA D (Matrix.vecMul (star ζ) L.gram j) * x j i) * β.b i r
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (Lifts InDual resUnit) in
theorem fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : MeasureTheory.Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] [DecidableEq n] (χ : AddChar k Circle) (hχ : HasConductor χ 1) (q : Unif k) (ψk : AddChar k Circle) (xi s : k), (∀ x, ψk x = χ (xi * x)) → s ≠ 0 → ∀ w : 𝒪[k]ˣ, -(xi * s) = ((w : 𝒪[k]) : k) → ∀ Q : Pair k n, ∃ (C : ℂ) (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix Unit n k)), (∀ M, c.1 M = charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∧ (∀ M, Ψ.1 M = cosetInd q Q.lat ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹ • Q).red (M ())) ∧ ∀ η, C * Ψ.1 η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c.1 (Matrix.of fun r _ => y r)) (η ()) := by
  intro k _ _ _ _ _ _ ν hν n _ _ χ hχ q ψk xi s hψk hs w hw Q
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  haveI := hν
  obtain ⟨F, hF⟩ := GlobalTheory.FinPl.CosetPairing.exists_lifts Q
  set wk : k := ((w : 𝒪[k]) : k) with hwk
  set wi : k := (((w⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) with hwi
  have hww : wk * wi = 1 := by rw [hwk, hwi, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hF' : Lifts Q.lat (wi • F) ((resUnit w)⁻¹ • Q).red := fun y => by
    obtain ⟨t, ht, hr⟩ := hF y
    refine ⟨(w⁻¹ : 𝒪[k]ˣ) * t, by rw [smul_dotProduct, ← ht]; rfl, ?_⟩
    rw [map_mul, hr]
    rfl
  let L' : Submodule 𝒪[k] (n → k) := Q.lat.comap ((LinearMap.lsmul k (n → k) s⁻¹).restrictScalars 𝒪[k])
  have hc : (fun M : Matrix n Unit k => charInd (resChar χ hχ q) Q (s⁻¹ • fun r => M r ())) ∈ SB (Matrix n Unit k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.SBFacts.charInd_mem _ Q) (s := fun y => Matrix.of fun r _ => s * y r)
      (by fun_prop) (continuous_pi fun r => continuous_pi fun _ => by simp only [Matrix.of_apply]; fun_prop) fun M => by
        ext r u
        simp [hs]
  have hΨ : (fun M : Matrix Unit n k => cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (M ())) ∈ SB (Matrix Unit n k) :=
    GlobalTheory.FinPl.Comm.comp_mem_SB (GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB k n q Q.lat _) (s := fun y => Matrix.of fun _ r => y r)
      (by fun_prop) (continuous_pi fun _ => continuous_pi fun r => by simp only [Matrix.of_apply]; fun_prop) fun M => rfl
  refine ⟨∫ y, vecInd L' y ∂(MeasureTheory.Measure.pi fun _ => ν), ⟨_, hc⟩, ⟨_, hΨ⟩, fun _ => rfl, fun _ => rfl, fun η => ?_⟩
  set η' : n → k := η () - q.inv • wi • F with hη'
  have e1 : cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) = dualInd Q.lat η' := by
    rw [← GlobalTheory.FinPl.CosetPairing.cosetInd_add q hF' η', hη', sub_add_cancel]
  have e2 : ∀ y : n → k, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) =
      vecInd L' y * (χ (wk * s⁻¹ * (η' ⬝ᵥ y)) : ℂ) := fun y => by
    by_cases hy : s⁻¹ • y ∈ Q.lat
    · have hy' : y ∈ L' := hy
      obtain ⟨t, ht, hr⟩ := hF ⟨_, hy⟩
      have hr' : Q.ev (s⁻¹ • y) = residue 𝒪[k] t := ((Q.hasVal_fn ⟨_, hy⟩).ev_eq).trans hr.symm
      rw [charInd, vecInd, vecInd, if_pos hy, if_pos hy', hr', ← map_neg, resChar_residue, hψk, mul_one, one_mul,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      have ht' : (t : k) = s⁻¹ * (F ⬝ᵥ y) := by rw [ht]; simp
      have hx : xi = -wk * s⁻¹ := by rw [← hw]; field_simp
      rw [hη', sub_dotProduct, smul_dotProduct, smul_dotProduct, Subring.coe_neg, ht', hx, smul_eq_mul, smul_eq_mul]
      linear_combination (q.inv * s⁻¹ * (F ⬝ᵥ y)) * hww
    · have hy' : y ∉ L' := hy
      rw [charInd, vecInd, vecInd, if_neg hy, if_neg hy', mul_zero, zero_mul, zero_mul]
  show _ * cosetInd q Q.lat ((resUnit w)⁻¹ • Q).red (η ()) =
    ∫ y, charInd (resChar χ hχ q) Q (s⁻¹ • y) * (ψk (-1 * (η () ⬝ᵥ y)) : ℂ) ∂(MeasureTheory.Measure.pi fun _ => ν)
  simp only [e2]
  rw [e1, dualInd]
  split_ifs with hd
  · rw [mul_one]
    congr 1
    funext y
    by_cases hy : y ∈ L'
    · have h1 : wk * s⁻¹ * (η' ⬝ᵥ y) ∈ 𝒪[k] := by
        have := mul_mem (w : 𝒪[k]).2 (hd _ hy)
        convert this using 1
        simp [mul_assoc, hwk]
      rw [apply_int_eq_one hχ ⟨_, h1⟩]
      simp
    · rw [vecInd, if_neg hy, zero_mul]
  · rw [mul_zero]
    obtain ⟨y, hy, hn⟩ : ∃ y ∈ Q.lat, η' ⬝ᵥ y ∉ 𝒪[k] := by
      by_contra h
      push Not at h
      exact hd h
    have h0 : η' ⬝ᵥ y ≠ 0 := fun h => hn (h ▸ zero_mem _)
    obtain ⟨z, hz, hz1⟩ : ∃ z, valuation k z ≤ valuation k (η' ⬝ᵥ y) ∧ χ z ≠ 1 := by
      by_contra h
      push Not at h
      exact hn ((Valuation.mem_integer_iff _ _).2 (by simpa using (hχ _).1 h))
    have ht : z / (η' ⬝ᵥ y) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hz zero_le'
    let t : 𝒪[k] := (w⁻¹ : 𝒪[k]ˣ) * ⟨_, ht⟩
    have hy₀ : s • t • y ∈ L' := by
      show s⁻¹ • s • t • y ∈ Q.lat
      rw [inv_smul_smul₀ hs]
      exact Q.lat.smul_mem t hy
    refine (GlobalTheory.FinPl.Comm.integral_vecInd_eq_zero χ _ _ L' η' hy₀ ?_).symm
    convert hz1 using 2
    show wk * s⁻¹ * (η' ⬝ᵥ s • (wi * (z / (η' ⬝ᵥ y))) • y) = z
    rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc wi, div_mul_cancel₀ _ h0]
    field_simp
    linear_combination z * hww

theorem kapStep : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n : Type) [Fintype n] [DecidableEq n] (L S L'' : HSp D) (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (β : Frame p S n) (LS : Lat S), IsSelfDualC S LS → ∀ (Q : Pair k n) (g₁ : WO L S → ℂ) (T₁ : (WO L S → ℂ) →ₗ[ℂ] (WO L S → ℂ)), IsThetaFunO ψ L S g₁ → IsPlaceModel ψ (symplO L S) (heisO ψ L S) p.e (latO L S ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ} : Lat L) : Set _) (LS : Set _) (· = p.v)) 1 g₁ T₁ → ∃ (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ ∧ IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ ∧ T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red)) = fun w => T₁ (colFun β ζ (charInd (resChar χ hχ q) Q)) (kap τ S w) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n _ _ L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  set P := GlobalTheory.LocMod.Place.ofSplitPt p with hP
  set l : k := p.pr (incA D lam) with hl
  have hl0 : l ≠ 0 := fun h => by rw [h, map_zero] at hlam; exact zero_ne_one hlam
  have hlO : l ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hlam.le
  have hliO : l⁻¹ ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hlam, inv_one])
  let w : 𝒪[k]ˣ := ⟨⟨l, hlO⟩, ⟨l⁻¹, hliO⟩, Subtype.ext (mul_inv_cancel₀ hl0), Subtype.ext (inv_mul_cancel₀ hl0)⟩
  refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.resUnit w)⁻¹, ?_⟩
  intro β LS hLS Q g₁ T₁ hg₁ hT₁
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have hν : (MeasureTheory.Measure.addHaar : MeasureTheory.Measure k).IsAddHaarMeasure := inferInstance
  have hxi : P.xi ≠ 0 := GlobalTheory.LocMod.Witness.xi_ne P
  set s : k := -l / P.xi with hs
  have hs0 : s ≠ 0 := div_ne_zero (neg_ne_zero.2 hl0) hxi
  have hxs : -(P.xi * s) = ((w : 𝒪[k]) : k) := by
    show -(P.xi * (-l / P.xi)) = l
    field_simp

  have hζne : ∃ r, ζ r ≠ 0 := by
    by_contra h
    have hz : ∀ r, ζ r = 0 := by simpa only [not_exists, not_not] using h
    apply hζ.2
    have : ζ = 0 := funext hz
    simp [this]
  have hz : (fun r => s * P.pr (ζ r)) ≠ 0 := by
    obtain ⟨r, hr⟩ := hζne
    intro h
    have h1 := congrFun h r
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hs0 h2
    · exact hr ((GlobalTheory.LocMod.Witness.prH P).injective (h2.trans (map_zero _).symm))
  obtain ⟨FL, hFL⟩ := GlobalTheory.KappaModel.exists_frame_col hζ.1 _ hz
  set FS := GlobalTheory.LocMod.Frame.ofFinPl β with hFS
  have hTLS := GlobalTheory.LineLatModel.isModel_ext D k p ψ hψ hU L S ζ hζ LS hLS g₁ T₁ hg₁ hT₁ n FL FS

  let ψk : AddChar k Circle := χ.compAddMonoidHom (AddMonoidHom.mulLeft P.xi)
  have hψk : ∀ x, ψk x = χ (P.xi * x) := fun _ => rfl
  have hk : P.IsChar ψ ψk := (GlobalTheory.LocMod.Place.isChar_ofSplitPt p hc).2 hψk
  set z₀ : Fin L''.rank → k := fun i => P.pr (ζ₀ i) with hz₀
  have hτz : (τ.map P.pr).mulVec z₀ = (-(P.xi * s)) • fun i => P.pr (ζ i) := by
    rw [hxs]
    funext i
    have h2 := congrArg (fun v => GlobalTheory.LocMod.Witness.prH P (v i)) hτ
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.map_mulVec] at h2
    simp only [Pi.smul_apply, smul_eq_mul]
    exact h2
  obtain ⟨FL'', hFL'', TL, hTL, hTLc⟩ := GlobalTheory.KappaModel.kappa_model D k P MeasureTheory.Measure.addHaar hν ψ hψ ψk hk
    L S L'' ζ τ hζ₀.1 hG s z₀ hs0 hτz n FS FL hFL _ hTLS
  obtain ⟨C, c, Ψ, hc1, hΨ, hCΨ⟩ := fourier k MeasureTheory.Measure.addHaar hν n χ hχ q ψk P.xi s hψk hs0 w hxs Q
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃e⟩ := _root_.GlobalTheory.ModelExtend.exists_placeModel_ext D k p ψ hψ hU S L'' ζ₀ hζ₀ LS hLS n FS FL'' (C • TL)
    (GlobalTheory.LocMod.Witness.isModel_smul P hTL C)
  refine ⟨g₃, T₃, hg₃, hT₃, ?_⟩
  have hrow := rowExt D k p S L'' n β ζ₀ hζ₀ FL'' hFL'' _ Ψ hΨ
  have hcol := colExt D k p L S n β ζ s hs0 FL hFL _ c hc1
  rw [← hrow, hT₃e, LinearMap.smul_apply, ← map_smul]
  funext w'
  rw [hTLc c (C • Ψ) (fun η => by rw [← hCΨ η]; rfl) w']
  show T₁ (GlobalTheory.LocMod.Witness.ext P FL FS c) _ = _
  rw [hcol]
  rfl

end GlobalTheory.KapStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentIntegralOfFiniteMatrixIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_integral_of_finiteMatrix_integral : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (κ : GA D V) (x : GL (Fin n) (GlobalTheory.AdForm.EF D)), GlobalTheory.AdForm.finM V hn κ = x.1 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ i j, (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x).1 i j ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E) (v.adicCompletionIntegers D.host.F).toSubring) → ∀ i j, (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v κ)).1 i j ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.FinIntBridge.mem_intLoc_of_finM | exact GlobalTheory.FinIntBridge.mem_intLoc_of_finM | (intros; apply GlobalTheory.FinIntBridge.mem_intLoc_of_finM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopVol
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX}

end GlobalTheory.TopVol

end
end

