module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
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

section Compare

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def RowAt {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

abbrev IsSum {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (t : Tp) (x : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev cuspOver {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) :
    Submodule O.c'.F (Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') :=
  cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank

def ClassSumsSpan {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop :=
  cuspOver O κ ≤ Submodule.span O.c'.F {g | g ∈ cuspOver O κ ∧ ∃ x, O.Plc () x ∧ IsSum O () x g}

def geo {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') (q : AutQ (Wc D i)) : ℂ :=
  cc (O.dict q.out).1 * jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu
    (actLev O.c' O.lev2 z f) q

variable {Tp : Type} {tup : Tp → T0}

theorem geo_add (O : OMDat C R i Tp tup) (cc z f g q) : geo O cc z (f + g) q = geo O cc z f q + geo O cc z g q := by
  unfold geo
  rw [map_add (f := _), map_add (f := _), Pi.add_apply, mul_add]

theorem geo_smul (O : OMDat C R i Tp tup) (cc z) (a : O.c'.F) (f q) : geo O cc z (a • f) q = (a : ℂ) * geo O cc z f q := by
  unfold geo
  rw [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rfl

theorem geo_of_isBC (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) (cc z)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n)
    {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n)
    (h : IsBC O.hle f as fs) (q : AutQ (Wc D i)) :
    geo O cc z f q = ∑ k, (as k : ℂ) * O.phi cc (actLev C.Q.c O.lev2 z (fs k)) q.out := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1) (O.dict q.out).1) (O.dict q.out).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (O.dict q.out).1 * (O.mu q.out * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem phi_eq {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (O' : OMDat C R i Tp' tup')
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) : O.phi (cE O.s0) = O'.phi (cE O'.s0) := by
  have key : ∀ (s s' : C.Q.c.F →+* ℂ) (_ : s = s') (hV : C.V ((i : ℕ) + 1) s = Wc D i) (hV' : C.V ((i : ℕ) + 1) s' = Wc D i)
      (f : C.R ((i : ℕ) + 1)),
      adel (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s)) (muPin (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s))
        (castDict hV (C.mu ((i : ℕ) + 1) s)) (cE s)) (rdU (C.U ((i : ℕ) + 1) s) f) =
      adel (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s')) (muPin (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s'))
        (castDict hV' (C.mu ((i : ℕ) + 1) s')) (cE s')) (rdU (C.U ((i : ℕ) + 1) s') f) := by
    intro s s' e hV hV' f
    subst e
    rfl
  funext f
  exact key _ _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm) O.hV O'.hV f

theorem geo_rulBC {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (M : OMDat C R i Tp' tup') (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (q : AutQ (Wc D i)) :
    geo M (cE M.s0) z (rulBC hle f) q = geo O (cE O.s0) z f q := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  rw [geo_of_isBC O hact _ z hf hfs h, geo_of_isBC M (e ▸ hact) _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle M.hle hf h), phi_eq M O cE, e]
  rfl

theorem isSum_unique {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) (t : Tp)
    {x : O.Cl' t → VsV D i O.c'.F} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f f' : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'}
    (hf : f ∈ sec _ O.c' a n) (hf' : f' ∈ sec _ O.c' a n) (h1 : IsSum O t x f) (h2 : IsSum O t x f') : f = f' := by
  obtain ⟨-, cga, -, -, hr, -⟩ := h.io
  refine GlobalTheory.ClassSumUnique.isThClsD_unique GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.cov t).1 (h.cov t).2.2
    (fun k => ⟨((h.reps t).1 k).1, ((h.reps t).1 k).2.2.1, ((h.reps t).1 k).2.2.2.1⟩) (wtA κ) (fun v => ?_) x a n f hf f' hf' h1 h2
  have hv := hr.le (LinearMap.mem_range_self O.io v)
  exact (Submodule.span_le (p := GlobalTheory.FrameRead.CoefMap.harmSub _ _ _ _ _ _)).2 (fun _ hP => hP) hv

theorem geo_agree {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (M : OMDat C R i Tp tup) (hle : O.c'.F ≤ M.c'.F)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hspan : ClassSumsSpan O κ)
    {cc cc' : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ} {z z' : G} {α β : ℂ} (q : AutQ (Wc D i))
    (h : ∀ g ∈ cuspOver O κ, (∃ x, O.Plc () x ∧ IsSum O () x g) →
      α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q) :
    ∀ f ∈ cuspOver M κ, α * geo M cc z f q = β * geo M cc' z' f q := by
  have hlin := (GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (C.Q.Xo ((i : ℕ) + 1)) _ _ hle).2
  have h0 : rulBC hle (0 : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') = 0 := by
    have := hlin (-1) 0 0
    rwa [smul_zero, zero_add, map_neg, map_one, neg_one_smul, neg_add_cancel] at this
  have h1 : ∀ g ∈ cuspOver O κ, α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q := by
    intro g hg
    have hg' := hspan hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem g hg => exact h g hg.1 hg.2
    | zero =>
      have e := geo_smul M cc z 0 0 q
      have e' := geo_smul M cc' z' 0 0 q
      rw [zero_smul] at e e'
      rw [h0, e, e']
      simp
    | add f g _ _ hf hg =>
      have e := hlin 1 f g
      rw [one_smul, map_one, one_smul] at e
      rw [e, geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf =>
      have e := hlin a f 0
      rw [add_zero, h0, add_zero] at e
      rw [e, geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  intro f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  rw [geo_of_isBC M hact cc z hf' hs hBC, geo_of_isBC M hact cc' z' hf' hs hBC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)
  have hb := isBC_rulBC_trans O.hle hle M.hle hk (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)
  have hs1 : ∀ k', ![fs k] k' ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k' => by
    rw [Subsingleton.elim k' 0]; exact hs k
  have e := h1 _ (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (C.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k))
  rw [geo_of_isBC M hact cc z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb,
    geo_of_isBC M hact cc' z' (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb] at e
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
  rw [mul_left_comm, e, mul_left_comm]


set_option maxHeartbeats 1000000 in
theorem oneMapOf_of_extends (O : OMDat C R i Unit (fun _ => A.μ0)) (M : OMDat C R i Tp tup) (t₀ : Tp) (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (hM : M.Pins κ v₀ ι x₀)
    (hext : ∀ x, O.Plc () x → ∃ x', M.Plc t₀ x' ∧ M.thAd t₀ x' = O.thAd () x ∧
      ∀ f ∈ sec _ O.c' (wtA κ) (Vc D i).rank, IsSum O () x f → IsSum M t₀ x' (rulBC hle f))
    (hspan : ClassSumsSpan O κ) (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) {ph : ℂ}
    (hO : O.OneMapOf κ v₀ (cE O.s0) ph) {cc' ph'} (hrow : RowAt M κ cc' ph') : M.OneMapOf κ v₀ (cE M.s0) ph := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hact := hM.act.1
  obtain ⟨hEq, ⟨hL, -, -, hcU, hph, z, hz, hO⟩, hRat⟩ := hO
  obtain ⟨ζ, hζL, ⟨m, hm, hζ⟩, hO⟩ := hO ()
  obtain ⟨-, hph', z', -, hrow⟩ := hrow
  obtain ⟨ζ₀, hζ₀L, ⟨m₀, hm₀, hζ₀⟩, hrow₀⟩ := hrow t₀
  have hζ₀0 : ζ₀ ≠ 0 := fun h0 => by simp [h0, hm₀.ne'] at hζ₀
  have hph0 : ph' ≠ 0 := fun h0 => by simp [h0] at hph'
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) := ⟨_, rfl⟩
  have mul4 : ∀ a b d : ℂ, a * b * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) * d = a * s * (b * d) :=
    fun a b d => by rw [hs]; ring
  have key : ∀ q, ∀ f ∈ cuspOver M κ, (ph' * ζ * s) * geo M (cE M.s0) z f q = (ph * ζ₀ * s) * geo M cc' z' f q := by
    intro q
    refine geo_agree O M hle hact hspan q ?_
    rintro g hg ⟨x, hx, hgx⟩
    have hg' := ((mem_cusp _ _ _ _ _ _).1 hg).1
    obtain ⟨x', hx', hth, hsum⟩ := hext x hx
    have h1 : ph * O.thAd () x q = ζ * s * geo O (cE O.s0) z g q := ((hO x hx).2 g hg' hgx q).trans (mul4 _ _ _)
    have h2 : ph' * M.thAd t₀ x' q = ζ₀ * s * geo M cc' z' (rulBC hle g) q :=
      ((hrow₀ x' hx').2 _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hg') (hsum g hg' hgx) q).trans (mul4 _ _ _)
    rw [geo_rulBC O M hle hlev (e ▸ hact) cE z hg']
    rw [hth] at h2
    linear_combination ph * h2 - ph' * h1
  refine ⟨?_, ⟨hL.trans hle, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2, ?_, hph, z, hz, fun t => ?_⟩, ?_⟩
  · unfold OMDat.EquivAt
    rw [phi_eq M O cE, e]
    exact hEq
  · have : ∀ s, s = O.s0 → ∀ k, ‖cE s k‖ = 1 := fun s hs => hs ▸ hcU
    exact this _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm)
  · obtain ⟨ζt, hζtL, ⟨mt, hmt, hζt⟩, ht⟩ := hrow t
    refine ⟨ζt * ζ * ζ₀⁻¹, mul_mem (mul_mem hζtL hζL) (inv_mem hζ₀L), ⟨mt * m * m₀, by positivity, ?_⟩,
      fun x hx => ⟨(ht x hx).1, fun f hf hfx q => ?_⟩⟩
    · have a1 : ζt ^ (mt * m * m₀) = 1 := by rw [mul_assoc, pow_mul, hζt, one_pow]
      have a2 : ζ ^ (mt * m * m₀) = 1 := by rw [mul_comm mt m, mul_assoc, pow_mul, hζ, one_pow]
      have a3 : ζ₀ ^ (mt * m * m₀) = 1 := by rw [mul_comm, pow_mul, hζ₀, one_pow]
      rw [mul_pow, mul_pow, inv_pow, a1, a2, a3]
      simp
    · obtain ⟨f₀, hf₀, hf₀x⟩ := (ht x hx).1
      obtain rfl : f = f₀ := isSum_unique hM t hf ((mem_cusp _ _ _ _ _ _).1 hf₀).1 hfx hf₀x
      have h1 : ph' * M.thAd t x q = ζt * s * geo M cc' z' f q := ((ht x hx).2 f hf hfx q).trans (mul4 _ _ _)
      have h2 := key q f hf₀
      have i1 := mul_inv_cancel₀ hζ₀0
      refine Eq.trans ?_ (mul4 _ _ _).symm
      show ph * M.thAd t x q = ζt * ζ * ζ₀⁻¹ * s * geo M (cE M.s0) z f q
      apply mul_left_cancel₀ (mul_ne_zero hph0 hζ₀0)
      linear_combination (ph * ζ₀) * h1 - ζt * h2 - (ph' * ζt * ζ * s * geo M (cE M.s0) z f q) * i1
  · unfold OMDat.PhRat
    rw [phi_eq M O cE]
    exact hRat

theorem oneMapOf_comap {Tp' : Type} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ cc ph}
    (h : O.OneMapOf κ v₀ cc ph) : (comap O f).OneMapOf κ v₀ cc ph := by
  obtain ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, h7⟩, h8⟩ := h
  exact ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, fun t => h7 (f t)⟩, h8⟩

end Compare

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def IdentityRow (i : Fin D.R.m) : Prop :=
  ∀ (Tp : Type) (tup : Tp → T0) (O' : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F →
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) → ∃ cc ph, RowAt O' (κ i) cc ph

def PinnedDataExist (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

variable {T R κ v₀}


variable (T R κ v₀)

end Row

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiWIncM
section
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.FourSumComposition

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA (σ : E →ₐ[F] E) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [piW, cA, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]

theorem piW_incM {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (i j : Fin m) :
    piW τ (incM F J i j) = τ (J i j) := by
  simp [incM, inclR, piW, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]

theorem comp_comp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) : (τ.comp σ).comp σ = τ := by
  ext x
  simp [GlobalTheory.AdelicU.cm_conj_conj h x]

theorem sum_four {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (X U : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l = ∑ k, ∑ l, (-(A * X * B.transpose)) k l * U k l := by

  have hR : ∀ k l, (-(A * X * B.transpose)) k l * U k l = ∑ j, ∑ i, X i j * A k i * -B l j * U k l := by
    intro k l
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, neg_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hR]
  calc ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l
      = ∑ i, ∑ k, ∑ j, ∑ l, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, X i j * A k i * -B l j * U k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ (i j : Fin m), (σ : E → E) (JA j i) = JA i j) → (∀ (i j : Fin n), (σ : E → E) (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k : Fin m, ∑ l : Fin n, (-(Matrix.map JA (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.transpose (Matrix.map JB (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)))) k l * Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) k l := by
  intro F E _ _ _ _ _ σ hσ v τ m n JA JB hA hB x u hx hu
  have hx' : ∀ i j, piW τ (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
  have hu' : ∀ k l, piW (τ.comp σ) (u k l) = 0 := fun k l => by simpa using congrFun (congrFun hu k) l

  have h1 : piW τ (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) = 0 := by
    simp [GlobalTheory.WeilM.hTens, piW_cA, hu']

  have h2 : piW (τ.comp σ) (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) =
      ∑ i, ∑ j, ∑ k, ∑ l, (x.map (piW (τ.comp σ))) i j * (JA.map τ) k i * -(JB.map τ) l j *
        (u.map (piW τ)) k l := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, piW_cA, comp_comp hσ, piW_incM, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hA k i, hB l j, map_neg]
  rw [h1, zero_add, h2]
  exact sum_four _ _ _ _

end GlobalTheory.FourSumComposition
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsGaussianSmulConstUnique
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact

theorem reads_smul_const_unique : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (G : VC D a d → ℂ) (f : WO S T → ℂ) (c c' : ℂ), G ≠ 0 →
  Reads ψ θ hS hT cc δ r (c • G) f → Reads ψ θ hS hT cc δ r (c' • G) f → c = c' := by
  intro D ψ θ S T a d hS hT cc δ r hs G f c c' hG h1 h2
  subst hS hT
  obtain ⟨Y, hY⟩ : ∃ Y, G Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hG (funext hc)
  have hδ : δ ≠ 0 := delta_ne_zero hs.crv
  have hr : r ≠ 0 := IsScale.ne_zero hs.crv.1.1 hs.scale
  have hm : ∀ τ, δ * embT D τ r ≠ 0 := fun τ => mul_ne_zero hδ ((map_ne_zero _).2 hr)
  obtain ⟨x, ⟨hx, hx0⟩, -⟩ := GlobalTheory.StdUnn.exists_unique_of_comp_finPart D θ hs.inf T.rank S.rank
    (fun τ => Matrix.of fun i j => Y τ i j / (δ * embT D τ r)) 0
  replace hx0 : x.map (finPart D) = 0 := by rw [hx0]; exact Matrix.map_zero _ (map_zero _)
  have hxY : coordY θ rfl rfl δ r x = Y := by
    funext τ i j
    simp only [coordY, Fin.cast_eq_self, hx, Matrix.of_apply]
    have hE : embT D τ r ≠ 0 := (map_ne_zero _).2 hr
    field_simp [hm τ, hE, hδ]
  have e1 := h1.2 x hx0
  have e2 := h2.2 x hx0
  rw [hxY] at e1 e2
  rw [e1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at e2
  have he := Complex.exp_ne_zero (-((Real.pi : ℂ) / 2) * Hf D (tor0 D cc δ) Y Y)
  have := mul_left_cancel₀ he e2
  exact mul_right_cancel₀ hY this

end GlobalTheory.NormExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrSB

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterativeScalingBound.main
  | exact _root_.GlobalTheory.IterativeScalingBound.main
  | (apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterativeScalingBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterativeScalingBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterativeScalingBound.main ..)

theorem isLocallyConstant_addChar {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    (ψ : AddChar G ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hU : (⇑ψ) ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : G) := by
    apply hψ.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact Metric.ball_mem_nhds _ (by norm_num)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hU
  have hker : ∀ y ∈ V, ψ y = 1 := by
    intro y hy
    apply eq_one_of_pow_two_pow
    intro k
    have hm : (2 ^ k) • y ∈ V := V.toAddSubgroup.nsmul_mem hy _
    have := hV hm
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, AddChar.map_nsmul_eq_pow] at this
    exact this
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hx : Filter.Tendsto (fun y => y - x) (nhds x) (nhds 0) := by
    have h := ((continuous_sub_right x).tendsto x)
    rwa [sub_self] at h
  filter_upwards [hx (V.isOpen.mem_nhds V.zero_mem)] with y hy
  have e : y = x + (y - x) := by abel
  rw [e, AddChar.map_add_eq_mul, hker _ hy, mul_one]

theorem continuous_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
  have h : Continuous (GlobalTheory.LatVac.liftV v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  exact hψ.comp h

theorem schr_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ GlobalTheory.WeilM.SB _ := by
  intro F _ _ κ _ ψ hψ v w φ hφ
  have hloc := isLocallyConstant_addChar _ (continuous_psiAt ψ hψ v)
  have hlin : Continuous fun x : κ → Fv F v => x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) :=
    (continuous_id.dotProduct continuous_const).add continuous_const
  refine ⟨?_, ?_⟩
  · exact (hloc.comp_continuous hlin).mul (hφ.1.comp_continuous (continuous_add_const w.1))
  · have hc : HasCompactSupport fun x : κ → Fv F v => φ (x + w.1) :=
      hφ.2.comp_homeomorph (Homeomorph.addRight w.1)
    exact hc.mul_left (f := fun x => GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)))

end GlobalTheory.SchrSB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PsiNontrivAt

theorem exists_psiAt_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1 := by
  intro F _ _ ψ hψ w
  by_contra h
  push_neg at h
  refine GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ w ?_
  ext t
  rw [h t, AddChar.one_apply]

end GlobalTheory.PsiNontrivAt
end

