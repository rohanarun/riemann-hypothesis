module

public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0017
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
section
noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def RowData.rk (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rk g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rk g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rk (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rk g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rk g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rk g a) (e a)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rk g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

structure WtHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (bgr : ZMod (N.ordP l) → Fin 2)
    (rk : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ)
    (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (N.R.k - 1) = alongOrb N l z W a + alongOrb N l z exc a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (N.R.k - 1) (ga z) N.R.r : ℝ) +
    ∑ a, ((N.R.k : ℝ) - 1) * ((alongOrb N l z exc a : ℕ) : ℝ))

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerate
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Agr

variable {C : Type} [Field C]

def Agr {τ : Type} (k : ℕ) (f g : MvPowerSeries τ C) : Prop :=
  ∀ e : τ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g

theorem Agr.symm {τ : Type} {k : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) : Agr k g f :=
  fun e he => (h e he).symm

theorem Agr.trans {τ : Type} {k : ℕ} {f g g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k g g') : Agr k f g' :=
  fun e he => (h e he).trans (h' e he)

theorem Agr.add {τ : Type} {k : ℕ} {f g f' g' : MvPowerSeries τ C} (h : Agr k f g) (h' : Agr k f' g') :
    Agr k (f + f') (g + g') := fun e he => by rw [map_add (f := _), map_add (f := _), h e he, h' e he]

theorem agr_iff_trunc {τ : Type} [Finite τ] (k : ℕ) (f g : MvPowerSeries τ C) :
    Agr k f g ↔ MvPowerSeries.truncTotal k f = MvPowerSeries.truncTotal k g := by
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with he
    · exact h e he
    · rfl
  · intro h e he
    have h2 := congrArg (AddMonoidAlgebra.coeff · e) h
    rwa [MvPowerSeries.coeff_truncTotal _ he, MvPowerSeries.coeff_truncTotal _ he] at h2

theorem agr_subst_left {σ τ : Type} [Finite σ] [Finite τ] {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    {k : ℕ} (h : ∀ s, Agr k (a s) (b s)) (f : MvPowerSeries σ C) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst b f) := by
  have h' : ∀ s, MvPowerSeries.truncTotal k (a s) = MvPowerSeries.truncTotal k (b s) :=
    fun s => (agr_iff_trunc k _ _).1 (h s)
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst hb]
  simp only [h']

theorem agr_subst_right {σ τ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {k : ℕ} {f g : MvPowerSeries σ C} (h : Agr k f g) :
    Agr k (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  rw [agr_iff_trunc, MvPowerSeries.truncTotal_subst ha, MvPowerSeries.truncTotal_subst ha,
    (agr_iff_trunc k f g).1 h]

end Agr

section Wit

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def RawChart.TyWit (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C) : Prop :=
  IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0

theorem RawChart.mem_tySet_iff (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) :
    x ∈ X.TySet V g ↔ ∃ γ lam, X.TyWit V g x γ lam := Iff.rfl

end Wit

section MM

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero]
  exact WithTop.coe_lt_top 0

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_mul_ge {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_sum {ι : Type} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact mm_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end MM

section Step2

variable {C : Type} [Field C]

theorem Agr.mono {τ : Type} {k k' : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) (hk : k' ≤ k) : Agr k' f g :=
  fun e he => h e (lt_of_lt_of_le he hk)

theorem const_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {γ : PowerSeries C}
    (hγ : PowerSeries.constantCoeff γ = 0) : MvPowerSeries.constantCoeff (cvAt s γ) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs) (fun _ => hs) hγ

theorem subst_cvAt {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) {σ : Type} [Finite σ]
    {γ : σ → PowerSeries C} (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (F : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun j => cvAt s (γ j)) F = cvAt s (MvPowerSeries.subst γ F) := by
  unfold cvAt
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hs)]

theorem cvAt_smul_X {s : MvPowerSeries (Fin 2) C} (hs : MvPowerSeries.constantCoeff s = 0) (c : C) :
    cvAt s (c • (MvPowerSeries.X () : PowerSeries C)) = c • s := by
  unfold cvAt
  have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero (σ := Unit) fun _ => hs
  rw [MvPowerSeries.subst_smul hS, MvPowerSeries.subst_X hS]

theorem eval_points_two {dd : ℕ} (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  unfold ev
  have e : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      fun q => (MvPowerSeries.X q : PS C 2 dd) := by
    funext ⟨k, j⟩
    fin_cases k <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem tyS_good_coeff {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (hl : 2 ≤ V.l) (c : I g) (n : ℕ)
    (hn : n < V.l ^ 2) :
    PowerSeries.coeff n (tyS V.l (fun s => x s (Sum.inl c))) = if n = 1 then w c else 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · rw [pow_zero]
    by_cases hn1 : n = 1
    · subst hn1
      rw [if_pos rfl, if_pos rfl]
      simp [h0]
    · have hn1' : ¬ (1 = n) := fun h => hn1 h.symm
      rw [if_neg hn1', if_neg hn1]
  · intro s _ hs0
    by_cases hs1 : s = 1
    · subst hs1
      simp [h1 c]
    · rw [if_neg]
      intro hsn
      have h2 : 2 ≤ s := by omega
      have h3 : V.l ^ 2 ≤ V.l ^ s := Nat.pow_le_pow_right (by omega) h2
      rw [hsn] at h3
      exact absurd hn (not_lt.mpr h3)
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h

theorem coeffX' (n : ℕ) : PowerSeries.coeff n (MvPowerSeries.X () : PowerSeries C) = if n = 1 then 1 else 0 :=
  PowerSeries.coeff_X n

theorem lg_addOf (Y : FBChart C V O dd) {τ : Type} (P : Fin 2 → Fin dd → MvPowerSeries τ C)
    (hP : ∀ k j, MvPowerSeries.constantCoeff (P k j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j))
        (un1 (Y.lg i)) =
      MvPowerSeries.subst (P 0) (un1 (Y.lg i)) + MvPowerSeries.subst (P 1) (un1 (Y.lg i)) := by
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => P q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP q.1 q.2
  have hF0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP q.1 q.2) (Y.B.G.const j)
  rw [subst_singlePointUncurry hF0, subst_singlePointUncurry (hP 0), subst_singlePointUncurry (hP 1)]
  have key := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2)) (Y.lg_add i)
  have hadd : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext j
    exact eval_points_two (Y.B.G.F j)
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.G.F q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => Y.B.G.const q.2
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => pt C (n := 2) dd k q.2) :=
    fun k => MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  rw [hadd, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst, MvPowerSeries.subst_add hPP,
    MvPowerSeries.subst_comp_subst_apply hA hPP, MvPowerSeries.subst_comp_subst_apply (hX 0) hPP,
    MvPowerSeries.subst_comp_subst_apply (hX 1) hPP] at key
  simp only [pt, MvPowerSeries.subst_X hPP] at key
  exact key

end Step2

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section IntSec

variable {V : VF C} {τ : Type}

theorem IntS.mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  refine VF.Ge.sum fun p _ => ?_
  have hp := (hf p.1).mul (hg p.2)
  simpa using hp

theorem IntS.one : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [MvPowerSeries.coeff_one]
  split_ifs
  all_goals simp [VF.Ge]

theorem IntS.pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IntS.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem IntS.subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  intro μ
  rw [MvPowerSeries.coeff_subst hA]
  have hterm : ∀ d : σ →₀ ℕ,
      V.Ge 0 (MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)) := by
    intro d
    have hp : IntS V (d.prod fun s e => a s ^ e) := by
      show IntS V (∏ s ∈ d.support, a s ^ d s)
      exact Finset.prod_induction _ (fun p => IntS V p) (fun _ _ hx hy => IntS.mul hx hy) IntS.one
        (fun s _ => IntS.pow (ha s) _)
    have h2 := (hf d).mul (hp μ)
    simpa [smul_eq_mul] using h2
  by_cases hfin : (Function.support fun d : σ →₀ ℕ =>
      MvPowerSeries.coeff d f • MvPowerSeries.coeff μ (d.prod fun s e => a s ^ e)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact VF.Ge.sum fun d _ => hterm d
  · rw [finsum_of_infinite_support hfin]
    simp [VF.Ge]

theorem intS_ps {f : PowerSeries C} : IntS V f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    have hμ : μ = Finsupp.single () (μ ()) := by
      ext
      simp [Finsupp.single_apply]
    rw [hμ]
    exact h (μ ())

end IntSec

section Kill

variable {dd : ℕ}

theorem subst_ev_kill (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) :
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) (ev a h) =
      MvPowerSeries.rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
  have hbS : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => (MvPowerSeries.X (1 - g, q.2) : PS C 2 dd)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  have haS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact MvPowerSeries.constantCoeff_X _
  unfold ev
  rw [MvPowerSeries.subst_comp_subst_apply haS hbS, MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  by_cases hs : s.1 = g
  · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
    rw [h1, ← MvPowerSeries.coe_substAlgHom hbS, map_zero]
    simp [hs]
  · have h1 : a s.1 s.2 = MvPowerSeries.X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
    rw [h1, MvPowerSeries.subst_X hbS]
    have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
    simp only [Pi.smul_apply', if_neg hs, one_smul]
    rw [← h2]

theorem coeff_eval_second_zero (G : PS C 2 dd) (μ : Fin dd →₀ ℕ) :
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (ev (n := 1) ![pt C dd 0, 0] G) =
      MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)) G := by
  have hk := subst_ev_kill G 1 ![pt C dd 0, 0] rfl (by
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl)
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) :=
    fun a b h => snd_injective_fin_one (Prod.mk.inj (show (((1 : Fin 2) - 1, a.2) : Fin 2 × Fin dd) = ((1 : Fin 2) - 1, b.2) from h)).2
  have h1 := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) hinj
    (ev (n := 1) ![pt C dd 0, 0] G) (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  rw [hk, ← Finsupp.mapDomain_comp, MvPowerSeries.coeff_rescale] at h1
  rw [← h1]
  have h2 : ((fun q : Fin 1 × Fin dd => (((1 : Fin 2) - 1, q.2) : Fin 2 × Fin dd)) ∘ fun x : Fin dd => ((0 : Fin 1), x)) =
      fun x : Fin dd => ((0 : Fin 2), x) := by
    funext x
    rfl
  rw [h2]
  have h3 : ((μ.mapDomain fun x : Fin dd => ((0 : Fin 2), x)).prod
      fun s m => (if s.1 = 1 then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    have hs' := Finsupp.mapDomain_support hs
    rw [Finset.mem_image] at hs'
    obtain ⟨x, _, rfl⟩ := hs'
    show (if (0 : Fin 2) = 1 then (0 : C) else 1) ^ _ = 1
    rw [if_neg (by decide), one_pow]
  rw [h3, one_mul]

end Kill

section SgSec

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end SgSec

section AddSec

variable {dd : ℕ}

theorem pts_eq_X : (fun p : Fin 2 × Fin dd => ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] p.1 p.2) = MvPowerSeries.X := by
  funext p
  rcases p with ⟨i, j⟩
  fin_cases i <;> first | rfl | simp [pt]

theorem addOf_pts (F : Fin dd → PS C 2 dd) (j : Fin dd) :
    addOf F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j = F j := by
  simp only [addOf, ev]
  rw [pts_eq_X, MvPowerSeries.subst_self]
  rfl

end AddSec

end Formalism.L2.FormalSeriesBounds
end
end

