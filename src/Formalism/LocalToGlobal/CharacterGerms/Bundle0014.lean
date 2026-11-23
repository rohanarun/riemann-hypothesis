module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0065
public import Formalism.LocalToGlobal.CharacterGerms.PlugUP
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0008
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieDesc
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

section Chart

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartDerivativeCoefficient (C3 : IntChart T io y) (k n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  nabValN (a3B C3) T.Fr (a3h C3) H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) P

theorem nuLocC_le_nval (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by
  unfold nuLocC chartDerivativeCoefficient
  exact le_trans (iInf₂_le P hP) (iInf₂_le f hf)

end Chart

section Val

variable {C : Type} [Field C] {V : VF C}

theorem le_v_sum (x : WithTop ℝ) {m : ℕ} (z : Fin m → C) (h : ∀ i, x ≤ V.v (z i)) : x ≤ V.v (∑ i, z i) := by
  refine Finset.sum_induction z (fun w => x ≤ V.v w)
    (fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)) ?_ (fun i _ => h i)
  rw [AddValuation.map_zero]
  exact le_top

end Val

variable (Xo c)

def NabMapSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C)
    (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr),
      Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι f) (MvPolynomial.map ι P) = ι (chartDerivativeCoefficient C3 k n f P)

def DescSpanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P ∈ (chartLetterSystem C3 V ι a).FF n, ∀ f : PS C n (chD C3.ch), IntS V f →
      ∃ (m : ℕ) (r : Fin m → C) (Pi : Fin m → MvPolynomial (LtN Dw n) T.Fr) (fi : Fin m → PS T.Fr n (chD C3.ch)),
        (∀ i, V.Ge 0 (r i)) ∧ (∀ i, Pi i ∈ FFV (Dw := Dw) T a n) ∧ (∀ i, IsIntPS T (fi i)) ∧
        Y.nab (chartLetterSystem C3 V ι a) n f P =
          ∑ i, r i * Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i))

def NvalEqSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ x : T.Fr, (WithBot.some (V.v (ι x)) : WithBot (WithTop ℝ)) = nval T.V (eOf T V) x

variable {Xo c}

theorem descent_of (h1 : NabMapSt Xo c) (h2 : DescSpanSt Xo c) (h3 : NvalEqSt) : DescentSt Xo c := by
  intro T io y C3 C _ _ V ι hι k Y hY a n
  unfold FBChart.nuPlE
  refine le_iInf₂ fun x hx => ?_
  obtain ⟨P, hP, f, hf, rfl⟩ := hx
  obtain ⟨m, r, Pi, fi, hr, hPi, hfi, heq⟩ := h2 T io y C3 C V ι hι k Y hY a n P hP f hf
  have hz : ∀ i, nuLocC C3 (eOf T V) k a n ≤ (WithBot.some (V.v (Y.nab (chartLetterSystem C3 V ι a) n
      (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i)))) : WithBot (WithTop ℝ)) := by
    intro i
    rw [h1 T io y C3 C V ι k Y hY a n (fi i) (Pi i), h3 T C V ι hι]
    exact nuLocC_le_nval C3 (eOf T V) k a n (Pi i) (hPi i) (fi i) (hfi i)
  rw [heq]
  generalize nuLocC C3 (eOf T V) k a n = ν at hz ⊢
  rcases ν with _ | w
  · exact bot_le
  · refine WithBot.coe_le_coe.mpr (le_v_sum w _ fun i => ?_)
    have hzi := WithBot.coe_le_coe.mp (hz i)
    rw [AddValuation.map_mul]
    calc w = 0 + w := (zero_add w).symm
      _ ≤ V.v (r i) + _ := add_le_add (hr i) hzi

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem van_sum {τ ι : Type} {T : Set τ} (s : Finset ι) (f : ι → MvPowerSeries τ C) (hf : ∀ i ∈ s, Van T (f i)) :
    Van T (∑ i ∈ s, f i) := by
  intro ν hν
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero (fun i hi => hf i hi ν hν)

theorem van_X {τ : Type} {T : Set τ} {q : τ} (hq : q ∈ T) : Van T (X q : MvPowerSeries τ C) := by
  intro ν hν
  rw [MvPowerSeries.coeff_X]
  split_ifs with h
  · exfalso
    exact hν q (by rw [h]; simp) hq
  · rfl

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem constantCoeff_inCol (col : Fin 2) (f : MvPowerSeries (Fin dd) C) (hf : constantCoeff f = 0) :
    constantCoeff (inCol col f) = 0 := by
  have hb : MvPowerSeries.HasSubst
      (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  unfold inCol
  rw [MvPowerSeries.constantCoeff_subst hb, finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => (MvPowerSeries.X (col, s) : MvPowerSeries (Fin 2 × Fin dd) C) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hi]
    rw [h0, smul_zero]

theorem van_hCol (col g : Fin 2) (h : PS C 2 dd)
    (hh : ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0) :
    Van {w : Fin 2 × (Fin 2 × Fin dd) | w.1 = g} (hCol col h) := by
  unfold hCol
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = g} (fun _ => constantCoeff_X _) ?_ ?_
  · intro s hs
    exact van_X hs
  · intro e he
    exact hh e he

theorem gauge_axes (Y : FBChart C V O dd) (g : Fin 2) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0 := by
  fin_cases g
  · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
    rfl
  · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
    intro g' hg'
    rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
    rfl

theorem axesSelf_holds : AxesSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
    apply constantCoeff_inCol
    rw [constantCoeff_uncurry]
    exact Y.ex_const x.2
  · intro g e he
    show coeff e (∑ col, hCol col Y.h) = 0
    exact van_sum Finset.univ _ (fun col _ => van_hCol col g Y.h (gauge_axes Y g)) e he

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallCv
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Bd

variable {C : Type} [Field C] {V : VF C}

def Bdd (V : VF C) (s : ℕ → C) : Prop := ∃ K : ℝ, ∀ n, V.Ge K (s n)

theorem bdd_const (x : C) : Bdd V (fun _ => x) := by
  obtain ⟨K, hK⟩ := exists_ge (V := V) x
  exact ⟨K, fun _ => hK⟩

theorem Bdd.add {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n + t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨min K L, fun n => ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))⟩

theorem Bdd.mul {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n * t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨K + L, fun n => (hK n).mul (hL n)⟩

theorem Bdd.sum {ι : Type} (S : Finset ι) {s : ι → ℕ → C} (h : ∀ i ∈ S, Bdd V (s i)) :
    Bdd V (fun n => ∑ i ∈ S, s i n) := by
  first | exact GlobalTheory.ScalarStatement.main .. | (apply GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply @GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> first | assumption | infer_instance) | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s h | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι | exact @GlobalTheory.ScalarStatement.main C ‹_› V | exact @GlobalTheory.ScalarStatement.main C ‹_› | exact @GlobalTheory.ScalarStatement.main C

theorem tends_mul_bdd {s t : ℕ → C} (hs : Bdd V s) (ht : Tends V t 0) : Tends V (fun n => s n * t n) 0 := by
  intro w
  obtain ⟨K, hK⟩ := hs
  obtain ⟨n0, h0⟩ := ht (w - K)
  refine ⟨n0, fun n hn => ?_⟩
  have h := (hK n).mul (h0 n hn)
  have e : (0 : C) - s n * t n = s n * (0 - t n) := by ring
  rw [e]
  exact h.mono (by linarith)

variable {σ : Type}

def BddS (V : VF C) (f : ℕ → MvPowerSeries σ C) : Prop := ∀ μ, Bdd V (fun n => coeff μ (f n))

theorem BddS.const (g : MvPowerSeries σ C) : BddS V (fun _ => g) := fun _ => bdd_const _

theorem BddS.of_int {f : ℕ → MvPowerSeries σ C} (h : ∀ n, IntS V (f n)) : BddS V f :=
  fun μ => ⟨0, fun n => h n μ⟩

theorem BddS.mul {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : BddS V g) :
    BddS V (fun n => f n * g n) := fun μ => by
  classical
  simp only [coeff_mul]
  exact Bdd.sum _ fun p _ => (hf p.1).mul (hg p.2)

theorem BddS.pow {f : ℕ → MvPowerSeries σ C} (hf : BddS V f) (k : ℕ) : BddS V (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using BddS.const (V := V) (1 : MvPowerSeries σ C)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem BddS.prod {ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} (h : ∀ i ∈ S, BddS V (f i)) :
    BddS V (fun n => ∏ i ∈ S, f i n) := by
  first | exact UpperTheory.Reformulated.B.BoundedSums.prod .. | (apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f h | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› | exact @UpperTheory.Reformulated.B.BoundedSums.prod C

theorem BddS.fprod {ι : Type} (d : ι →₀ ℕ) {a : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i)) :
    BddS V (fun n => d.prod fun i e => a n i ^ e) := by
  unfold Finsupp.prod
  exact BddS.prod _ fun i _ => (ha i).pow _

theorem BddS.subst [Finite σ] {τ : Type} {a : ℕ → σ → MvPowerSeries τ C} {f : ℕ → MvPowerSeries σ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (ha : ∀ s, BddS V (fun n => a n s)) (hf : BddS V f) :
    BddS V (fun n => MvPowerSeries.subst (a n) (f n)) := fun μ => by
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) (f n))) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d (f n) * coeff μ (d.prod fun s e => a n s ^ e) :=
    funext fun n => coeff_subst_eq_sum (ha0 n) _ _
  rw [e]
  exact Bdd.sum _ fun d _ => (hf d).mul (BddS.fprod d ha μ)

theorem TendsS.mul_bdd {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : TendsS V g 0) :
    TendsS V (fun n => f n * g n) 0 := fun μ => by
  classical
  show Tends V (fun n => coeff μ (f n * g n)) (coeff μ 0)
  simp only [coeff_mul, map_zero]
  have h := Tends.sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (s := fun p n => coeff p.1 (f n) * coeff p.2 (g n)) (x := fun _ => 0)
    fun p _ => tends_mul_bdd (hf p.1) (by simpa using hg p.2)
  simpa using h

def Close (V : VF C) (f g : ℕ → MvPowerSeries σ C) : Prop := TendsS V (fun n => f n - g n) 0

theorem Close.refl (f : ℕ → MvPowerSeries σ C) : Close V f f := by
  unfold Close
  simpa using TendsS.const (V := V) (0 : MvPowerSeries σ C)

theorem Close.mul {a a' b b' : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb' : BddS V b') (h1 : Close V a b)
    (h2 : Close V a' b') : Close V (fun n => a n * a' n) (fun n => b n * b' n) := by
  have e : (fun n => a n * a' n - b n * b' n) = fun n => a n * (a' n - b' n) + b' n * (a n - b n) :=
    funext fun n => by ring
  unfold Close
  rw [e]
  simpa using (TendsS.mul_bdd ha h2).add (TendsS.mul_bdd hb' h1)

theorem Close.pow {a b : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb : BddS V b) (h : Close V a b) (k : ℕ) :
    Close V (fun n => a n ^ k) (fun n => b n ^ k) := by
  induction k with
  | zero => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | succ k ih => simpa only [pow_succ] using Close.mul (ha.pow k) hb ih h

theorem Close.prod {ι : Type} (S : Finset ι) {a b : ι → ℕ → MvPowerSeries σ C} (ha : ∀ i ∈ S, BddS V (a i))
    (hb : ∀ i ∈ S, BddS V (b i)) (h : ∀ i ∈ S, Close V (a i) (b i)) :
    Close V (fun n => ∏ i ∈ S, a i n) (fun n => ∏ i ∈ S, b i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | insert x S hx ih =>
    simp only [Finset.prod_insert hx]
    exact Close.mul (ha x (Finset.mem_insert_self x S)) (BddS.prod S fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (h x (Finset.mem_insert_self x S))
      (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Close.fprod {ι : Type} (d : ι →₀ ℕ) {a b : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i))
    (hb : ∀ i, BddS V (fun n => b n i)) (h : ∀ i, Close V (fun n => a n i) (fun n => b n i)) :
    Close V (fun n => d.prod fun i e => a n i ^ e) (fun n => d.prod fun i e => b n i ^ e) := by
  unfold Finsupp.prod
  exact Close.prod _ (fun i _ => (ha i).pow _) (fun i _ => (hb i).pow _) fun i _ => Close.pow (ha i) (hb i) (h i) _

theorem Close.subst [Finite σ] {τ : Type} {a b : ℕ → σ → MvPowerSeries τ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (hb0 : ∀ n s, constantCoeff (b n s) = 0)
    (ha : ∀ s, BddS V (fun n => a n s)) (hb : ∀ s, BddS V (fun n => b n s))
    (h : ∀ s, Close V (fun n => a n s) (fun n => b n s)) (f : MvPowerSeries σ C) :
    Close V (fun n => MvPowerSeries.subst (a n) f) (fun n => MvPowerSeries.subst (b n) f) := fun μ => by
  show Tends V (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) (coeff μ 0)
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)) := funext fun n => by
    rw [map_sub, coeff_subst_eq_sum (ha0 n), coeff_subst_eq_sum (hb0 n), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [map_sub, mul_sub]
  rw [e, map_zero]
  have h2 := Tends.sum (V := V) (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset
    (s := fun d n => coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)))
    (x := fun _ => 0) fun d _ => by
      have h3 := (tends_const (V := V) (coeff d f)).mul (Close.fprod d ha hb h μ)
      simpa using h3
  simpa using h2

end Bd

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieTop
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm

section CH

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

variable {C : Type} [Field C]

end CH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Rank

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp := by
  refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.1 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)
  · intro g a hb
    simp only [FBChart.raw, pairOfLab]
    convert
      (card_sigma_fst (fun b => Dw.mult (lab.tau o g b)) a).trans ((hr o).2.2 g a hb)
      using 2
    exact Finset.filter_congr (fun _ _ => Iff.rfl)

end Rank

section Named

variable (Xo c)

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

end Top

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.ValBlocksCChart
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

section Gen

variable {d : ℕ} [NeZero d] (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

abbrev rdS (o : Orb) : RowData C V d (fun _ => I0 o) (JJ fun _ => I0 o) := (Y.rawSelf (p o)).rowData (H o)

def imgFamS {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : Set (∀ o, MvPolynomial (Fin N × WV fun _ => I0 o) C) :=
  {Po | ∃ P ∈ Ls.FF n, IsImgS (fun o => Y.rawSelf (p o)) pl (Ls.cp n) (Ls.uv n) P (∏ o, toAll o (Po o))}

theorem valO_self (ν : ℝ) (hν : (ν : EReal) ≤ Y.nuPlE Ls n) (hs : SelfSep Y p) (hv : ValEqSelfSt Y p H Ls n)
    {N : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) : ValO (fun o => rdS Y p H o) N (imgFamS Y p Ls n pl) ν := by
  rintro Po ⟨P, hP, hQ⟩ kind hk S t ht gr hg
  have key := val_self (hs := hs) (hv := hv) (N := N) (pl := pl) (P := P) (hP := hP) (Po := Po) (hQ := hQ)
    (kind := kind) (hk := hk) (S := S) (t := t) (ht := ht) (gr := gr) (hg := hg)
  exact WithBot.coe_le_coe.1 (hν.trans key)

end Gen

section Two

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y 2 (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
  (Ls : LetSys C dd) (n : ℕ)

end Two

end Formalism.L2.FormalSeriesBounds.RF
end
end

