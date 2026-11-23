module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.IntegralSubst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.HasSubstGood
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Assemble
section
noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

theorem good_X {σ : Type*} (i : σ) : Good (Xv (p := p) i) := by
  unfold Good
  refine ⟨by simp [PI.FglGram.Xv], ?_⟩
  unfold PI.FglGram.IntegralMv
  intro n
  unfold PI.FglGram.IsIntP
  unfold PI.FglGram.Xv
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem hP_fst {κ : Type*} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) :
    (hP x y).1 = ∑ i, (x i).1 * (y i).2 := by
  unfold hP
  rw [Prod.fst_sum]
  rfl

theorem column_of (hE : Expand) : Column := by
  intro p _ l ex ph S H k c d hcd
  have hg : ∀ j, Good (mulBy l ex (c j) (Xv j : MvPowerSeries (Fin k) ℂ_[p])) := fun j =>
    goodMul p l ex ph S H (Fin k) (c j, d j) (hcd j) _ (good_X j)
  have e : lin l ex c (fun j => (Xv j : MvPowerSeries (Fin k) ℂ_[p])) =
      pt ex (∑ j, lg l (mulBy l ex (c j) (Xv j))) := by
    unfold lin
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold mulBy
    rw [lg_pt H.data (by rw [map_mul, cc_lg H.data (cc_X _), mul_zero])]
  rw [e]
  refine sTrans (hE p l ex ph S H (Fin k) k _ hg) (sAdd ?_ ?_)
  · exact sSum _ fun j _ => normSub p l ex ph S H (Fin k) (c j, d j) (hcd j) _ (good_X j)
  · exact sSum _ fun j _ => sSum _ fun j' _ =>
      moveSub p l ex ph S H (Fin k) (c j, d j) (c j', d j') (hcd j) (hcd j') _ _ (good_X j) (good_X j')

theorem gather_of (hSF : SumFirst) : Gather := by
  intro p _ l ex ph S H hC κ _ k A hA
  have hcol : ∀ i, _root_.PI.FglGram.Simeq (phAt ph (lin l ex (fun e => (A e i).1) (fun e => (Xv e : MvPowerSeries (Fin k) ℂ_[p]))))
      (∑ j, MvPowerSeries.C ((A j i).1 * (A j i).2) * phAt ph (Xv j) +
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j')) :=
    fun i => hC k (fun j => (A j i).1) (fun j => (A j i).2) (fun j => by simpa using hA j i)
  unfold PhOn GramRhs
  refine sTrans (sSum Finset.univ fun i _ => hcol i) ?_
  rw [Finset.sum_add_distrib]
  refine sAdd (sOfEq ?_) ?_
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← map_sum, hP_fst]
  · have e1 : (∑ i, ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j') : MvPowerSeries (Fin k) ℂ_[p]) =
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), ∑ i,
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    refine sSum _ fun j _ => sSum _ fun j' _ => ?_
    have hg : ∀ i ∈ (Finset.univ : Finset κ),
        Good (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j : MvPowerSeries (Fin k) ℂ_[p])) := by
      intro i _
      rw [← mulBy_mulBy H.data _ _ (cc_X _)]
      exact goodMul p l ex ph S H (Fin k) (A j' i).swap (H.swap _ (hA j' i)) _
        (goodMul p l ex ph S H (Fin k) (A j i) (hA j i) _ (good_X j))
    have h := hSF p l ex ph S H (Fin k) κ Finset.univ (fun i => (A j' i).2 * (A j i).1) (Xv j) (Xv j')
      (good_X j) (good_X j') hg
    have e2 : (hP (A j) (A j')).1 = ∑ i, (A j' i).2 * (A j i).1 := by
      rw [hP_fst]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e2]
    exact h

theorem phGram_of_steps (hE : Expand) (hSF : SumFirst) : PI.FglGram.PhGram := by
  have hC := column_of hE
  have hG := gather_of hSF
  unfold Column at hC
  unfold Gather at hG
  unfold PI.FglGram.PhGram
  intro p _ l ex ph S hD hsw hint hadd hph hbe hbadd κ _ k A hA
  have hH : Hyps l ex ph S := Hyps.mk hD hsw hint hadd hph hbe hbadd
  exact hG p l ex ph S hH (hC p l ex ph S hH) κ k A hA

end PI.UnitaryGroupMassFormula.PhGram
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.Expand
section
noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW

open PI.FglGram PI.UnitaryGroupMassFormula.PhGram

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}

theorem cc_l (hd : Data l ex ph) : PowerSeries.constantCoeff l = 0 := by
  exact PI.UnitaryGroupMassFormula.PhGram.cc_l hd

theorem ex_l (hd : Data l ex ph) : PowerSeries.subst l ex = PowerSeries.X :=
  (PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hd.1 hd.2.1).2

theorem cc_lg (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (lg l a) = 0 := by
  exact PI.UnitaryGroupMassFormula.PhGram.cc_lg hd ha

theorem lg_pt (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    lg l (pt ex x) = x := by
  exact PI.UnitaryGroupMassFormula.PhGram.lg_pt hd hx

theorem pt_lg (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    pt ex (lg l a) = a := by
  unfold pt lg
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero (cc_l hd))
    (PowerSeries.HasSubst.of_constantCoeff_zero ha), ex_l hd,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)]

theorem pt_zero (hd : Data l ex ph) : pt ex (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero hd.1

theorem lg_zero (hd : Data l ex ph) : lg l (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero (cc_l hd)

theorem phAt_zero (hd : Data l ex ph) : phAt ph (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero hd.2.2

theorem add_pt (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (b : MvPowerSeries σ ℂ_[p]) : add l ex (pt ex x) b = pt ex (x + lg l b) := by
  unfold add
  rw [lg_pt hd hx]

theorem be_zero_left (hd : Data l ex ph) {b : MvPowerSeries σ ℂ_[p]} (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph 0 b = 0 := by
  unfold be add
  rw [lg_zero hd, zero_add, pt_lg hd hb, phAt_zero hd]
  ring

theorem mulBy_zero (hd : Data l ex ph) (a : MvPowerSeries σ ℂ_[p]) : mulBy l ex 0 a = 0 := by
  unfold mulBy
  rw [map_zero, zero_mul, pt_zero hd]

theorem mulBy_add (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (e e' : ℂ_[p]) : mulBy l ex (e + e') a = add l ex (mulBy l ex e a) (mulBy l ex e' a) := by
  unfold mulBy add
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.C e * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.C e' * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  rw [lg_pt hd h1, lg_pt hd h2, map_add (f := _), add_mul]

theorem good_zero : Good (0 : MvPowerSeries σ ℂ_[p]) := by
  exact ⟨map_zero _, fun n => by simp [_root_.PI.FglGram.IsIntP]⟩

theorem good_mulBy_sum (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {ι : Type}
    {a : MvPowerSeries σ ℂ_[p]} (ha : Good a) (s : Finset ι) (e : ι → ℂ_[p])
    (he : ∀ i ∈ s, Good (mulBy l ex (e i) a)) : Good (mulBy l ex (∑ i ∈ s, e i) a) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, mulBy_zero H.data]
    exact good_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, mulBy_add H.data ha.1]
    exact hGA p l ex ph S H σ _ _ (he i (Finset.mem_insert_self i s))
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj)))

theorem sumFirst_of (hGA : GoodAdd) (hBS : BiaddSub) : SumFirst := by
  intro p _ l ex ph S H σ ι s e a b ha hb he
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [mulBy_zero H.data, be_zero_left H.data hb.1]
    exact sRefl 0
  | insert i s hi ih =>
    have he' : ∀ j ∈ s, Good (mulBy l ex (e j) a) := fun j hj => he j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, mulBy_add H.data ha.1]
    have hY := good_mulBy_sum hGA H ha s e he'
    exact sTrans (sAdd (sRefl _) (ih he'))
      (sSymm (hBS p l ex ph S H σ _ _ b (he i (Finset.mem_insert_self i s)) hY hb))

theorem cc_sum_lg (hd : Data l ex ph) {m : ℕ} {a : Fin m → MvPowerSeries σ ℂ_[p]}
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, lg l (a j)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => cc_lg hd (ha j)

theorem pt_sum_succ (hd : Data l ex ph) {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p])
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    pt ex (∑ j, lg l (a j)) =
      add l ex (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc, ← add_pt hd (cc_sum_lg hd (fun j => ha (Fin.castSucc j)))]

theorem pt_sum_zero (hd : Data l ex ph) (a : Fin 0 → MvPowerSeries σ ℂ_[p]) :
    pt ex (∑ j, lg l (a j)) = 0 := by
  rw [Finset.univ_eq_empty, Finset.sum_empty, pt_zero hd]

theorem good_pt_sum (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {m : ℕ}
    (a : Fin m → MvPowerSeries σ ℂ_[p]) (ha : ∀ j, Good (a j)) : Good (pt ex (∑ j, lg l (a j))) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data]
    exact good_zero
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1)]
    exact hGA p l ex ph S H σ _ _ (ih (fun j => a (Fin.castSucc j)) (fun j => ha _)) (ha _)

theorem be_pt_sum (hGA : GoodAdd) (hBS : BiaddSub) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S)
    {z : MvPowerSeries σ ℂ_[p]} (hz : Good z) {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p])
    (ha : ∀ j, Good (a j)) : _root_.PI.FglGram.Simeq (be l ex ph (pt ex (∑ j, lg l (a j))) z) (∑ j, be l ex ph (a j) z) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data, be_zero_left H.data hz.1, Finset.univ_eq_empty, Finset.sum_empty]
    exact sRefl 0
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1), Fin.sum_univ_castSucc]
    have hX := good_pt_sum hGA H (fun j => a (Fin.castSucc j)) (fun j => ha _)
    exact sTrans (hBS p l ex ph S H σ _ _ z hX (ha _) hz)
      (sAdd (ih (fun j => a (Fin.castSucc j)) (fun j => ha _)) (sRefl _))

def rhsBy (l ex ph : PowerSeries ℂ_[p]) {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ j', (phAt ph (a j') + ∑ j, if j < j' then be l ex ph (a j) (a j') else 0)

theorem rhsBy_succ {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = rhsBy l ex ph (fun j : Fin m => a (Fin.castSucc j)) +
      (phAt ph (a (Fin.last m)) + ∑ j : Fin m, be l ex ph (a (Fin.castSucc j)) (a (Fin.last m))) := by
  unfold rhsBy
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_castSucc_iff, (Fin.castSucc_lt_last k).asymm]
  · rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_last]

theorem ph_pt_sum (hGA : GoodAdd) (hBS : BiaddSub) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S)
    {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) (ha : ∀ j, Good (a j)) :
    _root_.PI.FglGram.Simeq (phAt ph (pt ex (∑ j, lg l (a j)))) (rhsBy l ex ph a) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data, phAt_zero H.data]
    unfold rhsBy
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact sRefl 0
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1), rhsBy_succ]
    have e : phAt ph (add l ex (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m))) =
        phAt ph (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) + (phAt ph (a (Fin.last m)) +
          be l ex ph (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m))) := by
      unfold be
      ring
    rw [e]
    exact sAdd (ih (fun j => a (Fin.castSucc j)) (fun j => ha _))
      (sAdd (sRefl _) (be_pt_sum hGA hBS H (ha _) (fun j => a (Fin.castSucc j)) (fun j => ha _)))

theorem rhsBy_eq {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = ∑ j, phAt ph (a j) +
      ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (a j) (a j') := by
  unfold rhsBy
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j' j => if j < j' then be l ex ph (a j) (a j') else 0)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]

theorem expand_of (hGA : GoodAdd) (hBS : BiaddSub) : Expand := by
  intro p _ l ex ph S H σ m a ha
  rw [← rhsBy_eq]
  exact ph_pt_sum hGA hBS H a ha

end PI.UnitaryGroupMassFormula.PhGram.ExpandW

namespace PI.UnitaryGroupMassFormula.PhGram

theorem expand_of (hGA : GoodAdd) (hBS : BiaddSub) : Expand := ExpandW.expand_of hGA hBS

theorem sumFirst_of (hGA : GoodAdd) (hBS : BiaddSub) : SumFirst := ExpandW.sumFirst_of hGA hBS

theorem gram_bilinear_expansion : Expand := expand_of goodAdd biaddSub

theorem gram_sum_first_variable : SumFirst := sumFirst_of goodAdd biaddSub

end PI.UnitaryGroupMassFormula.PhGram
end
end

