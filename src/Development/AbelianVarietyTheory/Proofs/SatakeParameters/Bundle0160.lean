module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
section
namespace GlobalTheory.ColPeriod

open _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingIsGoodCyclotomicInvariantReferenceLatti
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod

section Unfold

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem good_om_two {N' N : ℕ} {e' e : ℕ → ℤ} {Φ : HomE E N' N → K}
    (h : Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e)) Φ) (cq sq : K)
    (χ₀ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {g : Sp E N' ≃ₗ[E] Sp E N'} (hg : g ∈ stabL E N' (LocE.sclLat P (qOf P) N' e'))
    {k : Sp E N ≃ₗ[E] Sp E N} (hk : k ∈ stabL E N (LocE.sclLat P (qOf P) N e)) :
    Good P (homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
      (Loc.om (LocE.locChar (qOf P) cq χ₀) (LocE.vP P (qOf P)) sq g k Φ) := by
  have hu := isUnit_det_of_stab hg
  have h1 := isUnit_det_of_stab hk
  unfold Loc.om
  rw [locChar_unit _ _ hu, locChar_unit _ _ h1, vP_unit hu, vP_unit h1]
  refine Good.const_mul (h.comp (H' := homS (LocE.sclLat P (qOf P) N' e') (LocE.sclLat P (qOf P) N e))
    (fun x => k.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)
    (fun x z => ?_) fun w => ⟨fun hw y hy => (inv_mem hk _).2 (hw _ ((hg y).2 hy)), fun hw y hy => ?_⟩) ?_
  · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul]
  · have := hw (g.symm y) ((hg _).1 (by simpa using hy))
    rw [← g.apply_symm_apply y]
    exact (inv_mem hk _).1 this
  · simp only [neg_zero, zero_mul, zpow_zero, mul_one]
    exact mul_mem (unitV_mem _ _) (unitV_inv_mem _ _)

omit [NumberField E] [StarRing E] in
theorem freeCoordinateExtension_apply_single {n' c' n c : ℕ} (xj : HomE E n' n) (t : Loc.FC n' c' n c → E) (l : Fin (n + c)) (s : Fin (n' + c')) :
    Loc.xx1 xj t (Pi.single s 1) l =
      if hf : Loc.IsFree n' n c l.1 s.1 then t ⟨(l, s), hf⟩
      else if hs : s.1 < n' then (if hl : l.1 < n then xj (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0)
      else if l.1 = n + (s.1 - n') then 1 else 0 := by
  unfold Loc.xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply, LinearMap.toMatrix'_apply]

theorem intAt_zpow {z : ℤ} (hz : 0 ≤ z) : IntAt P ((qOf P : E) ^ z) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  rw [zpow_natCast]
  exact intAt_pow (intAt_nat _) _

theorem mem_homS_std {a b : ℕ} {x : HomE E a b} :
    x ∈ homS (stdAt E a P) (stdAt E b P) ↔ ∀ l s, IntAt P (x (Pi.single s 1) l) := by
  refine ⟨fun h l s => mem_stdAt.1 (h _ (single_mem_stdAt s)) l, fun h y hy => mem_stdAt.2 fun l => ?_⟩
  rw [apply_eq_sum]
  exact intAt_sum _ fun j _ => (mem_stdAt.1 hy j).mul (h l j)

theorem standardLattice_restriction_of_freeExtension_mem {n' c' n c : ℕ} {ex' ex : ℕ → ℕ} {xj : HomE E n' n} {t : Loc.FC n' c' n c → E}
    (h : Loc.xx1 xj t ∈ homS (LocE.lamY P (qOf P) n' c' ex') (LocE.lamY P (qOf P) n c ex)) :
    xj ∈ homS (stdAt E n' P) (stdAt E n P) := by
  refine mem_homS_std.2 fun l s => ?_
  have h1 := mem_homS_sclLat.1 h (Fin.castAdd c l) (Fin.castAdd c' s)
  have hs : (Fin.castAdd c' s).1 < n' := s.2
  have hl : (Fin.castAdd c l).1 < n := l.2
  rw [freeCoordinateExtension_apply_single, dite_eq_right (fun hf => absurd hf.1 (by omega)), dite_eq_left hs, dite_eq_left hl] at h1
  simpa [LocE.scE] using h1

theorem chArg_int {n' c' n c : ℕ} {x : HomE E (n' + c') (n + c)}
    (h : x ∈ homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) :
    IntAt P ((qOf P : E) * (-Loc.chArg x)) := by
  rw [mul_neg]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      have h3 := mem_homS_sclLat.1 h ⟨_, h1⟩ ⟨_, h2⟩
      have e : LocE.scE n' (fun i => i + 1) (n' + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
        unfold LocE.scE
        rw [if_neg (by omega), if_neg (by omega)]
        dsimp only
        omega
      rw [e, zpow_one, mul_comm] at h3
      exact h3
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

omit [StarRing E] in
theorem chArg_sub_int {n' c' n c : ℕ} {x x' : HomE E (n' + c') (n + c)}
    (h : ∀ l s, IntAt P (x' (Pi.single s 1) l - x (Pi.single s 1) l)) : IntAt P (Loc.chArg x - Loc.chArg x') := by
  rw [← neg_sub]
  refine intAt_neg ?_
  unfold Loc.chArg
  rw [← Finset.sum_sub_distrib]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h1
  · by_cases h2 : n' + i + 1 < n' + c'
    · rw [eN_eq h2]
      exact h _ _
    · rw [eN_of_not h2]
      simpa using intAt_zero
  · simpa using intAt_zero

theorem integrand_congr {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    {xj xj' : HomE E n' n} {t t' : Loc.FC n' c' n c → E}
    (hx : ∀ l s, IntAt P ((qOf P : E)⁻¹ * (xj' (Pi.single s 1) l - xj (Pi.single s 1) l))) (ht : ∀ p, IntAt P (t' p - t p)) :
    Φ (Loc.xx1 xj' t') * psi (-Loc.chArg (Loc.xx1 xj' t')) = Φ (Loc.xx1 xj t) * psi (-Loc.chArg (Loc.xx1 xj t)) := by
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have h1 : (qOf P : E)⁻¹ • (Loc.xx1 xj' t' - Loc.xx1 xj t) ∈
      homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1) := by
    refine mem_homS_sclLat.2 fun l s => ?_
    rw [LinearMap.smul_apply, LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · have hl := l.2
      have e : 0 ≤ LocE.scE n' (fun i => i + 1) s.1 - LocE.scE n (fun i => i + 1) l.1 - 1 := by
        unfold LocE.scE
        unfold Loc.IsFree at hf
        dsimp only
        split_ifs <;> omega
      convert (ht ⟨(l, s), hf⟩).mul (intAt_zpow e) using 1
      rw [zpow_sub_one₀ hq]
      ring
    · simpa [LocE.scE, hs, hl] using hx _ _
    all_goals simpa using intAt_zero
  have h2 : ∀ l s, IntAt P (Loc.xx1 xj' t' (Pi.single s 1) l - Loc.xx1 xj t (Pi.single s 1) l) := fun l s => by
    rw [freeCoordinateExtension_apply_single, freeCoordinateExtension_apply_single]
    split_ifs with hf hs hl h4
    · exact ht _
    · have := (intAt_nat (qOf P)).mul (hx ⟨l.1, hl⟩ ⟨s.1, hs⟩)
      rwa [mul_inv_cancel_left₀ hq] at this
    all_goals simpa using intAt_zero
  have h3 := h.2.1 (Loc.xx1 xj t) _ h1
  rw [smul_inv_smul₀ hq, add_sub_cancel] at h3
  rw [h3]
  by_cases h0 : Φ (Loc.xx1 xj t) = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [← hpsi _ _ (chArg_int (h.1 _ h0)) (chArg_sub_int h2)]
    congr 2
    ring

theorem unfolding_isGoodCyclotomicInvariant_referenceLattices [CharZero K] {n' c' n c : ℕ} {Φ : HomE E (n' + c') (n + c) → K}
    (h : Good P (homS (LocE.lamY P (qOf P) n' c' fun i => i + 1) (LocE.lamY P (qOf P) n c fun i => i + 1)) Φ)
    {psi : E → K} (hpsi : ∀ a b, IntAt P ((qOf P : E) * a) → IntAt P b → psi (a + b) = psi a)
    (hmem : ∀ a, IntAt P ((qOf P : E) * a) → psi a ∈ Zmu K (qOf P)) (A B : ℕ) :
    Good P (homS (stdAt E n' P) (stdAt E n P)) (Loc.E1 psi (LocE.valsQ E (qOf P) A B) (((qOf P : K) ^ B)⁻¹) Φ) := by
  classical
  have hq : (qOf P : E) ≠ 0 := qOf_ne_zero
  have hqK : (qOf P : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.cast_ne_zero.1 hq)
  refine ⟨fun x hx => ?_, fun x z hz => ?_, fun x => ?_⟩
  · obtain ⟨t, -, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hx)
    exact standardLattice_restriction_of_freeExtension_mem (h.1 _ (left_ne_zero_of_mul h0))
  · unfold Loc.E1
    congr 1
    refine Finset.sum_congr rfl fun t _ => integrand_congr h hpsi (fun l s => ?_) fun p => ?_
    · simpa [inv_mul_cancel_left₀ hq] using mem_homS_std.1 hz l s
    · simpa using intAt_zero
  · unfold Loc.E1
    rw [weighted_sum_piFinset (Loc.FC n' c' n c) E K (fun g => ∀ a u, IntAt P u → g (a + (qOf P : E) ^ 0 * u) = g a)
      (LocE.valsQ E (qOf P) A B) (LocE.valsQ E (qOf P) A 0) (((qOf P : K) ^ B)⁻¹) 1 (fun g hg => ?_)
      (fun t => Φ (Loc.xx1 x t) * psi (-Loc.chArg (Loc.xx1 x t))) fun t p a u hu => ?_]
    · rw [one_pow, one_mul]
      refine sum_mem fun t _ => ?_
      by_cases h0 : Φ (Loc.xx1 x t) = 0
      · rw [h0, zero_mul]
        exact zero_mem _
      · exact mul_mem (h.2.2 _) (hmem _ (chArg_int (h.1 _ h0)))
    · rw [sum_valsQ_of_invariant E P K g 0 hg A B (Nat.zero_le B), Nat.sub_zero, inv_mul_cancel_left₀ (pow_ne_zero _ hqK), one_mul]
    · refine integrand_congr h hpsi (fun l s => by simpa using intAt_zero) fun p' => ?_
      by_cases hp : p' = p
      · subst hp
        simpa using hu
      · simpa [hp] using intAt_zero


omit [StarRing E] in
theorem volN_inv_nat {n c : ℕ} {Λ : Submodule (𝓞 E) (Sp E (n + c))} {J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c))}
    (hJ : J ≤ stabL E _ Λ) {k : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hk : k ∈ stabL E _ Λ) :
    ∃ m : ℕ, (Loc.volN K (Loc.Cbe J k) (Loc.N1 E n c ⊓ stabL E _ Λ))⁻¹ = m := by
  have h : Loc.Cbe J k ⊓ Loc.N1 E n c ≤ Loc.N1 E n c ⊓ stabL E _ Λ := fun r hr => ⟨hr.2, by
    have h1 : k⁻¹ * r * k⁻¹⁻¹ ∈ stabL E _ Λ := hJ hr.1.2
    have h2 := mul_mem (mul_mem hk h1) (inv_mem hk)
    rwa [show k * (k⁻¹ * r * k⁻¹⁻¹) * k⁻¹ = r by group] at h2⟩
  unfold Loc.volN
  rw [Subgroup.relIndex_eq_one.2 h, Nat.cast_one, one_div, inv_inv]
  exact ⟨_, rfl⟩

end Unfold

theorem entryAtG : EntryAtG := by
  intro X Pr R Ch sel S mu cst L G m2 hL i hi al be P hP _
  have hm := hL.hm
  have hal := hL.stabG i al P hP
  have hbe := hL.stabG (i + 1) be P hP
  have hJ : Jat (Pr := Pr) cst.sharp (i + 1) P.1 ≤ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) := by
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP]
    split_ifs
    · exact inf_le_left
    · exact inf_le_left
  obtain ⟨v, hv⟩ := volN_inv_nat (K := X.K) hJ hbe
  have h1 : R.k ≤ R.N i := Nat.le_add_right _ _
  have h2 : R.k ≤ R.N (i + 1) := Nat.le_add_right _ _
  have h3 : R.r + (i + 1 - 1) * R.t = R.N i + cOf R i := by
    unfold Ranks.r Ranks.N cOf
    rw [hm, Nat.add_sub_cancel, mul_add i]
    omega
  have h4 : R.N i + cOf R i ≤ R.N (i + 1) + cOf R (i + 1) := by
    unfold Ranks.N cOf
    rw [hm, add_mul i]
    omega
  have hom : Good P.1 (homS (LocE.lamY P.1 (qOf P.1) (R.N i) (cOf R i) fun i => i + 1)
      (LocE.lamY P.1 (qOf P.1) (R.N (i + 1)) (cOf R (i + 1)) fun i => i + 1))
      (omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P)) := by
    unfold lamYat at hal hbe
    rw [if_pos hP] at hal hbe
    refine good_om_two ?_ _ _ _ hal hbe
    unfold PhiAt
    rw [if_pos hP]
    split_ifs
    · exact good_PhiGS _ _ h1 h2 h3 h4
    · exact good_PhiG _ _ h1 h2 h3 h4
  refine (fnModAt_iff _ _ _).2 (Good.const_mul (unfolding_isGoodCyclotomicInvariant_referenceLattices hom (fun a b => psi_add_int hL.cst_ok P)
    (fun a => psi_mem hL.cst_ok P) cst.A cst.B) ?_)
  rw [hv]
  exact natCast_mem _ v

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
section
noncomputable section

namespace GlobalTheory.ColPeriod.Scal

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)

variable {X : Fields} {Pr : Primes X}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (GlobalTheory.ColPeriod.mem_divs h)

theorem g_notMem_of_vGs (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) (h' : P ∉ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  have h2 : ∃ k, P ∈ Pr.vG k := by
    rcases Finset.mem_union.1 h with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  obtain ⟨k, hk⟩ := h2
  have hne : Pr.g i ≠ Pr.g k := by
    have h0 := hPr.g_ne
    fin_cases i <;> fin_cases k
    · exact absurd hk h'
    · exact h0
    · exact h0.symm
    · exact absurd hk h'
  exact natCast_notMem_of_ne (hPr.g_prime i) (hPr.g_prime k) hne P (g_mem_of_vG hPr hk)

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem g_notMem_sel (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ rowSG Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  rw [← hPr.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), by rw [under_conjP hX, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hsel v⟩

theorem val_locChar_unit {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (cq : K) (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (ha : P.valuation E a = 1) :
    w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  have hu := GlobalTheory.LocCharVal.isUnit_redP P _ ha
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  rw [GlobalTheory.LastSteps.locChar_unit _ _ hu, LocE.unitV, dite_eq_left hu]
  exact GlobalTheory.CharVal.unit_of_finOrder (MonoidHom.isOfFinOrder ψ (isOfFinOrder_of_finite _))

theorem val_locChar {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) {cq : K} (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hc : w.valuation K cq = 1) {a : E} (ha : a ≠ 0) : w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul E K P (qOf P) cq ψ a
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hq) ha
  rw [e, map_mul, map_zpow₀, hc, GlobalTheory.CharVal.unit_of_finOrder hζ, one_zpow, one_mul]

end GlobalTheory.ColPeriod.Scal

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker Scal

theorem scalarUnit_of (hL : LevelPrimes) (hH : HeckeUnit) (hT : TwistUnit) : ScalarUnit := by
  intro X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hS ht hOk i w hw j hj
  have hH' := hH X Pr R.m Ch G.σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (G.mu0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.g i) w
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      w.valuation X.K (Ch.muVal ⟨j, hj⟩ P : X.K) = 1 := fun P hP =>
    hH' P (hPr.g_prime i) hw (hP i) (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1 := by
    intro P hPi
    have hq := (hT X.F X.E X.K S mu P.1 w).2
    obtain ⟨hd, hn⟩ := hL X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · have h1 := hOk.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have h3 := hH' P.1 (hPr.g_prime i) hw (g_notMem_of_vGs hPr hP hPi) _ _ h2
      rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hOk.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        hq, hval _ hg]
      simp
  refine ⟨h1, fun n N fr _ hN hfr => ?_⟩
  have h2 : w.valuation X.K (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N) = 1 := by
    unfold muOff
    refine finprod_induction (fun x => w.valuation X.K x = 1) (map_one _)
      (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · exact map_one _
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dite_eq_left hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hval _ (g_notMem_sel hX hPr hsel hv),
        (hT X.F X.E X.K S mu _ w).1]
      simp
  rw [muInvDet, map_mul, h2, one_mul, map_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  by_cases hP : P.1 ∈ Pr.vG i
  · refine val_locChar_unit w P.1 _ _ ?_
    rw [LinearEquiv.coe_det]
    refine GlobalTheory.StdReps.val_det_eq fun x => ?_
    rw [← hfr P x, hN P.1 (g_mem_of_vG hPr hP)]
  · exact val_locChar w P.1 _ (hL X Pr sel S mu hX hPr hsel P).1.2 (h1 P hP) (Units.ne_zero _)

end GlobalTheory.ColPeriod
end
end

