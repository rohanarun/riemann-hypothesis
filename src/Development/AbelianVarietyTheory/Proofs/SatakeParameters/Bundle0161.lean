module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastTwoStepsGuarded
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ColPeriod

theorem valuation_finOrder_apply {G K : Type} [Group G] [Field K] [NumberField K] (ξ : G →* Kˣ) (hξ : IsOfFinOrder ξ)
    (w : HeightOneSpectrum (𝓞 K)) (y : G) : w.valuation K ((ξ y : Kˣ) : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hξ
  have h1 : (ξ y) ^ n = 1 := by
    have := congrArg (fun φ : G →* Kˣ => φ y) h
    simpa using this
  have h2 : (w.valuation K ((ξ y : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 h2

theorem twistUnit : TwistUnit := by
  intro F E K _ _ _ _ _ _ _ S mu P w
  have hfin : IsOfFinOrder (mu : Chr F E K) := mu.2.1.1.1.2
  let v : HeightOneSpectrum (𝓞 F) := P.under (𝓞 F)
  have hv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  constructor
  · unfold unifVal
    split_ifs with h
    · obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
        have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
        simpa using this
      obtain ⟨y, y₀, h1, h2, h3, h4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hv
      rw [← h.choose_spec v hv y y₀ b h1 hb hb2 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp
  · unfold qValC
    split_ifs with h
    · obtain ⟨y, y₀, h1, h2, h3, h4⟩ :=
        GlobalTheory.SuppIdele.exists_supported_idele F E P v ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) hv
      rw [← h.choose_spec v hv y y₀ h1 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfPow
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.TopStep GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator GlobalTheory.LastSteps

noncomputable section

namespace GlobalTheory.ColPeriod.TopTwist

theorem valuation_le_one_of_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {k : ℕ}
    (hk : k ≠ 0) (h : x ^ k = 1) : w.valuation K x ≤ 1 := by
  by_contra hn
  have h1 := one_lt_pow₀ (not_le.1 hn) hk
  rw [← map_pow, h, map_one] at h1
  exact lt_irrefl _ h1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

omit [StarRing E] in
theorem qOf_nat_ne_zero : qOf P ≠ 0 := fun h => (qOf_ne_zero (P := P)) (by rw [h, Nat.cast_zero])

omit [StarRing E] in
theorem qOf_pred_ne_zero : qOf P - 1 ≠ 0 := by
  intro h
  have h0 := qOf_nat_ne_zero (P := P)
  have h1 : qOf P = 1 := by omega
  have h2 := qOf_mem (P := P)
  rw [h1, Nat.cast_one] at h2
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

omit [StarRing E] in
theorem valuation_PhiQ [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (q k₀ r c' n' c n : ℕ)
    (x : HomE E (n' + c') (n + c)) : w.valuation K (LocE.PhiQ q ξ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ LocE.unitV
  split_ifs
  · exact valuation_le_one_of_pow w qOf_pred_ne_zero (char_pow ξ _)
  · simp
  · simp

theorem PhiQ_add (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r c' n' c n : ℕ} (h1 : r ≤ n' + c') (h2 : r ≤ n + c)
    (x z : HomE E (n' + c') (n + c)) (hz : z ∈ homS (LocE.lamY P (qOf P) n' c' 0) (LocE.lamY P (qOf P) n c 0)) :
    LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • z) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  have hZ := entB_int k₀ hz
  unfold LocE.PhiQ
  rw [entB_add_smul]
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 z = Z at hZ
  generalize LocE.entB (qOf P) k₀ c' n' c n 0 0 x = M
  have e1 := fun a p p' => intAt_add_q (a := a) (hZ p p')
  have e2 := fun a p p' => intAt_add_q_div (a := a) (hZ p p')
  refine ite_eq_ite_zero (by simp only [e1, e2]) fun h => ?_
  exact unitV_congr _ (redP_det_add_q (fun s s' => h.1 _ _ (by have := s.2; omega) (by have := s'.2; omega)) fun _ _ => hZ _ _)

end Phi

section Psi

variable {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB}

theorem psi_add_int' (hc : c.Ok) (P : SB) {a b : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) (hb : IntAt P.1 b) :
    c.psi P (a + b) = c.psi P a := by
  rw [hc.psi_add P a b ha ((intAt_pow (intAt_nat _) _).mul hb), hc.psi_int P b hb, mul_one]

theorem psi_pow (hc : c.Ok) (P : SB) {a : X.E} (ha : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * a)) :
    c.psi P a ^ (qOf P.1 ^ c.D P) = 1 := by
  have h : ∀ k : ℕ, c.psi P a ^ k = c.psi P ((k : X.E) * a) := fun k => by
    induction k with
    | zero => rw [pow_zero, Nat.cast_zero, zero_mul, hc.psi_int P 0 intAt_zero]
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, hc.psi_add P _ _ _ ha]
      rw [mul_left_comm]
      exact (intAt_nat _).mul ha
  rw [h, Nat.cast_pow, hc.psi_int P _ ha]

end Psi

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_arg (P : rowSG Pr sel mu) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E)
    (h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η y)) := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hD
  have h1 := (inDual_iff (((qOf P.1 : X.E) ^ cst.M) • η)).2 h _ hy
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
  rw [hk]
  ring

theorem valuation_ftY (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((qOf P.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) :
    w.valuation X.K (ftY sel mu cst P η y) ≤ 1 := by
  unfold ftY
  rw [if_neg hP]
  split_ifs with h
  · have h2 : w.valuation X.K (algebraMap (𝓞 X.K) X.K (qOf P.1 : 𝓞 X.K)) = 1 :=
      (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rw [map_natCast] at h2
    rw [map_mul, map_inv₀, map_pow, h2, one_pow, inv_one, one_mul]
    exact valuation_le_one_of_pow w (pow_ne_zero _ qOf_nat_ne_zero) (psi_pow hc P (intAt_arg sel mu cst P hD hy η h))
  · simp

theorem ftY_add (hc : cst.Ok) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P) {n : ℕ} {y : Sp X.E n}
    (hy : ((qOf P.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n P.1) (η z : Sp X.E n →ₗ[X.E] X.E) (hz : InDual P.1 z) :
    ftY sel mu cst P (η + ((qOf P.1 : X.E) ^ cst.B) • z) y = ftY sel mu cst P η y := by
  have he : IntAt P.1 (epsSg : X.E) := by simpa [epsSg] using intAt_neg intAt_one
  have hz' := (inDual_iff z).1 hz
  unfold ftY
  simp only [if_neg hP]
  refine ite_eq_ite_zero (forall_congr' fun i => ?_) fun h => ?_
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add]
    exact intAt_add_iff ((intAt_pow (intAt_nat _) _).mul ((intAt_pow (intAt_nat _) _).mul (hz' i)))
  · rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, mul_add,
      psi_add_int' hc P (intAt_arg sel mu cst P hD hy η h)]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc.M_le_B
    have h1 := hz _ hy
    rw [map_smul, smul_eq_mul] at h1
    convert (he.mul (intAt_pow (intAt_nat (qOf P.1)) k)).mul h1 using 1
    rw [hk]
    ring

theorem frsF_mem' {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (x : Sp X.E (R.N j)) : frsF sel mu p P x ∈ localization₂ P.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  classical
  unfold frsF
  rw [dite_eq_right hP]
  have h : ∀ Q : QE sel (mu : Chr X.F X.E X.K), p.fr Q x ∈ localization₂ Q.1.asIdeal p.deco.1.N ↔ x ∈ stdAt X.E (R.N j) Q.1 :=
    fun Q => p.2 Q x
  exact h ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩

theorem pow_smul_repY {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N)
    (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) : ((qOf P.1 : X.E) ^ cst.M) • repY Y ∈ localization₂ P.1.asIdeal N := by
  obtain ⟨y, hy, hY⟩ := hY
  have h0 : repY Y ∈ Y := Classical.epsilon_spec (p := fun y => y ∈ Y) ⟨y, by rw [hY]; simp⟩
  generalize repY Y = y' at h0
  rw [hY] at h0
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 h0 P
  rw [if_neg hP] at h1 h2
  simp only [zpow_neg, inv_inv, zpow_natCast] at h1 h2
  have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ qOf_ne_zero
  have hi : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M) := intAt_pow (intAt_nat _) _
  have h3 := smul_mem_locP hi (smul_mem_locP hi h2)
  rw [smul_inv_smul₀ hq] at h3
  have h4 := add_mem h3 h1
  rwa [← smul_add, sub_add_cancel] at h4

end Chain

theorem topAtQ : GlobalTheory.ColPeriod.TopAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL P w hP _ hw p d Y hY
  have hc := hL.cst_ok
  have hm := hL.hm
  have hD := hL.depthQ P hP
  have hu := piT_notMem_rowSG sel mu hPr hsel u hS
  have hy : ((qOf P.1 : X.E) ^ cst.M) • (frsF sel mu p P).symm (repY Y) ∈ stdAt X.E _ P.1 := by
    rw [← map_smul, ← frsF_mem' sel mu p P hP, LinearEquiv.apply_symm_apply]
    exact pow_smul_repY sel mu cst hY P hP
  refine ⟨fun x => ?_, fun x z hz => ?_⟩
  · unfold facTop PhiTop
    rw [if_neg hP, map_mul]
    exact mul_le_one' (valuation_PhiQ w _ _ _ _ _ _ _ _ _) (valuation_ftY sel mu cst hc P hP hD w hw hy _)
  · have key : ∀ y ∈ stdAt X.E (R.N (m2 + 1)) P.1,
        (d.1.liftFr P).symm (prXp X.E R (z (frsF sel mu p P y))) ∈ stdAt X.E (R.N R.m - 1) P.1 ∧
          IntAt P.1 (((Pr.piT u : 𝓞 X.E) : X.E)⁻¹ * atNL X.E (R.N R.m) (R.N R.m - 1) (z (frsF sel mu p P y))) := fun y hy => by
      have h := (mem_tilH (N_m_succ R) d (conj_piT_notMem hPr u) hu P.1 _).1
        (hz P.1 (Finset.mem_singleton_self _) _ ((frsF_mem' sel mu p P hP y).2 hy))
      rw [atNL_last, ← (liftFr_spec d.2 P).1, LinearEquiv.apply_symm_apply, inv_mul_eq_div]
      exact ⟨h.1, h.2.div_of_notMem (hu P)⟩
    have h1 : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by
      unfold Ranks.r Ranks.N cOf
      rw [hm, mul_add (m2 + 1)]
      omega
    have h4 : R.N (m2 + 1) + cOf R (m2 + 1) ≤ R.N R.m - 1 + 0 := by
      unfold Ranks.N cOf
      rw [hm, show m2 + 2 = m2 + 1 + 1 from rfl, add_mul (m2 + 1)]
      omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc.B_pos
    unfold facTop PhiTop
    rw [if_neg hP]
    congr 1
    · have e : (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ (x + ((qOf P.1 : X.E) ^ cst.B) • z) ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
          (d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ x ∘ₗ
            (frsF sel mu p P).toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) +
          (qOf P.1 : X.E) • ((((qOf P.1 : X.E) ^ k) • ((d.1.liftFr P).symm.toLinearMap ∘ₗ prXp X.E R ∘ₗ z ∘ₗ
            (frsF sel mu p P).toLinearMap)) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
        rw [hk, pow_succ', mul_smul]
        simp only [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.comp_assoc]
      rw [e]
      refine PhiQ_add _ h1 (h1.trans h4) _ _ ?_
      rw [comp_funLeft_mem (cOf_top hm), lamY_zero]
      exact fun y hy => smul_mem_locP (intAt_pow (intAt_nat _) _) (key y hy).1
    · rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp ((qOf P.1 : X.E) ^ cst.B), LinearMap.comp_smul]
      exact ftY_add sel mu cst hc P hP hD hy _ _ fun y hy => (key y hy).2

end GlobalTheory.ColPeriod.TopTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VolqExistsPow
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain _root_.Formalism.L2.Col GlobalTheory.TopStep

theorem volq_index {G : Type} [Group G] (H : Subgroup G) {q k : ℕ} (hq : q.Prime) (h : ∀ g : G, g ^ q ^ k ∈ H) :
    H.index = 0 ∨ ∃ e : ℕ, H.index = q ^ e := by
  by_cases h0 : H.index = 0
  · exact Or.inl h0
  right
  haveI : H.FiniteIndex := ⟨h0⟩
  haveI := Fact.mk hq
  have hp : IsPGroup q (G ⧸ H.normalCore) := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    intro b
    have := h (b * g * b⁻¹)
    rwa [conj_pow] at this
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hp
  have hd : H.index ∣ q ^ e := by
    rw [← he]
    exact Subgroup.index_dvd_of_le H.normalCore_le
  obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow hq).1 hd
  exact ⟨e', he'⟩

theorem volq_choose {q : ℕ} (hq : q.Prime) (a c i : ℕ) (h0 : i ≠ 0) (hi : i ≤ c) : q ^ a ∣ (q ^ (a + c)).choose i := by
  by_cases h : i ≤ q ^ (a + c)
  · have h1 := Nat.factorization_choose_prime_pow_add_factorization hq h h0
    have h2 := Nat.factorization_lt q h0
    rw [hq.pow_dvd_iff_le_factorization (Nat.choose_pos h).ne']
    omega
  · rw [Nat.choose_eq_zero_of_lt (not_le.1 h)]
    exact dvd_zero _

theorem volq_pow_mem {V : Type} [AddCommGroup V] (A B : AddSubgroup V) {q : ℕ} (hq : q.Prime) (b c : ℕ)
    (hAB : ∀ v ∈ A, q ^ b • v ∈ B) (hBA : ∀ v ∈ B, q ^ b • v ∈ A) (r : Module.End ℤ V) (hr : ∀ v ∈ B, r v ∈ B)
    (hn : (r - 1) ^ (c + 1) = 0) : ∀ v ∈ A, (r ^ q ^ (2 * b + c)) v ∈ A := by
  intro v hv
  have hν : ∀ i : ℕ, ∀ v ∈ B, ((r - 1) ^ i) v ∈ B := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (B.sub_mem (hr v hv) hv)
  have e : r = (r - 1) + 1 := by simp
  rw [e, (Commute.one_right _).add_pow, LinearMap.sum_apply]
  refine A.sum_mem fun i _ => ?_
  rw [one_pow, mul_one, ← nsmul_eq_mul', LinearMap.smul_apply]
  rcases eq_or_ne i 0 with rfl | h0
  · simpa using hv
  by_cases hi : i ≤ c
  · obtain ⟨t, ht⟩ := volq_choose hq (2 * b) c i h0 hi
    have h1 := hBA _ (hν i _ (hAB v hv))
    rw [map_nsmul, smul_smul, ← pow_add, ← two_mul] at h1
    rw [ht, mul_comm, mul_smul]
    exact A.nsmul_mem h1 t
  · rw [pow_eq_zero_of_le (by omega) hn]
    simpa using A.zero_mem

section Nil

variable {k : Type} [CommRing k] {n c : ℕ}

theorem volq_lower {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) (i : ℕ) :
    ∀ v ∈ Loc.Ufl k n c (i + 1), r v - v ∈ Loc.Ufl k n c i := by
  intro v hv
  have h1 : v - Loc.atN v (n + i) • Loc.eN k (n + c) (n + i) ∈ Loc.Ufl k n c i := by
    intro l hl
    by_cases h : l.1 = n + i
    · have h2 : n + i < n + c := h ▸ l.2
      have h3 : l = ⟨n + i, h2⟩ := Fin.ext h
      subst h3
      simp [Loc.atN, Loc.eN, h2]
    · have := hv l (by simp only [Set.mem_setOf_eq] at hl ⊢; omega)
      simp [Loc.eN, h, this]
  have h2 := hr.1.1.1 i _ h1
  have h3 := (Loc.Ufl k n c i).smul_mem (Loc.atN v (n + i)) (hr.1.1.2.2 i)
  have h4 := add_mem (sub_mem h2 h1) h3
  convert h4 using 1
  simp only [map_sub, map_smul, smul_sub]
  abel

theorem volq_zero {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ∀ v ∈ Loc.Ufl k n c 0, r v - v = 0 := by
  intro v hv
  have e : v = Loc.inX k n c fun l => v (Fin.castAdd c l) := by
    funext l
    by_cases h : l.1 < n
    · simp [Loc.inX, h]
    · simp only [Loc.inX, LinearMap.pi_apply, h, dif_neg, not_false_eq_true, LinearMap.zero_apply]
      exact hv l (by simpa using h)
  rw [sub_eq_zero, e]
  exact hr.2 _

theorem volq_nil {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (c + 1) = 0 := by
  have h : ∀ i, ∀ v ∈ Loc.Ufl k n c i,
      (((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (i + 1)) v = 0 := by
    intro i
    induction i with
    | zero => intro v hv; simpa using volq_zero hr v hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (volq_lower hr i v hv)
  exact LinearMap.ext fun v => h c v fun l hl => absurd l.2 hl

end Nil

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem volq_exists_pow (a : E) : ∃ b : ℕ, IntAt P ((qOf P : E) ^ b * a) := by
  have hq : P.valuation E (qOf P : E) < 1 := by
    have := (P.valuation_lt_one_iff_mem (K := E) _).2 (qOf_mem (P := P))
    change P.valuation E (algebraMap (𝓞 E) E _) < 1 at this
    rwa [map_natCast] at this
  have : ∃ b : ℕ, P.valuation E ((qOf P : E) ^ b * a) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    have h0 : P.valuation E a ≠ 0 := (map_ne_zero _).2 ha
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hq (Units.mk0 _ h0)⁻¹
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, ← le_mul_inv_iff₀ (zero_lt_iff.2 h0), one_mul]
    simpa using hb.le
  obtain ⟨b, hb⟩ := this
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hb
  exact ⟨b, n, d, d.2, by rw [mul_comm]; exact h⟩

variable [StarRing E]

theorem volq_bound {N : ℕ} (f : Sp E N →ₗ[E] Sp E N) :
    ∃ b : ℕ, ∀ b', b ≤ b' → ∀ v ∈ stdAt E N P, qOf P ^ b' • f v ∈ stdAt E N P := by
  choose g hg using fun p : Fin N × Fin N => volq_exists_pow (P := P) (f (Pi.single p.2 1) p.1)
  refine ⟨Finset.univ.sup g, fun b' hb v hv => mem_stdAt.2 fun i => ?_⟩
  rw [Pi.smul_apply, apply_eq_sum, nsmul_eq_mul, Finset.mul_sum]
  refine intAt_sum _ fun j _ => ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ((Finset.le_sup (f := g) (Finset.mem_univ (i, j))).trans hb)
  have := ((mem_stdAt.1 hv j).mul (hg (i, j))).mul (intAt_pow (intAt_nat (qOf P)) t)
  convert this using 1
  push_cast
  ring

theorem volq_lamY {n c : ℕ} : LocE.lamY P (qOf P) n c 0 = stdAt E (n + c) P := by
  ext v
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt, mem_stdAt]
  simp [LocE.scE]

theorem volq_relIndex (hq : (qOf P).Prime) {n c : ℕ} (J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)))
    (hJ : J ≤ stabL E _ (stdAt E (n + c) P)) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = 0 ∨
    ∃ e : ℕ, (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = qOf P ^ e := by
  obtain ⟨b₁, h₁⟩ := volq_bound (P := P) h.toLinearMap
  obtain ⟨b₂, h₂⟩ := volq_bound (P := P) h.symm.toLinearMap
  have key : ∀ r ∈ Loc.Cbe J h ⊓ Loc.N1 E n c, ∀ v ∈ stdAt E (n + c) P,
      (r ^ qOf P ^ (2 * (b₁ + b₂) + c)) v ∈ stdAt E (n + c) P := by
    intro r hr v hv
    have hs : h⁻¹ * r * h ∈ stabL E _ (stdAt E (n + c) P) := by
      have := hJ (Subgroup.mem_comap.1 hr.1.2)
      simpa using this
    have := volq_pow_mem (stdAt E (n + c) P).toAddSubgroup
      ((stdAt E (n + c) P).toAddSubgroup.comap h.symm.toLinearMap.toAddMonoidHom) hq (b₁ + b₂) c
      (fun v hv => ?_) (fun v hv => ?_) (r.toLinearMap.restrictScalars ℤ) (fun v hv => ?_) (volq_nil hr.2) v hv
    · have e : ∀ m : ℕ, ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Sp E (n + c))) ^ m) v = (r ^ m) v := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; rfl
      rw [e] at this
      exact this
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h₂ _ (by omega) v hv
    · have := h₁ (b₁ + b₂) (by omega) _ hv
      simpa using this
    · have := (hs (h.symm v)).2 hv
      change h.symm (r (h (h.symm v))) ∈ _ at this
      rw [h.apply_symm_apply] at this
      exact this
  refine volq_index _ hq (k := 2 * (b₁ + b₂) + c) fun g => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  refine ⟨pow_mem g.2.2 _, fun v => ⟨fun hv => ?_, key g.1 g.2 v⟩⟩
  have := key g.1⁻¹ (inv_mem g.2) _ hv
  rw [inv_pow] at this
  change (g.1 ^ _).symm _ ∈ _ at this
  rwa [LinearEquiv.symm_apply_apply] at this

end Loc

theorem volumeAtQ : VolumeAtQ := by
  intro X Pr R sharp j P h w hP hd hw
  unfold Loc.volN Jat lamYat
  simp only [if_neg hP]
  rw [volq_lamY, inv_div, map_div₀]
  have hn : ∀ m : ℕ, w.valuation X.K (m : X.K) ≤ 1 := fun m => by
    have := w.valuation_le_one (K := X.K) (m : 𝓞 X.K)
    change w.valuation X.K (algebraMap (𝓞 X.K) X.K _) ≤ 1 at this
    rwa [map_natCast] at this
  have hq : w.valuation X.K (qOf P : X.K) = 1 := by
    have := (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rwa [map_natCast] at this
  rcases volq_relIndex hd.1 (LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j)) inf_le_left h with h0 | ⟨e, he⟩
  · rw [h0]
    simp
  · rw [he, Nat.cast_pow, map_pow, hq, one_pow, div_one]
    exact hn _

end GlobalTheory.ColPeriod
end
end

