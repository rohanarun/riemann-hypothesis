module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop

namespace GlobalTheory.RefSum.DivWt

section Free

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd


omit [Fintype ι] in
theorem antitone (τ : ι) : Antitone (W.u1 τ) := fun a b hab => by
  have hab' : (a : ℕ) ≤ b := hab
  have := (W.div_gap_sum h hd τ (b - a) a b (by omega)).1
  linarith

theorem mul_abs_le (τ : ι) (a : Fin N) : (W.T : ℝ) * |(W.u1 τ a : ℝ)| ≤ 2 * W.b := by
  have h1 := (divided_entries ι N W h hd τ a).1
  have h2 : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h3 := h.h5 τ a
  have h4 : 0 ≤ ((W.Dd : ℝ) + 1) * |(W.u1 τ a : ℝ)| := by positivity
  linarith


omit [Fintype ι] in
theorem mul_cloud_le (τ : ι) (a : Fin N) (ha : (a : ℕ) < W.kc) : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ W.S + 2 * N := by
  have hk := h.kc_lt
  have hp := h.p_lt
  let c : Fin N := ⟨W.kc - 1, by omega⟩
  have hc : (c : ℕ) + 1 = W.kc := by simp only [c]; omega
  obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (c - a) a c (by omega)
  have h3 : (((c : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
  rw [(hd τ).1 c hc, sub_zero] at h1 h2
  rw [h.anchor τ c hc] at h2
  have h4 : 0 ≤ ((W.Dd : ℤ) + 1) * W.u1 τ a := by positivity
  have h5 : (W.T : ℤ) * W.u1 τ a ≤ W.u τ a + 2 * N := by linarith
  have h6 : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ (W.u τ a : ℝ) + 2 * N := by exact_mod_cast h5
  linarith [(h.h3cloud τ a ha).2]

end Free

theorem nCol_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    nCol Dw ≤ Module.finrank ℚ E * (Dw.p + Dw.q) * (2 * (Dw.p + Dw.q) + 8) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := rk_le f
    have : Dw.mult f.1 ≤ Dw.p + Dw.q := by rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q) + 8) (card_Lt1_le_finrank_mul (Dw := Dw))
  rw [mul_add (Fintype.card (Lt1 Dw))] at h2
  unfold nCol
  omega

theorem gap_num {PP T X h g f r : ℝ} (hT : 0 < T) (hX : 60 ≤ X) (hf : 1 ≤ f) (hr : 1 ≤ r) (hP : f * r ^ 2 ≤ PP)
    (h1 : PP * X * T ≤ h) (h2 : h ≤ 2 * T * g) : 2 * f * r * (2 * r + 8) + 8 + 1 ≤ g := by
  have a : PP * X ≤ 2 * g := le_of_mul_le_mul_right (by linarith) hT
  have b1 : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have b2 : f * r ≤ f * r ^ 2 := by nlinarith
  have c : PP * 60 ≤ PP * X := mul_le_mul_of_nonneg_left hX (by linarith)
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem wtAt_of_wtNum {PP : ℝ} (h : WtNum p i PP) (hP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : GlobalTheory.AllWt.Weight (dat p i)) (hq : Quo p i PP u1) : WtAt p i PP 802 u1 := by
  obtain ⟨h0, S, eta, hS, he, hSe, -, hh0, hH⟩ := h.hyp hi
  have H := hH u1
  have hd := (quo_iff p i PP h0 S eta u1).1 hq
  obtain ⟨hp, hq', hr⟩ := h.sig
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : 2 ≤ D.R.f := D.R.two_le_m.trans D.R.m_le_f
  simp only [Ranks.sigW] at hp hq'
  have hT1 : 4 * GlobalTheory.CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := H.h1
  have hD : 1 ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by
    rw [h.dim]; exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨τ0⟩ : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [h.card]; omega)).1
  have han : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) ≤ 4 * L.sc.b := by
    unfold anchor
    rw [dite_eq_left (by omega)]
    exact (le_abs_self _).trans (h.up τ0 _)
  have hlow := h.low τ0
  have hw : 4 * ((eta + S + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + S + ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + 20 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) := H.h3w τ0
  have hc0 : (0 : ℝ) ≤ ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) := by exact_mod_cast (cZero_spec D _).2.1
  have hrows := h.what₂.1
  have e1 : ∀ τ a, (lenT p i PP : ℝ) * |(u1 τ a : ℝ)| ≤ 2 * (4 * L.sc.b) := mul_abs_le _ H hd
  have e2 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) < D.R.k - 1 →
      (lenT p i PP : ℝ) * (u1 τ a : ℝ) ≤ S + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) := mul_cloud_le _ H hd
  have e3 : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := fun τ a b hab hb =>
    ((divided_gaps _ _ _ H hd τ a b hab).2.1 hb).1
  have e4 : ∀ τ, Antitone (u1 τ) := antitone _ H hd
  have e5 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = D.R.k - 1 → u1 τ a = 0 := fun τ => (hd τ).1
  have hn := nCol_le (dat p i)
  rw [GlobalTheory.PinNum.finrank_host D, hr] at hn
  rw [hr] at hw
  simp only [hr] at e2
  unfold WtAt
  clear H hd hH hq h
  have hT : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hT' : 1 ≤ lenT p i PP := by omega
  generalize lenT p i PP = T at *
  generalize (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) = w at *
  generalize ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) = c at *
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hD' : (1 : ℝ) ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by exact_mod_cast hD
  have hkP : (D.R.k : ℝ) ≤ PP := by nlinarith
  have hTb : (T : ℝ) ≤ 4 * L.sc.b := by nlinarith
  have hb : 0 ≤ L.sc.b := by linarith
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, GlobalTheory.PinNum.finrank_host D⟩, by omega,
    ⌊8 * L.sc.b / T⌋₊, D.R.k * (S + 2 * D.R.r) / T, ⟨e4, fun τ a ha => e5 τ a (by omega), fun τ a b ha hb' => ?_,
      fun τ a => ?_, fun τ => ?_⟩, ?_, ?_, hT'⟩
  · have g1 : (h0 : ℝ) ≤ 2 * (T : ℝ) * ((u1 τ a - u1 τ b : ℤ) : ℝ) := by exact_mod_cast e3 τ a b (by omega) hb'
    have hX : (60 : ℝ) ≤ D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * GlobalTheory.CompHt.dimFlag (dat p i) := by
      calc (60 : ℝ) ≤ 5 * 2 ^ 2 * 2 ^ 2 * 5 * 1 := by norm_num
        _ ≤ _ := by gcongr; linarith
    have g2 := gap_num (by linarith) hX (by linarith) (by linarith) hP (le_of_eq_of_le (by ring) hh0) g1
    have g3 : ((nCol (dat p i) : ℕ) : ℝ) ≤ 2 * D.R.f * D.R.r * (2 * D.R.r + 8) + 8 := by exact_mod_cast hn
    have g4 : ((nCol (dat p i) : ℕ) : ℝ) + 1 ≤ ((u1 τ a - u1 τ b : ℤ) : ℝ) := by linarith
    exact_mod_cast g4
  · have g1 : ((|u1 τ a|.toNat : ℕ) : ℝ) = |(u1 τ a : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _), Int.cast_abs]
    have g2 : |u1 τ a|.toNat ≤ ⌊8 * L.sc.b / T⌋₊ := by
      refine Nat.le_floor ?_
      rw [g1, le_div_iff₀ (by linarith)]
      linarith [e1 τ a]
    exact Int.toNat_le.1 g2
  · rw [le_div_iff₀ (by linarith), Finset.sum_mul]
    refine (Finset.sum_le_card_nsmul _ _ (S + 2 * D.R.r) fun a ha => ?_).trans ?_
    · have := (Finset.mem_filter.1 ha).2
      linarith [e2 τ a (by omega)]
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (Finset.univ.filter (fun a : Fin ((dat p i).p + (dat p i).q) => (a : ℕ) + 2 < D.R.k)).card ≤
          (Finset.range D.R.k).card :=
        Finset.card_le_card_of_injOn (fun a => (a : ℕ))
          (fun a ha => by have := (Finset.mem_filter.1 ha).2; simp only [Finset.coe_range, Set.mem_Iio]; omega)
          (fun a _ b _ e => Fin.ext e)
      rw [Finset.card_range] at this
      exact_mod_cast this
  · have g1 : ((⌊8 * L.sc.b / T⌋₊ : ℕ) : ℝ) ≤ 8 * L.sc.b / T := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by linarith)] at g1
    linarith
  · rw [mul_div_cancel₀ _ (by linarith)]
    have g1 : (D.R.k : ℝ) * S ≤ PP * (S + eta) := mul_le_mul hkP (by linarith) hS (by linarith)
    have g2 : (D.R.r : ℝ) * D.R.k ≤ L.sc.b := by
      refine le_trans ?_ hrows
      calc (D.R.r : ℝ) * D.R.k = 1 ^ 2 * D.R.r * 1 * D.R.k * 1 ^ 3 := by ring
        _ ≤ _ := by gcongr <;> linarith
    linarith

theorem le_PP {P : ParameterChoice' D L} (T : ParamsT D L P) : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ T.PP := by
  have h1 : D.R.f * D.R.r ^ 2 ≤ T.nWn := le_trans (by nlinarith [Nat.zero_le (D.R.f * D.R.r)]) T.nW_lo.1
  exact le_trans (by exact_mod_cast h1) T.nW_le

end GlobalTheory.RefSum.DivWt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectivePairedModels
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DblGoodInt

section Coord

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
  {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

theorem symp_fromCols {d : Darboux (symp c ξ JA JB) κ} {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}
    (h : IsDblCoord c ξ JA JB d dd) (w₁ w₂ w₁' w₂' : Matrix α β E) :
    symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂' := by
  rw [dd.form, h, h, d.form, d.form]
  simp only [GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg]
  ring

def dblEquiv (d₁ : Darboux (symp c ξ JA JB) κ) : Matrix α (β ⊕ β) E ≃ₗ[R] (κ ⊕ κ → R) × (κ ⊕ κ → R) where
  toFun z := (Sum.elim (d₁.e z.toCols₁).1 (d₁.e z.toCols₂).1, Sum.elim (d₁.e z.toCols₁).2 (-(d₁.e z.toCols₂).2))
  invFun p := Matrix.fromCols (d₁.e.symm (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl)) (d₁.e.symm (p.1 ∘ Sum.inr, -(p.2 ∘ Sum.inr)))
  map_add' z z' := by
    have h1 : (z + z').toCols₁ = z.toCols₁ + z'.toCols₁ := by ext; simp [Matrix.toCols₁]
    have h2 : (z + z').toCols₂ = z.toCols₂ + z'.toCols₂ := by ext; simp [Matrix.toCols₂]
    rw [h1, h2, map_add (f := _), map_add (f := _)]
    ext k <;> cases k <;> simp [add_comm]
  map_smul' a z := by
    have h1 : (a • z).toCols₁ = a • z.toCols₁ := by ext; simp [Matrix.toCols₁]
    have h2 : (a • z).toCols₂ = a • z.toCols₂ := by ext; simp [Matrix.toCols₂]
    rw [h1, h2, map_smul, map_smul]
    ext k <;> cases k <;> simp
  left_inv z := by
    simp only
    conv_rhs => rw [← Matrix.fromCols_toCols z]
    congr 1 <;> rw [LinearEquiv.symm_apply_eq] <;> ext <;> simp
  right_inv p := by
    simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols, LinearEquiv.apply_symm_apply]
    ext k <;> cases k <;> simp

def dblOf (d₁ : Darboux (symp c ξ JA JB) κ)
    (hf : ∀ w₁ w₂ w₁' w₂' : Matrix α β E, symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂') : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ) where
  e := dblEquiv d₁
  form z z' := by
    rw [← Matrix.fromCols_toCols z, ← Matrix.fromCols_toCols z', hf, d₁.form, d₁.form]
    simp only [dblEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Matrix.toCols₁_fromCols,
      Matrix.toCols₂_fromCols, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg]
    ring

theorem isDblCoord_dblOf (d₁ : Darboux (symp c ξ JA JB) κ)
    (hf : ∀ w₁ w₂ w₁' w₂' : Matrix α β E, symp c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁' w₂') =
      symp c ξ JA JB w₁ w₁' - symp c ξ JA JB w₂ w₂') : IsDblCoord c ξ JA JB d₁ (dblOf d₁ hf) := fun w₁ w₂ => by
  simp [dblOf, dblEquiv]

end Coord

section Fun

variable {R : Type}

def conjEquiv {X : Type} (T : (X → ℂ) ≃ₗ[ℂ] (X → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (X → ℂ) :=
  LinearEquiv.ofLinear (conjMap T.toLinearMap) (conjMap T.symm.toLinearMap)
    (LinearMap.ext fun φ => by simp [conjMap_apply]) (LinearMap.ext fun φ => by simp [conjMap_apply])

def partLEquiv {κ κ' : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partL T.toLinearMap) (partL T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partL_apply])

def partREquiv {κ κ' : Type} (T : ((κ' → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ' → R) → ℂ) :=
  LinearEquiv.ofLinear (partR T.toLinearMap) (partR T.symm.toLinearMap)
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])
    (LinearMap.ext fun Φ => funext fun s => by simp [partR_apply])

def dblEquivFun {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ) :=
  (partREquiv (conjEquiv T)).trans (partLEquiv T)

theorem dblEquivFun_coe {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    (dblEquivFun T).toLinearMap = evDbl T.toLinearMap := rfl

theorem dblEquivFun_symm_coe {κ : Type} (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) :
    (dblEquivFun T).symm.toLinearMap = partR (conjMap T.symm.toLinearMap) ∘ₗ partL (κ' := κ) T.symm.toLinearMap := rfl

end Fun

section Law

variable {F : Type} [Field F] [NumberField F]

theorem evDbl_schr (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ)) (A₁ B₁ A₂ B₂ : κ → AF F) (a₁ b₁ a₂ b₂ : κ₁ → AF F)
    (h1 : ∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a₁, b₁) (T Φ))
    (h2 : ∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a₂, b₂) (T Φ))
    (h3 : ∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) :
    ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
      schr ψ (Sum.elim a₁ a₂, Sum.elim b₁ (-b₂)) (evDbl T φ) := by
  intro φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a₂, -b₂) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := GlobalTheory.DoublingEvLaw.star_schr' ψ hψ (a₂, -b₂) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := GlobalTheory.DoublingEvLaw.sliceL hΨ (s ∘ Sum.inr + a₂)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b₂) - ⅟(2 : AF F) * (a₂ ⬝ᵥ b₂)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a₂))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, GlobalTheory.DoublingEvLaw.elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (GlobalTheory.DoublingEvLaw.sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, GlobalTheory.DoublingEvLaw.elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b₁ (-b₂) = (s ∘ Sum.inl) ⬝ᵥ b₁ - (s ∘ Sum.inr) ⬝ᵥ b₂ := by
    rw [← Sum.elim_comp_inl_inr s, GlobalTheory.DoublingEvLaw.elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr,
      sub_eq_add_neg]
  rw [hs]
  ring

end Law

section Generic

variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
  {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}

theorem hasDbl_of (ψ : AddChar (AF F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (hT : IsTame F T.toLinearMap)
    (hT' : IsTame F T.symm.toLinearMap) (hheis : ∀ w, ∀ φ ∈ schA F κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ k : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = k * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hf := symp_fromCols hdd
  have hR : IsTame F (partR (κ := κ) (conjMap T.toLinearMap)) := GlobalTheory.T.tame_part_right F κ κ κ _ (_root_.GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hT)
  have hL : IsTame F (partL (κ' := κ) T.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hT
  have hR' : IsTame F (partR (κ := κ) (conjMap T.symm.toLinearMap)) :=
    GlobalTheory.T.tame_part_right F κ κ κ _ (_root_.GlobalTheory.DoublingEv.isTame_conjMap F κ κ _ hT')
  have hL' : IsTame F (partL (κ' := κ) T.symm.toLinearMap) := GlobalTheory.T.tame_part_left F κ κ κ _ hT'
  have hTd : IsTame F (dblEquivFun T).toLinearMap := by rw [dblEquivFun_coe]; exact hR.comp hL
  have hTd' : IsTame F (dblEquivFun T).symm.toLinearMap := by rw [dblEquivFun_symm_coe]; exact hL'.comp hR'
  have hconj : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ k : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖conjMap T.toLinearMap φ x‖ₑ ^ 2 ∂μ = k * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨k, hk⟩ := hunit μ hμ
    refine ⟨k, fun φ hφ => ?_⟩
    have h := hk (star φ) (GlobalTheory.SchAConj.star_mem_schA F κ φ hφ)
    simp only [conjMap_apply, Pi.star_apply, LinearEquiv.coe_coe, enorm_eq_nnnorm, nnnorm_star] at h ⊢
    exact h
  refine ⟨dblOf d₁ hf, dblEquivFun T, conjEquiv T, isDblCoord_dblOf d₁ hf, ⟨fun φ => ⟨fun h => hTd.mapsTo φ h,
    fun h => ?_⟩, fun w φ hφ => ?_, fun l => ⟨fun hl => hTd.comp_adm hl, fun hl => ?_⟩, fun μ hμ => ?_⟩,
    fun φ => ⟨fun h => ?_, fun h => ?_⟩, fun φ₁ _ φ₂ _ => evDbl_boxFun T.toLinearMap φ₁ φ₂⟩
  · have := hTd'.mapsTo _ h
    exact (by simpa using this : φ ∈ schA F (κ ⊕ κ))
  · obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, w = Matrix.fromCols w₁ w₂ := ⟨_, _, (Matrix.fromCols_toCols w).symm⟩
    show evDbl T.toLinearMap (schr ψ (dd.e (Matrix.fromCols w₁ w₂)) φ) =
      schr ψ ((dblOf d₁ hf).e (Matrix.fromCols w₁ w₂)) (evDbl T.toLinearMap φ)
    rw [hdd, isDblCoord_dblOf d₁ hf]
    exact evDbl_schr ψ hψ T.toLinearMap _ _ _ _ _ _ _ _ (fun Φ hΦ => hheis w₁ Φ hΦ) (fun Φ hΦ => hheis w₂ Φ hΦ)
      hR.mapsTo φ hφ
  · have := hTd'.comp_adm hl
    convert this using 1
    ext φ
    simp
  · obtain ⟨k₁, hk₁⟩ := GlobalTheory.T.partial_fourier_right_isometry_l2 F κ κ (conjMap T.toLinearMap) hR.mapsTo hconj μ hμ
    obtain ⟨k₂, hk₂⟩ := GlobalTheory.T.partial_fourier_left_isometry_l2 F κ κ T.toLinearMap hL.mapsTo hunit μ hμ
    refine ⟨k₂ * k₁, fun φ hφ => ?_⟩
    show ∫⁻ x, ‖partL (κ' := κ) T.toLinearMap (partR (κ := κ) (conjMap T.toLinearMap) φ) x‖ₑ ^ 2 ∂μ = _
    rw [hk₂ _ (hR.mapsTo φ hφ), hk₁ φ hφ, mul_assoc]
  · exact GlobalTheory.SchAConj.star_mem_schA F κ _ (hT.mapsTo _ (GlobalTheory.SchAConj.star_mem_schA F κ φ h))
  · have h2 := GlobalTheory.SchAConj.star_mem_schA F κ _ (hT'.mapsTo _ (GlobalTheory.SchAConj.star_mem_schA F κ _ h))
    have e : (conjEquiv T).symm (conjEquiv T φ) = φ := (conjEquiv T).symm_apply_apply φ
    rw [← e]
    exact h2

end Generic

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co M₁.co T := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hTame : IsTame F T.toLinearMap := by
    intro g hg
    obtain ⟨ι, _, P, g', hg', hP⟩ :=
      GlobalTheory.T.evaluation_good_models_intertwine F E σ B n d n d X W X W M M₁ 1 1 _ e hpair.good hM₁ hev g hg
    exact ⟨ι, inferInstance, P, g', hg', fun f => by
      rw [LinearEquiv.coe_coe, hTe _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)]
      exact hP f⟩
  refine hasDbl_of B.ψ (GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std) M.co M₁.co T hTame
    (_root_.GlobalTheory.EvSymmTame.isTame_symm F E σ B n d X W M M₁ hpair.good hM₁ e hev hbij T hTe) (fun w Φ hΦ => ?_) (fun μ hμ => ?_)
  · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) := _root_.GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
    have := hev.Heisenberg₂ w Φ hΦ
    rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
    rw [hTe _ hm, hTe _ hΦ, this]
  · obtain ⟨k, hk⟩ := _root_.GlobalTheory.EvalUnitUnconditional.exists_const F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
    exact ⟨k, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hk Φ hΦ⟩

end GlobalTheory.DblGoodInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
section
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def SympCond {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (T : Over S)
    (t₁ : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left) (β : cycAway M →+* k) (z : kˣ),
      x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      (∀ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = 1 ↔ ∃ c, a = M • c) ∧
      (∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, g ^ M = 1 →
        ∃ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = g) ∧
      ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a)
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv c) (unitOn (z ^ (2 * omegaStd a c)))

theorem zetaAway_pow_self (M : ℕ) (hM : M ≠ 0) : zetaAway M ^ M = 1 :=
  Subtype.ext (by simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp M hM).pow_eq_one)

theorem zetaAway_pow_eq (M : ℕ) (hM : M ≠ 0) {k k' : ℕ} (h : (k : ZMod M) = k') :
    zetaAway M ^ k = zetaAway M ^ k' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod k' M, pow_add, pow_add, pow_mul, pow_mul, zetaAway_pow_self M hM,
    one_pow, one_pow, h]

theorem isMultOf_unique {h M : ℕ} (hh : 1 ≤ h) {a : sympSimGrp h M} {n n' : ℕ} (hn : IsMultOf a n)
    (hn' : IsMultOf a n') : (n : ZMod M) = n' := by
  let i : Fin h := ⟨0, hh⟩
  have e1 := hn (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have e2 := hn' (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have h1 : omegaMod M (Pi.single (Sum.inl i) (1 : ZMod M)) (Pi.single (Sum.inr i) 1) = 1 := by
    simp [omegaMod, Pi.single_apply]
  rw [h1, _root_.mul_one] at e1 e2
  rw [← e1, ← e2]

end GlobalTheory.HTSympCover
end
end

