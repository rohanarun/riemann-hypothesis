module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterBlockDiagonal
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType Matrix

noncomputable section

namespace GlobalTheory.PsType.BlockTheta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_mul_char (χ η : kˣ →* ℂˣ) (x : k) : ev (χ * η) x = ev χ x * ev η x := by
  unfold ev
  split_ifs with h
  · simp
  · simp

theorem ev_one_char (x : k) : ev (1 : kˣ →* ℂˣ) x = 1 := by
  unfold ev; split_ifs <;> simp

theorem ev_at_one (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  rw [dite_eq_left (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem ev_mul_of_val (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
  unfold ev
  rw [dite_eq_left hxy, dite_eq_left hx, dite_eq_left hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (h : Triv χ 1) (x : k) : ev χ x = 1 := by
  unfold ev
  split_ifs with hx
  · have hu : χ (Units.mk0 x fun h0 => by simp [h0] at hx) = 1 := by
      refine h _ (by simpa using hx) ?_
      calc valuation k ((Units.mk0 x fun h0 => by simp [h0] at hx : kˣ) - 1 : k)
          ≤ max (valuation k x) (valuation k 1) := by rw [Units.val_mk0]; exact Valuation.map_sub _ _ _
        _ = valuation k 1 := by rw [hx, map_one, max_self]
    simp [hu]
  · rfl

theorem val_det_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) :
    valuation k g.val.det = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have h1 : ((Matrix.GeneralLinearGroup.map (n := n) (algebraMap 𝒪[k] k)) A).val.det
      = algebraMap 𝒪[k] k A.val.det := by
    simp [RingHom.map_det]
  rw [h1]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Matrix.isUnits_det_units A)

def head {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) : kˣ →* ℂˣ := if h : 0 < n then ψ ⟨0, h⟩ else 1

theorem prod_ev_nxt : ∀ (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (x : k),
    ∏ m, ev (ψ m / nxt ψ m) x = ev (head ψ) x
  | 0, ψ, x => by simp [head, ev_one_char]
  | n + 1, ψ, x => by
    rw [Fin.prod_univ_succ]
    have h1 : ∀ j : Fin n, nxt ψ j.succ = nxt (fun i => ψ i.succ) j := by
      intro j; unfold nxt
      by_cases h : (j : ℕ) + 1 < n
      · rw [dite_eq_left (by simp [Fin.val_succ]; omega), dite_eq_left h]; congr 1
      · rw [dite_eq_right (by simp [Fin.val_succ]; omega), dite_eq_right h]
    have h2 : nxt ψ 0 = head (fun i : Fin n => ψ i.succ) := by
      unfold nxt head
      by_cases h : 0 < n
      · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
      · rw [dite_eq_right (by simp; omega), dite_eq_right h]
    simp_rw [h1]
    rw [prod_ev_nxt n, ← h2, ← ev_mul_char, div_mul_cancel]
    simp [head]

variable {r t : ℕ}

theorem castAdd_eq (i : Fin r) : Fin.castAdd t i = stdSum (rfl : r + t = r + t) (Sum.inl i) := by ext; simp
theorem natAdd_eq (j : Fin t) : Fin.natAdd r j = stdSum (rfl : r + t = r + t) (Sum.inr j) := by ext; simp

theorem emb_ll (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  rw [castAdd_eq, castAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inl i))) (stdSum (rfl : r + t = r + t) (Sum.inl j))

theorem emb_lr (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) (j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inl i))) (stdSum (rfl : r + t = r + t) (Sum.inr j))

theorem emb_rl (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin t) (j : Fin r) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  rw [castAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inr i))) (stdSum (rfl : r + t = r + t) (Sum.inl j))

theorem emb_rr (a : GL (Fin r) k) (b : GL (Fin t) k) (i j : Fin t) :
    (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val (Fin.natAdd r i) (Fin.natAdd r j) = b.val i j := by
  rw [natAdd_eq, natAdd_eq]
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
    congrFun (congrFun (val_emb₂ k (stdSum (rfl : r + t = r + t)) (a, b))
      (stdSum (rfl : r + t = r + t) (Sum.inr i))) (stdSum (rfl : r + t = r + t) (Sum.inr j))

def eqvL (i : Fin r) : {y : Fin r // y ≤ i} ≃ {x : Fin (r + t) // x ≤ Fin.castAdd t i} :=
  Equiv.ofBijective (fun y : {y : Fin r // y ≤ i} => (⟨Fin.castAdd t y.1, by
      have := y.2; simp only [Fin.le_def, Fin.coe_castAdd] at this ⊢; omega⟩ :
        {x : Fin (r + t) // x ≤ Fin.castAdd t i})) (by
    constructor
    · rintro ⟨y, hy⟩ ⟨z, hz⟩ h
      simp only [Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd] at h
      exact Subtype.ext (Fin.ext h)
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ i := by simpa [Fin.le_def] using hx
      exact ⟨⟨⟨x, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp⟩)

theorem eqvL_val (i : Fin r) (y : {y : Fin r // y ≤ i}) : ((eqvL (t := t) i y) : Fin (r + t)) = Fin.castAdd t y.1 := rfl

def eqvR (j : Fin t) : Fin r ⊕ {y : Fin t // y ≤ j} ≃ {x : Fin (r + t) // x ≤ Fin.natAdd r j} :=
  Equiv.ofBijective (Sum.elim (fun i : Fin r => (⟨Fin.castAdd t i, by
        simp only [Fin.le_def, Fin.coe_castAdd, Fin.coe_natAdd]; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))
      (fun y : {y : Fin t // y ≤ j} => (⟨Fin.natAdd r y.1, by
        have := y.2; simp only [Fin.le_def, Fin.coe_natAdd] at this ⊢; omega⟩ : {x : Fin (r + t) // x ≤ Fin.natAdd r j}))) (by
    constructor
    · intro u v h
      rcases u with y | y <;> rcases v with z | z <;>
        simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Fin.ext_iff, Fin.coe_castAdd,
          Fin.coe_natAdd] at h
      · exact congrArg Sum.inl (Fin.ext h)
      · have := y.2; omega
      · have := z.2; omega
      · exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨x, hx⟩
      have hx' : (x : ℕ) ≤ r + j := by simpa [Fin.le_def] using hx
      by_cases h : (x : ℕ) < r
      · exact ⟨Sum.inl ⟨x, h⟩, by ext; simp⟩
      · exact ⟨Sum.inr ⟨⟨x - r, by omega⟩, by simp [Fin.le_def]; omega⟩, by ext; simp; omega⟩)

theorem eqvR_inl (j : Fin t) (i : Fin r) : ((eqvR j (Sum.inl i)) : Fin (r + t)) = Fin.castAdd t i := rfl
theorem eqvR_inr (j : Fin t) (y : {y : Fin t // y ≤ j}) : ((eqvR (r := r) j (Sum.inr y)) : Fin (r + t)) = Fin.natAdd r y.1 := rfl

theorem minor_castAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (i : Fin r) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.castAdd t i) = minor a i := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvL i)]
  congr 1
  ext y z
  simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvL_val, emb_ll]

theorem minor_natAdd (a : GL (Fin r) k) (b : GL (Fin t) k) (j : Fin t) :
    minor (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) (Fin.natAdd r j) = a.val.det * minor b j := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (eqvR j)]
  rw [show ((emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)).val.toSquareBlockProp fun x => x ≤ Fin.natAdd r j).submatrix (eqvR j) (eqvR j)
      = fromBlocks a.val 0 0 (b.val.toSquareBlockProp fun x => x ≤ j) by
    ext (y | y) (z | z) <;> simp only [toSquareBlockProp, toBlock, submatrix_apply, eqvR_inl, eqvR_inr,
      emb_ll, emb_lr, emb_rl, emb_rr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.zero_apply]]
  rw [det_fromBlocks_zero₂₁]

theorem minor_last {r : ℕ} (a : GL (Fin (r + 1)) k) : minor a (Fin.last r) = a.val.det := by
  unfold minor
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Fin.le_last x)).symm]
  congr 1

theorem nxt_natAdd (ψ : Fin (r + t) → kˣ →* ℂˣ) (j : Fin t) :
    nxt ψ (Fin.natAdd r j) = nxt (fun i => ψ (Fin.natAdd r i)) j := by
  unfold nxt
  by_cases h : (j : ℕ) + 1 < t
  · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
  · rw [dite_eq_right (by simp; omega), dite_eq_right h]

theorem nxt_castAdd_castSucc {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) (i : Fin r) :
    nxt ψ (Fin.castAdd t i.castSucc) = nxt (fun i => ψ (Fin.castAdd t i)) i.castSucc := by
  unfold nxt
  rw [dite_eq_left (by simp; omega), dite_eq_left (by simp)]
  congr 1

theorem nxt_castAdd_last {r : ℕ} (ψ : Fin (r + 1 + t) → kˣ →* ℂˣ) :
    nxt ψ (Fin.castAdd t (Fin.last r)) = head (fun j : Fin t => ψ (Fin.natAdd (r + 1) j)) := by
  unfold nxt head
  by_cases h : 0 < t
  · rw [dite_eq_left (by simp; omega), dite_eq_left h]; congr 1
  · rw [dite_eq_right (by simp; omega), dite_eq_right h]

theorem nxt_last_one {r : ℕ} (φ : Fin (r + 1) → kˣ →* ℂˣ) : nxt φ (Fin.last r) = 1 := by
  unfold nxt; rw [dite_eq_right (by simp)]

theorem first_part : ∀ (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (a : GL (Fin r) k),
    (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
      ev (head fun j : Fin t => ψ (Fin.natAdd r j)) a.val.det = theta (fun i => ψ (Fin.castAdd t i)) a
  | 0, t, ψ, a => by simp [theta, Matrix.det_isEmpty, ev_at_one]
  | r + 1, t, ψ, a => by
    unfold theta
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc, minor_last, nxt_castAdd_last,
      nxt_last_one, ← ev_mul_char, div_mul_cancel, div_one]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [nxt_castAdd_castSucc]

end GlobalTheory.PsType.BlockTheta


open GlobalTheory.PsType.BlockTheta in
theorem GlobalTheory.PsType.theta_emb₂_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp (fun i => ψ (Fin.castAdd t i)), ∀ b ∈ grp (fun i => ψ (Fin.natAdd r i)), theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) = theta (fun i => ψ (Fin.castAdd t i)) a * theta (fun i => ψ (Fin.natAdd r i)) b := by
  intro k _ _ _ _ r t ψ hord a ha b hb
  have hord₂ : Ordered (fun i => ψ (Fin.natAdd r i)) := by
    intro i a' b' j h1 h2 h3 x hx
    exact hord (Fin.natAdd r i) (Fin.natAdd r a') (Fin.natAdd r b') (Fin.natAdd r j) (by rw [Fin.le_def] at h1 ⊢; simp only [Fin.coe_natAdd]; omega) (by rw [Fin.le_def] at h2 ⊢; simp only [Fin.coe_natAdd]; omega)
      (by rw [Fin.le_def] at h3 ⊢; simp only [Fin.coe_natAdd]; omega) x hx
  have hda : valuation k a.val.det = 1 := val_det_of_mem_KO ha.1
  have hsplit : theta ψ (emb₂ k (stdSum (rfl : r + t = r + t)) (a, b)) =
      (∏ i : Fin r, ev (ψ (Fin.castAdd t i) / nxt ψ (Fin.castAdd t i)) (minor a i)) *
        ((∏ j : Fin t, ev ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) a.val.det) *
          theta (fun i => ψ (Fin.natAdd r i)) b) := by
    unfold theta
    rw [Fin.prod_univ_add]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [minor_castAdd]
    · rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [minor_natAdd, nxt_natAdd]
      by_cases hT : Triv ((fun i => ψ (Fin.natAdd r i)) j / nxt (fun i => ψ (Fin.natAdd r i)) j) 1
      · rw [_root_.GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, _root_.GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, _root_.GlobalTheory.PsType.BlockTheta.ev_of_triv_one _ hT, one_mul]
      · exact ev_mul_of_val _ hda ((_root_.GlobalTheory.PsType.minor_mul_mod k t _ hord₂ j hT).1 b hb)
  rw [hsplit, prod_ev_nxt, ← mul_assoc, first_part]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterEqOneNearOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ev_one' (χ : kˣ →* ℂˣ) : ev χ (1 : k) = 1 := by
  unfold ev
  simp

theorem minor_one' {n : ℕ} (m : Fin n) : minor (1 : GL (Fin n) k) m = 1 := by
  unfold minor
  simp [Matrix.toSquareBlockProp]

theorem continuous_minor' {n : ℕ} (m : Fin n) : Continuous fun g : GL (Fin n) k => minor g m := by
  unfold minor
  exact (Units.continuous_val.matrix_submatrix _ _).matrix_det

theorem ev_eventually_one (χ : kˣ →* ℂˣ) (S : Set k) (hS : S ∈ nhds (0 : k)) (hT : ∀ x ∈ S, Triv χ x) :
    ∀ᶠ x in nhds (1 : k), ev χ x = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := triv_ev_props k
  have hball : {x : k | valuation k (x - 1) < 1} ∈ nhds (1 : k) :=
    (IsValuativeTopology.hasBasis_nhds' (1 : k)).mem_of_mem one_ne_zero
  have hpre : (fun x : k => x - 1) ⁻¹' S ∈ nhds (1 : k) :=
    (continuous_sub_right (1 : k)).continuousAt.preimage_mem_nhds (by simpa using hS)
  filter_upwards [hball, hpre] with x hx hxS
  have hv : valuation k x = 1 := by
    have : x = 1 + (x - 1) := by ring
    rw [this]
    exact Valuation.map_one_add_of_lt _ hx
  rw [h8 χ x 1 hv (by simp) (hT _ hxS), ev_one']

theorem theta_one_and_near : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) →
    theta ψ 1 = 1 ∧ ∃ U ∈ nhds (1 : GL (Fin n) k), ∀ g ∈ U, theta ψ g = 1 := by
  intro k _ _ _ _ n ψ hψ
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -⟩ := triv_ev_props k
  have hset : ∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → {x : k | Triv χ x} ∈ nhds (0 : k) := fun χ hχ =>
    (h6 χ hχ).1.mem_nhds (h3 χ)
  have hnxt : ∀ m, {x : k | Triv (nxt ψ m) x} ∈ nhds (0 : k) := by
    intro m
    unfold nxt
    split_ifs with h
    · exact hset _ (hψ _)
    · refine Filter.univ_mem' fun x => ?_
      intro u _ _
      rfl
  have hev : ∀ m, ∀ᶠ x in nhds (1 : k), ev (ψ m / nxt ψ m) x = 1 := fun m =>
    ev_eventually_one _ _ (Filter.inter_mem (hset _ (hψ m)) (hnxt m)) fun x hx => by
      rw [div_eq_mul_inv]
      exact h4 _ _ x hx.1 (h5 _ x hx.2)
  refine ⟨?_, ?_⟩
  · unfold theta
    exact Finset.prod_eq_one fun m _ => by rw [minor_one', ev_one']
  · have hall : ∀ᶠ g in nhds (1 : GL (Fin n) k), ∀ m, ev (ψ m / nxt ψ m) (minor g m) = 1 := by
      rw [Filter.eventually_all]
      intro m
      have hc := (continuous_minor' (k := k) m).continuousAt (x := 1)
      rw [ContinuousAt, minor_one'] at hc
      exact hc.eventually (hev m)
    exact ⟨_, hall, fun g hg => Finset.prod_eq_one fun m _ => hg m⟩

end

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesUnipotentStripProperties
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_int_det {I : Type} [Fintype I] [DecidableEq I] {g : GL I k}
    (hM : ∀ i j, valuation k (g.val i j) ≤ 1) (hd : valuation k g.val.det = 1) : g ∈ KO k I := by
  classical
  let M : Matrix I I 𝒪[k] := fun i j => ⟨g.val i j, (Valuation.mem_integer_iff _ _).2 (hM i j)⟩
  have hmap : M.map (algebraMap 𝒪[k] k) = g.val := by
    ext i j
    rfl
  have hdet : IsUnit M.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_of_one' ?_
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hd]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det M).2 hdet
  refine ⟨u, ?_⟩
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, hu]
  rfl

end GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem strip_off {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ))) : y.val i j = (1 : Matrix (Fin n) (Fin n) k) i j := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_neg h] at h0
  exact h0

theorem strip_on {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : (i : ℕ) < r ∧ r ≤ (j : ℕ)) :
    valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) := by
  simp only [strip, Set.mem_ofPred_eq] at hy
  have h0 := hy i j
  rw [if_pos h] at h0
  exact h0

theorem strip_lower {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i j : Fin n) (h : j < i) : y.val i j = 0 := by
  have hji : (j : ℕ) < (i : ℕ) := h
  rw [strip_off hy i j (fun hc => by omega), Matrix.one_apply_ne (ne_of_gt h)]

theorem strip_diag {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m)
    (i : Fin n) : y.val i i = 1 := by
  rw [strip_off hy i i (fun hc => by omega), Matrix.one_apply_eq]

theorem strip_det {ψ : Fin n → kˣ →* ℂˣ} {r : ℕ} {ϖ : k} {m : ℕ} {y : GL (Fin n) k} (hy : y ∈ strip ψ r ϖ m) :
    y.val.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j h => strip_lower hy i j h)]
  simp [strip_diag hy]

theorem strip_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → Cut ψ r → (∀ y ∈ strip ψ r ϖ 0, y ∈ grp ψ) ∧ (∀ m, ∀ y ∈ strip ψ r ϖ m, theta ψ y = 1) ∧ (∀ y ∈ strip ψ r ϖ 1, y ∈ KO k (Fin n)) ∧ ∀ (z : GL (Fin n) k), z.val = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then ϖ else 1) → ∀ m y, y ∈ strip ψ r ϖ (m + 1) ↔ z * y * z⁻¹ ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ n ψ r ϖ hϖ hϖ1 hunif hcut
  have hent : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → ∀ i j : Fin n,
      ¬ ((i : ℕ) < r ∧ r ≤ (j : ℕ)) → valuation k (y.val i j) ≤ 1 := by
    intro m y hy i j h
    rw [strip_off hy i j h]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have hdet1 : ∀ (m : ℕ) (y : GL (Fin n) k), y ∈ strip ψ r ϖ m → valuation k y.val.det = 1 := by
    intro m y hy
    rw [strip_det hy, map_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    refine (show y ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (y.val i j) from ⟨?_, ?_⟩)
    · refine mem_KO_of_int_det (fun i j => ?_) (hdet1 0 y hy)
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).1
        rwa [pow_zero, one_mul] at h0
      · exact hent 0 y hy i j h
    · intro i j hij
      by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
      · have h0 := (strip_on hy i j h).2
        rwa [pow_zero, one_mul] at h0
      · rw [strip_off hy i j h, Matrix.one_apply_ne (ne_of_lt hij)]
        exact triv_zero _
  · intro m y hy
    rw [_root_.GlobalTheory.PsType.theta_of_triangular k n ψ y (fun _ => 1) (fun _ => by simp) (fun i => by simp [strip_diag hy i])
      (Or.inr fun i j h => strip_lower hy i j h)]
    simp
  · intro y hy
    refine mem_KO_of_int_det (fun i j => ?_) (hdet1 1 y hy)
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · obtain ⟨h1, h2⟩ := strip_on hy i j h
      rw [pow_one] at h1 h2
      have hlt : valuation k (ϖ * y.val i j) < 1 := by
        refine lt_of_le_of_ne h1 fun heq => hcut i j h.1 h.2 ?_
        exact triv_mono _ _ _ (le_of_eq (by rw [heq, map_one])) h2
      have hle := hunif _ hlt
      rw [map_mul] at hle
      have hpos : 0 < valuation k ϖ := zero_lt_iff.2 ((map_ne_zero _).2 hϖ)
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    · exact hent 1 y hy i j h
  · intro z hz m y
    set d : Fin n → k := fun i : Fin n => if (i : ℕ) < r then ϖ else 1 with hd_def
    have hd : ∀ i, d i ≠ 0 := by
      intro i
      simp only [hd_def]
      split_ifs
      exacts [hϖ, one_ne_zero]
    have hzz : z.val * (z⁻¹).val = 1 := by simp
    have hzinv : (z⁻¹).val = Matrix.diagonal (fun i => (d i)⁻¹) := by
      calc (z⁻¹).val = (Matrix.diagonal (fun i => (d i)⁻¹) * z.val) * (z⁻¹).val := by
            rw [hz, Matrix.diagonal_mul_diagonal]
            rw [show (fun i => (d i)⁻¹ * d i) = fun _ => (1 : k) from funext fun i => inv_mul_cancel₀ (hd i)]
            rw [Matrix.diagonal_one, one_mul]
        _ = Matrix.diagonal (fun i => (d i)⁻¹) := by rw [mul_assoc, hzz, mul_one]
    have hentry : ∀ i j : Fin n, (z * y * z⁻¹).val i j = d i * y.val i j * (d j)⁻¹ := by
      intro i j
      rw [Units.val_mul, Units.val_mul, hz, hzinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [strip, Set.mem_ofPred_eq, hentry]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · rw [if_pos h, if_pos h]
      have hdi : d i = ϖ := by simp only [hd_def]; rw [if_pos h.1]
      have hdj : d j = 1 := by simp only [hd_def]; rw [if_neg (by omega)]
      rw [hdi, hdj, show ϖ ^ m * (ϖ * y.val i j * (1 : k)⁻¹) = ϖ ^ (m + 1) * y.val i j by ring]
    · rw [if_neg h, if_neg h]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.one_apply_eq, mul_comm (d i), mul_inv_cancel_right₀ (hd i)]
      · rw [Matrix.one_apply_ne hij]
        simp [hd i, hd j]

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevelStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGaloisAction_preserves_gammaLevel : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  first | exact @GlobalTheory.Tower.gal_level | exact GlobalTheory.Tower.gal_level | (intros; apply GlobalTheory.Tower.gal_level <;> assumption)
end

