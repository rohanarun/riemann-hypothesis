module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.Smooth
section
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section smoothAt

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}

lemma sm_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} :
    ContDiffAt ℝ n F x₀ ↔ ∀ i j, ContDiffAt ℝ n (fun x => F x i j) x₀ := by
  exact contDiffAt_pi.trans (forall_congr' fun i => contDiffAt_pi)

lemma sm_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {F : X → Matrix ι κ ℂ} {G : X → Matrix κ μ ℂ}
    (hF : ContDiffAt ℝ n F x₀) (hG : ContDiffAt ℝ n G x₀) : ContDiffAt ℝ n (fun x => F x * G x) x₀ := by
  rw [sm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma sm_conjT {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x)ᴴ) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (Complex.conjCLE.contDiff.contDiffAt).comp x₀ (hF j i)

private lemma contDiffAt_finset_prod' {ι : Type*} (s : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ s, ContDiffAt ℝ n (f i) x₀) : ContDiffAt ℝ n (fun x => ∏ i ∈ s, f i x) x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ n (fun _ : X => (1 : ℂ)) x₀)
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma sm_det {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => (F x).det) x₀ := by
  rw [sm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun τ _ => contDiffAt_const.mul (contDiffAt_finset_prod' _ _ fun i _ => hF (τ i) i)

lemma sm_updateRow {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (j : ι) (b : ι → ℂ) : ContDiffAt ℝ n (fun x => (F x).updateRow j b) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i l
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hF i l

lemma sm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (hu : (F x₀).det ≠ 0) : ContDiffAt ℝ n (fun x => (F x)⁻¹) x₀ := by
  rw [sm_iff]
  intro i l
  simp only [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact ((sm_det hF).inv hu).mul (sm_det (sm_updateRow hF l _))

lemma sm_fromBlocks {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} {C : X → Matrix ι' κ ℂ} {D : X → Matrix ι' κ' ℂ}
    (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) (hC : ContDiffAt ℝ n C x₀) (hD : ContDiffAt ℝ n D x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x)) x₀ := by
  rw [sm_iff] at hA hB hC hD ⊢
  rintro (i | i) (j | j)
  · simpa only [Matrix.fromBlocks_apply₁₁] using hA i j
  · simpa only [Matrix.fromBlocks_apply₁₂] using hB i j
  · simpa only [Matrix.fromBlocks_apply₂₁] using hC i j
  · simpa only [Matrix.fromBlocks_apply₂₂] using hD i j

lemma sm_fromRows {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [Fintype κ]
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι' κ ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromRows (A x) (B x)) x₀ := by
  rw [sm_iff] at hA hB ⊢
  rintro (i | i) j
  · simpa only [Matrix.fromRows_apply_inl] using hA i j
  · simpa only [Matrix.fromRows_apply_inr] using hB i j

lemma sm_fromCols {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromCols (A x) (B x)) x₀ := by
  rw [sm_iff] at hA hB ⊢
  rintro i (j | j)
  · simpa only [Matrix.fromCols_apply_inl] using hA i j
  · simpa only [Matrix.fromCols_apply_inr] using hB i j

lemma sm_reindex {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => Matrix.reindex e₁ e₂ (F x)) x₀ := by
  rw [sm_iff] at hF ⊢
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply] using hF (e₁.symm i) (e₂.symm j)

end smoothAt

section slice

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}

lemma sm_of {s : ℕ} (Z : G.Mat s) : ContDiffAt ℝ n (fun Z' : G.Mat s => Matrix.of Z') Z := by
  rw [sm_iff]
  intro i j
  simp only [Matrix.of_apply]
  exact (contDiff_apply_apply ℝ i j).contDiffAt

lemma mMap_sm {k j ρ : ℕ} {M : X → Matrix (Fin j) (Fin j) ℂ} (hM : ContDiffAt ℝ n M x₀)
    (hdet : (M x₀).det ≠ 0) (γ : B.Mat k ρ) : ContDiffAt ℝ n (fun x => mMap k j ρ (M x) γ) x₀ := by
  have hdet' : ((M x₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hdet
  simp only [mMap, blk3]
  refine sm_reindex _ _ (sm_fromBlocks contDiffAt_const ?_ ?_ contDiffAt_const)
  · exact sm_fromRows (sm_mul (sm_inv (sm_conjT hM) hdet') contDiffAt_const) contDiffAt_const
  · exact sm_fromCols (sm_mul contDiffAt_const hM) contDiffAt_const

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

lemma permutationMatrix_eq_permMatrix' (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private lemma det_one_add_strictLower {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, a ≤ b → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : i < j := hij
    simp [Matrix.one_apply_ne hij'.ne, h i j hij'.le]

private lemma det_one_add_strictUpper' {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (h : ∀ a b, b ≤ a → M a b = 0) :
    (1 + M).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [h _ _ le_rfl]
  · intro i j hij
    have hij' : j < i := hij
    simp [Matrix.one_apply_ne hij'.ne', h i j hij'.le]

lemma rn_mem' (hRP : RadicalParam) (j : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have hr : Rn k j ρ x ∈ Rset k j ρ := (hRP k j ρ).2.1 ▸ Set.mem_range_self x
  exact ((hRP k j ρ).2.2 hr).1

private lemma mul_mem_GV' {k r : ℕ} {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) :
    a * b ∈ B.GV k r :=
  (Formalism.QuantumDeterminants.unitary_group_holds _ _
    (Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r))).2.1 a ha b hb

lemma gaXi_mem (hSM : SliceMem) (hRP : RadicalParam) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) {Z : G.Mat s}
    (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  exact mul_mem_GV' (mul_mem_GV' (P.BetaSesquilinearity.gv_inv (rn_mem' hRP (p + s) ξ.1.1))
    ((hSM k (p + s) ρ).1 _ γ (det_zjH_ne hd ξ.2 hZ) hγ)) (rn_mem' hRP (p + s) ξ.1.2)

lemma zjH_sm (η : XiH p s σ) (Z : G.Mat s) : ContDiffAt ℝ n (fun Z' : G.Mat s => ZjH σ d η Z') Z := by
  simp only [ZjH, Zj, blk2]
  refine sm_mul (sm_mul contDiffAt_const ?_) contDiffAt_const
  exact sm_reindex _ _ (sm_fromBlocks contDiffAt_const contDiffAt_const contDiffAt_const (sm_of Z))

lemma gaXi_sm (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (γ : B.Mat k ρ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    ContDiffAt ℝ n (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
  have hz := zjH_sm (n := n) (d := d) ξ.2 Z
  simp only [gaXi]
  exact sm_mul (sm_mul contDiffAt_const (mMap_sm hz (det_zjH_ne hd ξ.2 hZ) γ)) contDiffAt_const

end slice

theorem zSmooth : ZSmooth := by
  intro hSM hRP k p s ρ σ d hd E _ _ H m hH ξ Z γ hZ hγ
  have hmem := gaXi_mem hSM hRP hd ξ γ hZ hγ
  have hsm : ContDiffAt ℝ m (fun Z' => gaXi k ρ σ d ξ Z' γ) Z := gaXi_sm hd ξ γ hZ
  refine ⟨hmem, hsm.continuousAt, ?_⟩
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hH _ hmem
  have hcomp : ContDiffAt ℝ m (fun Z' => f' (gaXi k ρ σ d ξ Z' γ)) Z :=
    (hf'.contDiffAt (hU.mem_nhds hgU)).comp Z hsm
  refine hcomp.congr_of_eventuallyEq ?_
  have hdet : ∀ᶠ Z' in 𝓝 Z, G.detM Z' ≠ 0 := by
    have hc : ContinuousAt (fun Z' : G.Mat s => G.detM Z') Z := by
      simp only [G.detM]
      exact (sm_det (n := 0) (sm_of Z)).continuousAt
    exact hc.eventually_ne hZ
  have hU' : ∀ᶠ Z' in 𝓝 Z, gaXi k ρ σ d ξ Z' γ ∈ U :=
    hsm.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  filter_upwards [hdet, hU'] with Z' h1 h2
  exact hfe _ h2 (gaXi_mem hSM hRP hd ξ γ h1 hγ)

end PI.UnitaryGroupMassFormula.UsCost
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.UnitarySumCostOfParts
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem top_prod_map_le {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x ∧ f x ≤ c) (hc : 0 ≤ c) : (l.map f).prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 0 ≤ f a ∧ f a ≤ c := hf a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ f x ∧ f x ≤ c := fun x hx => hf x (by simp [hx])
    have h0 : 0 ≤ (t.map f).prod := by
      apply List.prod_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact (ht x hx).1
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul ha.2 (ih ht) h0 hc

theorem top_lsz_ge_one {k r : ℕ} (X : B.Mat k r) : 1 ≤ lsz X := by
  unfold lsz
  exact le_max_left _ _

theorem top_prod_lsz_nonneg {k r : ℕ} (l : List (B.Mat k r)) : 0 ≤ (l.map lsz).prod := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨X, -, rfl⟩ := List.mem_map.1 ha
  exact le_trans zero_le_one (top_lsz_ge_one X)

theorem top_gN_nonneg {k r : ℕ} (g : B.Mat k r) : 0 ≤ B.gN g := by
  unfold B.gN
  exact Real.sqrt_nonneg _

theorem unitarySum_cost_of_parts (hW : WordsId) (hL : LetterSize) (hS : StarScale) (hC : CommLR) (hO : OffK)
    (hZS : ZSmooth) (hZ : ZCost) : DerivativeCostFromComponents := by
  intro hM hR hRt hLt hZt hD hS21
  intro k p s ρ σ d hd hs K hK hKpos Q
  obtain ⟨CL, hCL⟩ := hL k (p + s) ρ
  obtain ⟨CS, hCS⟩ := hS21 k p s ρ σ d hd hs K hK hKpos
  choose Cz hCz using fun q : ℕ => hZ hM hR hZt hD hS21 k p s ρ σ d hd hs K hK hKpos q
  set C1 : ℝ := max 1 (CL * CS ^ 2) with hC1def
  have hC1ge : 1 ≤ C1 := le_max_left _ _
  refine ⟨(∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q, ?_⟩
  intro E _ _ F₁ A₁ B₁ hStar ξ u v q hu hv hq Z γ hZdet hγ
  let u' := u.map (cj k (p + s) ρ ξ.1.1)
  let v' := v.map (cj k (p + s) ρ ξ.1.2)
  let H : B.Mat k (p + s + ρ) → E := B.dLR u' v' F₁
  have hfun : (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) =
      fun Z' => H (gaXi k ρ σ d ξ Z' γ) := by
    funext Z'
    exact congrFun (hW hLt hRt k p s ρ σ d ξ Z' E F₁ u v) γ
  rw [hfun]
  have hcjP : ∀ (x : RC k (p + s) ρ) (Y : B.Mat k ρ), B.unitLie k ρ Y →
      inLieP k (p + s) ρ (cj k (p + s) ρ x Y) :=
    fun x Y hY => (hD k (p + s) ρ x).1 Y hY.1
  have hu' : ∀ X ∈ u', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hu Y hY)
  have hv' : ∀ X ∈ v', inLieP k (p + s) ρ X := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact hcjP _ Y (hv Y hY)
  have hwl : ∀ x ∈ wL u' ++ wR v', B.inLie k (p + s + ρ) x.2 := by
    intro x hx
    simp only [List.mem_append, wL, wR, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu' X hX).1
    · exact (hv' X hX).1
  have hHeq : H = Dw (wL u' ++ wR v') F₁ := dLR_eq _ _ _
  have hg0 : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) :=
    (hZS hM hR k p s ρ σ d hd E F₁ Q hStar.1 ξ Z γ hZdet hγ).1
  have hB₁ : 0 ≤ B₁ := by
    have h0 := hStar.2.2 [] [] (by simp [unitP]) (by simp [unitP]) (by simp) _ hg0
    exact le_trans (mul_nonneg (Real.rpow_nonneg (top_gN_nonneg _) _) (norm_nonneg _)) h0
  have hC0 : 0 ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q :=
    mul_nonneg (Finset.sum_nonneg fun q _ => le_max_right _ _) (pow_nonneg (le_trans zero_le_one hC1ge) _)
  by_cases hKg : ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K
  · obtain ⟨hg1, hRn1, hRn2, -⟩ := hCS ξ Z γ hγ hKg
    set g0 := gaXi k ρ σ d ξ Z γ with hg0def
    set X0 := B.gN g0 with hX0def
    have hX0pos : 0 < X0 := lt_of_lt_of_le zero_lt_one hg1
    have hX0nn : 0 ≤ X0 := hX0pos.le
    have hCkH : B.CkOn (q : ℕ∞) (B.GV k (p + s + ρ)) H := by
      rw [hHeq]
      apply CkOn_Dw hwl
      apply sCkOn_mono _ hStar.1
      have hl : q + (u.length + v.length) ≤ Q := by omega
      simp only [List.length_append, wL, wR, List.length_map, u', v']
      exact_mod_cast hl
    let β : ℝ := B₁ * X0 ^ (-A₁) * ((u'.map lsz).prod * (v'.map lsz).prod)
    have hw : ∀ w : List (B.Mat k (p + s + ρ)), (∀ X ∈ w, inLieP k (p + s) ρ X) → w.length ≤ q →
        ‖B.Rw w H g0‖ ≤ β * (w.map lsz).prod := by
      intro w hwP hwl'
      have hcomm := hC k (p + s + ρ) E F₁ Q hStar.1 u' v' w (fun X hX => (hu' X hX).1)
        (fun X hX => (hv' X hX).1) (fun X hX => (hwP X hX).1)
        (by simp only [List.length_map, u', v']; omega) g0 hg0
      rw [hcomm]
      have hsc := hS k (p + s) ρ E F₁ A₁ Q B₁ K hStar u' (w ++ v') hu'
        (by
          intro X hX
          rcases List.mem_append.1 hX with h | h
          · exact hwP X h
          · exact hv' X h)
        (by simp only [List.length_append, List.length_map, u', v']; omega) g0 hg0
      have hprod : ((u' ++ (w ++ v')).map lsz).prod =
          (u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod) := by
        simp only [List.map_append, List.prod_append]
      rw [hprod] at hsc
      have hpowpos : 0 < X0 ^ A₁ := Real.rpow_pos_of_pos hX0pos _
      have hle : ‖B.dLR u' (w ++ v') F₁ g0‖ ≤
          B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := by
        rw [le_div_iff₀ hpowpos]
        linarith [hsc]
      calc ‖B.dLR u' (w ++ v') F₁ g0‖
          ≤ B₁ * ((u'.map lsz).prod * ((w.map lsz).prod * (v'.map lsz).prod)) / X0 ^ A₁ := hle
        _ = β * (w.map lsz).prod := by
          simp only [β]
          rw [Real.rpow_neg hX0nn]
          field_simp
    obtain ⟨hcd, hbd⟩ := hCz q E H β hCkH ξ Z γ hZdet hγ hKg hw
    refine ⟨hcd, le_trans hbd ?_⟩
    have hlet : ∀ x : RC k (p + s) ρ, B.gN (Rn k (p + s) ρ x) ≤ CS * X0 ^ (p + s) →
        ∀ Y, B.unitLie k ρ Y → lsz (cj k (p + s) ρ x Y) ≤ C1 * X0 ^ (2 * (p + s + ρ)) := by
      intro x hx Y hY
      have h1 := hCL x Y hY.2
      have hn0 : 0 ≤ B.gN (Rn k (p + s) ρ x) := top_gN_nonneg _
      have hl1 := top_lsz_ge_one (cj k (p + s) ρ x Y)
      have hCL0 : 0 ≤ CL := by nlinarith [sq_nonneg (B.gN (Rn k (p + s) ρ x))]
      have hsq : B.gN (Rn k (p + s) ρ x) ^ 2 ≤ (CS * X0 ^ (p + s)) ^ 2 := pow_le_pow_left₀ hn0 hx 2
      calc lsz (cj k (p + s) ρ x Y) ≤ CL * B.gN (Rn k (p + s) ρ x) ^ 2 := h1
        _ ≤ CL * (CS * X0 ^ (p + s)) ^ 2 := mul_le_mul_of_nonneg_left hsq hCL0
        _ = (CL * CS ^ 2) * X0 ^ (2 * (p + s)) := by ring
        _ ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
          mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hg1 (by omega)) (pow_nonneg hX0nn _)
            (le_trans zero_le_one hC1ge)
    have hc : 0 ≤ C1 * X0 ^ (2 * (p + s + ρ)) :=
      mul_nonneg (le_trans zero_le_one hC1ge) (pow_nonneg hX0nn _)
    have hu'b : (u'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ u.length := by
      have h := top_prod_map_le u' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn1 Y (hu Y hY)⟩) hc
      simpa only [List.length_map, u'] using h
    have hv'b : (v'.map lsz).prod ≤ (C1 * X0 ^ (2 * (p + s + ρ))) ^ v.length := by
      have h := top_prod_map_le v' lsz (C1 * X0 ^ (2 * (p + s + ρ)))
        (fun X hX => by
          obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
          exact ⟨le_trans zero_le_one (top_lsz_ge_one _), hlet _ hRn2 Y (hv Y hY)⟩) hc
      simpa only [List.length_map, v'] using h
    have hβ : β ≤ B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by
      have h1 : (u'.map lsz).prod * (v'.map lsz).prod ≤
          (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) := by
        rw [pow_add]
        exact mul_le_mul hu'b hv'b (top_prod_lsz_nonneg _) (pow_nonneg hc _)
      have h2 : (C1 * X0 ^ (2 * (p + s + ρ))) ^ (u.length + v.length) ≤
          C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1ge (by omega)) (pow_nonneg hX0nn _)
      exact mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
    have hβ0 : 0 ≤ β :=
      mul_nonneg (mul_nonneg hB₁ (Real.rpow_nonneg hX0nn _))
        (mul_nonneg (top_prod_lsz_nonneg _) (top_prod_lsz_nonneg _))
    have hX5 : 0 ≤ X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) := Real.rpow_nonneg hX0nn _
    have hexp : X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
          2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) =
        X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
          X0 ^ (2 * (p + s + ρ) * (u.length + v.length)) := by
      rw [Real.rpow_add hX0pos, Real.rpow_add hX0pos, ← Real.rpow_natCast]
      congr 2
      push_cast
      ring
    have hmax : max (Cz q) 0 ≤ ∑ q ∈ Finset.range (Q + 1), max (Cz q) 0 :=
      Finset.single_le_sum (f := fun q => max (Cz q) 0) (fun i _ => le_max_right _ _)
        (Finset.mem_range.mpr (by omega))
    calc Cz q * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ))
        ≤ max (Cz q) 0 * β * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hβ0) hX5
      _ ≤ max (Cz q) 0 * (B₁ * X0 ^ (-A₁) * (C1 ^ Q * X0 ^ (2 * (p + s + ρ) * (u.length + v.length)))) *
            X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (le_max_right _ _)) hX5
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * (X0 ^ (-A₁) * X0 ^ (5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ)) *
            X0 ^ (2 * (p + s + ρ) * (u.length + v.length))) := by ring
      _ = max (Cz q) 0 * C1 ^ Q * B₁ * X0 ^ (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) +
            2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by rw [hexp]
      _ ≤ (∑ q ∈ Finset.range (Q + 1), max (Cz q) 0) * C1 ^ Q * B₁ * X0 ^ (-A₁ +
            5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) + 2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0nn _)
          apply mul_le_mul_of_nonneg_right _ hB₁
          exact mul_le_mul_of_nonneg_right hmax (pow_nonneg (le_trans zero_le_one hC1ge) _)
  · have hcont : Continuous fun g : B.Mat k (p + s + ρ) => ‖DjU k (p + s) ρ g‖ := by
      have hZc : Continuous fun g : B.Mat k (p + s + ρ) => Zh k (p + s) ρ g :=
        continuous_pi fun a => continuous_pi fun b => (continuous_apply _).comp (continuous_apply _)
      exact hZc.matrix_det.norm
    have hOopen : IsOpen {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} :=
      hK.isClosed.isOpen_compl.preimage hcont
    have hF0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        F₁ g = 0 := by
      intro g hg hgO
      by_contra hne
      exact hgO (hStar.2.1 g hg hne)
    have hH0 : ∀ g ∈ B.GV k (p + s + ρ), g ∈ {g : B.Mat k (p + s + ρ) | ‖DjU k (p + s) ρ g‖ ∉ K} →
        H g = 0 := by
      intro g hg hgO
      rw [hHeq]
      exact Dw_vanish hOopen hwl hF0 g hg hgO
    obtain ⟨hcd, hz⟩ := hO hM hR k p s ρ σ d hd E H _ hOopen hH0 ξ Z γ hZdet hγ hKg q
    refine ⟨hcd, ?_⟩
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 hB₁) (Real.rpow_nonneg (top_gN_nonneg _) _)

end PI.UnitaryGroupMassFormula.UsCost
end
end

