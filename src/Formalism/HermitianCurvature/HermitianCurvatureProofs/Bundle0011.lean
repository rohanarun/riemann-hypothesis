module

public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.Bundle0003
public import Formalism.HermitianCurvature.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007
public import Mathlib
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FinitePointSets
section
namespace Formalism.FourierDecayAlt.P.FinitePointSets

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem finite_pts {E : Type} [Field E] (S : Finset E) (i : ℕ) :
    {p : Pt E | level p = i ∧
      ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ S}.Finite := by
  classical
  set F : Finset (ℕ × E) := (range (i + 1)) ×ˢ S with hFdef
  refine ((List.finite_length_le F i).image (List.map Subtype.val)).subset ?_
  rintro p ⟨hl, hp⟩
  have hmem : ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ∈ S := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact hp k hk
  unfold level at hl
  have hF : ∀ x ∈ p, x ∈ F := by
    intro x hx
    simp only [hFdef, mem_product, mem_range]
    refine ⟨?_, (hmem x hx).2⟩
    have : x.1 ≤ (p.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
    omega
  refine ⟨p.pmap Subtype.mk hF, ?_, ?_⟩
  · have h1 : (p.map Prod.fst).length ≤ (p.map Prod.fst).sum := by
      refine List.length_le_sum_of_one_le _ fun n hn => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
      exact (hmem x hx).1
    change (p.pmap Subtype.mk hF).length ≤ i
    simpa [hl] using h1
  · simp [List.map_pmap]

noncomputable def tw {E : Type} [Field E] (S : Finset E) (h0 : (0 : E) ∉ S) : Tower E where
  Sg := fun _ _ => S
  X := fun i => (finite_pts S i).toFinset
  isTower := by
    intro i p
    simp
  zero_not_mem := fun _ _ => h0

theorem form_nonneg {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (hk : PSDOn Y k) (V : α → H) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix Y Y ℂ, Matrix.gram ℂ (fun p : Y => V p.1) = star B * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.posSemidef_gram ℂ (fun p : Y => V p.1)).nonneg
  have hG : ∀ p q : Y, ⟪V p.1, V q.1⟫ = ∑ j, conj (B j p) * B j q := by
    intro p q
    have := congrFun (congrFun hB p) q
    simpa [Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using this
  have e1 : ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
      = ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫ := by
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have e2 : ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫
      = ∑ j : Y, star (fun p : Y => conj (B j p)) ⬝ᵥ
          (Matrix.of fun x y : Y => k x y).mulVec (fun p : Y => conj (B j p)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hG q p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => Matrix.PosSemidef.re_dotProduct_nonneg hk _

theorem norm_sq_comb {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ Y, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Y, ∑ q ∈ Y, (c p * conj (c q)) * ⟪V q, V p⟫ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ Y, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

theorem rows_le_form {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (V : α → H) (c : ℕ → α → ℂ) (R : Finset ℕ)
    (h : PSDOn Y (fun p q => k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) :
    ∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  have h0 := form_nonneg Y _ h V
  have e : ∑ p ∈ Y, ∑ q ∈ Y, (k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q)) * ⟪V q, V p⟫
      = ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
        - ((∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith

end Formalism.FourierDecayAlt.P.FinitePointSets

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

theorem limitStep : Formalism.FourierDecayAlt.TB.LimitStep := by
  intro E W _ D jn H _ _ _ Vt c _ _ hE hC hA B hB R
  classical
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hsum : ∀ ρ, Summable (fun p : Pt E => c ρ p • Vt p) := by
    intro ρ
    refine Summable.of_norm ?_
    simpa [norm_smul] using hA3 ρ
  have hlim : Tendsto (fun F : Finset (Pt E) => ∑ ρ ∈ R, ‖∑ p ∈ F, c ρ p • Vt p‖ ^ 2) atTop
      (𝓝 (∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun ρ _ => ?_
    exact ((hsum ρ).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F

  set F0 : Finset (Pt E) := F.filter (fun p => IsPt p (D.r + 1)) with hF0
  set S : Finset E := F0.biUnion fun p => (p.map Prod.snd).toFinset with hS
  have hS0 : (0 : E) ∉ S := by
    intro h
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hp, b, hb, hb0⟩ := h
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
    exact ((Finset.mem_filter.1 hp).2.2 k hk).2 hb0
  set T : Tower E := FinitePointSets.tw S hS0 with hT
  set Y : Finset (Pt E) := T.X (D.r + 1) with hY
  have hYpt : ∀ p ∈ Y, IsPt p (D.r + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (T.isTower (D.r + 1) p).1 hp
    refine ⟨h1, fun k hk => ⟨(h2 k hk).1, fun h => ?_⟩⟩
    have := (h2 k hk).2
    rw [h] at this
    exact T.zero_not_mem _ _ this
  have hF0Y : ∀ p ∈ F0, p ∈ Y := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine (T.isTower (D.r + 1) p).2 ⟨hp'.1, fun k hk => ⟨(hp'.2 k hk).1, ?_⟩⟩
    change (p[k]'hk).2 ∈ S
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, p[k]'hk, List.getElem_mem hk, rfl⟩
  refine ⟨F ∪ Y, Finset.subset_union_left, ?_⟩
  have e : ∀ ρ, ∑ p ∈ F ∪ Y, c ρ p • Vt p = ∑ p ∈ Y, c ρ p • Vt p := by
    intro ρ
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p hp hnp => ?_
    have hc : c ρ p = 0 := by
      by_contra h
      have hpF : p ∈ F := by
        rcases Finset.mem_union.1 hp with h' | h'
        · exact h'
        · exact absurd h' hnp
      exact hnp (hF0Y p (Finset.mem_filter.2 ⟨hpF, hA1 ρ p h⟩))
    rw [hc, zero_smul]
  simp_rw [e]
  refine (FinitePointSets.rows_le_form Y (D.Kr (D.r + 1)) Vt c R (hA2 Y hYpt R)).trans ?_

  have key : ∀ δ : ℝ, 0 < δ →
      (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re ≤ B * (jn + δ) := by
    intro δ hδ
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ D.Wb D.Ntop,
        (D.gram ε 0 w [] []).re / D.wt w ≤ jn + δ :=
      (Filter.eventually_all_finset _).2 fun w hw =>
        (hE w hw).eventually_le_const (by linarith)
    obtain ⟨ε, h1ε, h2ε, hε⟩ := (h1.and ((hC Y hYpt).and self_mem_nhdsWithin)).exists
    have h3 := hB T ε hε (jn + δ) h1ε
    have e2 : D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1))
        = (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re := by
      unfold Data.Sf
      congr 1
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
      by_cases hK : D.Kr (D.r + 1) p q = 0
      · rw [hK, zero_mul, zero_mul]
      · rw [h2ε p hp q hq hK]
    rwa [e2] at h3
  have ht : Tendsto (fun δ : ℝ => B * (jn + δ)) (𝓝[>] 0) (𝓝 (B * (jn + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [add_zero] at ht
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with δ hδ using key δ hδ)

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
section
namespace Formalism.FourierDecayAlt.P.W

open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W

section Words

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

theorem first_embedding_mul (M N : Matrix (Fin 2) (Fin 2) B) : E1 (M * N) = E1 M * E1 N :=
  blockDiagonal_mul (fun _ : Fin 2 => M) (fun _ => N)

private theorem E2_eq_reindex (M : Matrix (Fin 2) (Fin 2) B) :
    E2 M = reindexRingEquiv B (Equiv.prodComm (Fin 2) (Fin 2)) (E1 M) := rfl

theorem entries_mem_mul (M N : Matrix (Fin 2) (Fin 2) B) : E2 (M * N) = E2 M * E2 N := by
  simp only [E2_eq_reindex, first_embedding_mul, map_mul]

theorem first_embedding_one : E1 (1 : Matrix (Fin 2) (Fin 2) B) = 1 :=
  blockDiagonal_one

theorem entries_mem_one : E2 (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
  rw [E2_eq_reindex, first_embedding_one, map_one]

theorem first_second_embedding_commute (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : E1 A * E2 C = E2 C * E1 A := by
  unfold E1 E2
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, mul_ite, h]

theorem transpose_mul_of_comm (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : (A * C)ᵀ = Cᵀ * Aᵀ := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply, h]

theorem isDet_iff (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) :
    IsDet M q ↔ ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = q Y • Formalism.YangianSpanCharacter.T.J B ∧
      M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J B := by
  unfold Formalism.FourierDecayAlt.W.IsDet
  simp only [algebraMap_smul]

private theorem rtt_relation_mul_of_rtt_of_commute {A : Type*} [Ring A] (P a b c d : A) (hM : P * a * c = c * a * P)
    (hN : P * b * d = d * b * P) (c1 : b * c = c * b) (c2 : a * d = d * a) :
    P * (a * b) * (c * d) = c * d * (a * b) * P := by
  calc P * (a * b) * (c * d) = P * a * (b * c) * d := by simp only [mul_assoc]
    _ = P * a * (c * b) * d := by rw [c1]
    _ = (P * a * c) * b * d := by simp only [mul_assoc]
    _ = (c * a * P) * b * d := by rw [hM]
    _ = c * a * (P * b * d) := by simp only [mul_assoc]
    _ = c * a * (d * b * P) := by rw [hN]
    _ = c * (a * d) * b * P := by simp only [mul_assoc]
    _ = c * (d * a) * b * P := by rw [c2]
    _ = c * d * (a * b) * P := by simp only [mul_assoc]

theorem isRTT_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (hM : IsRTT M) (hN : IsRTT N)
    (hc : EntriesCommute M N) : IsRTT (fun Y => M Y * N Y) := by
  unfold Formalism.FourierDecayAlt.W.IsRTT at *
  intro Y Y'
  simp only [first_embedding_mul, entries_mem_mul]
  exact rtt_relation_mul_of_rtt_of_commute _ _ _ _ _ (hM Y Y') (hN Y Y')
    (first_second_embedding_commute _ _ (fun i j k l => (hc Y Y' k l i j).symm)) (first_second_embedding_commute _ _ (fun i j k l => hc Y' Y i j k l))

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_left {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h1 : a' * Jm * a = s • Jm) (h3 : b' * Jm * b = t • Jm) : b' * a' * Jm * (a * b) = (s * t) • Jm := by
  calc b' * a' * Jm * (a * b) = b' * (a' * Jm * a) * b := by simp only [mul_assoc]
    _ = b' * (s • Jm) * b := by rw [h1]
    _ = s • (b' * Jm * b) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = s • (t • Jm) := by rw [h3]
    _ = (s * t) • Jm := by rw [smul_smul]

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_right {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h2 : a * Jm * a' = s • Jm) (h4 : b * Jm * b' = t • Jm) : a * b * Jm * (b' * a') = (s * t) • Jm := by
  calc a * b * Jm * (b' * a') = a * (b * Jm * b') * a' := by simp only [mul_assoc]
    _ = a * (t • Jm) * a' := by rw [h4]
    _ = t • (a * Jm * a') := by rw [mul_smul_comm, smul_mul_assoc]
    _ = t • (s • Jm) := by rw [h2]
    _ = (s * t) • Jm := by rw [smul_smul, mul_comm]

theorem isDet_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (q qN : R → R) (hM : IsDet M q)
    (hN : IsDet N qN) (hc : EntriesCommute M N) :
    IsDet (fun Y => M Y * N Y) (fun Y => q Y * qN Y) := by
  rw [isDet_iff] at hM hN ⊢
  intro Y
  obtain ⟨h1, h2⟩ := hM Y
  obtain ⟨h3, h4⟩ := hN Y
  have ht := transpose_mul_of_comm (M (Y + 1)) (N (Y + 1)) (fun i j k l => hc (Y + 1) (Y + 1) i j k l)
  try beta_reduce
  refine ⟨?_, ?_⟩
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_left _ _ _ _ _ _ _ h1 h3
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_right _ _ _ _ _ _ _ h2 h4

theorem entriesCommute_prod (M : R → Matrix (Fin 2) (Fin 2) B)
    (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ y ∈ L, EntriesCommute M y.1) :
    EntriesCommute M (fun Y => (L.map (fun x => x.1 Y)).prod) := by
  unfold Formalism.FourierDecayAlt.W.EntriesCommute at *
  intro Y Y' i j k l
  induction L generalizing k l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs <;> simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * y.1 Y' k l = y.1 Y' k l * M Y i j :=
      fun y hy => h y (by simp [hy])
    exact (Commute.sum_right _ _ _ (fun m _ => Commute.mul_right (hx Y Y' i j k m) (ih ht m l))).eq


set_option maxHeartbeats 800000 in
theorem wordFusion_list (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ x ∈ L, IsRTT x.1 ∧ IsDet x.1 x.2)
    (hp : L.Pairwise (fun x y => EntriesCommute x.1 y.1)) :
    IsRTT (fun Y => (L.map (fun x => x.1 Y)).prod) ∧
      IsDet (fun Y => (L.map (fun x => x.1 Y)).prod) (fun Y => (L.map (fun x => x.2 Y)).prod) := by
  induction L with
  | nil =>
    refine ⟨?_, ?_⟩
    · unfold Formalism.FourierDecayAlt.W.IsRTT
      intro Y Y'
      simp [first_embedding_one, entries_mem_one]
    · rw [isDet_iff]
      intro Y
      simp
  | cons x t ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, IsRTT y.1 ∧ IsDet y.1 y.2 := fun y hy => h y (by simp [hy])
    rw [List.pairwise_cons] at hp
    obtain ⟨ih1, ih2⟩ := ih ht hp.2
    have hc := entriesCommute_prod x.1 t hp.1
    have e1 := isRTT_mul x.1 _ hx.1 ih1 hc
    have e2 := isDet_mul x.1 _ x.2 _ hx.2 ih2 hc
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · first
      | exact e1
      | simpa using e1
    · first
      | exact e2
      | simpa using e2

end Words

section Norm

end Norm

end Formalism.FourierDecayAlt.P.W

namespace Formalism.FourierDecayAlt.P

open NumberField

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LagrangeExtraction
section
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem extractK : ExtractK := by
  intro V _ _ K
  induction K with
  | zero =>
    intro d s W grid _ _ y₀
    simp
    congr 1
    exact Subsingleton.elim _ _
  | succ K ih =>
    intro d s W grid hP hg y₀
    set c := y₀ (Fin.last K) with hc
    have hP' : PolyStep K d (fun a => s a.castSucc)
        (fun m (y' : Fin K → ℝ) => W m (Fin.snoc (α := fun _ => ℝ) y' c)) := by
      intro a y'
      obtain ⟨cc, h1, h2⟩ := hP a.castSucc (Fin.snoc (α := fun _ => ℝ) y' c)
      refine ⟨cc, by simpa using h1, fun t => ?_⟩
      have := h2 t
      rw [← Fin.snoc_update] at this
      simpa using this
    have ih' := ih d _ _ (fun a => grid a.castSucc) hP' (fun a => hg _) (Fin.init y₀)
    simp only [hc, Fin.snoc_init_self] at ih'
    have hl : ∀ y' : Fin K → ℝ, s (Fin.last K) • W K (Fin.snoc (α := fun _ => ℝ) y' c) =
        ∑ i, ((lagCo (grid (Fin.last K)) i : ℝ) : ℂ) •
          W (K + 1) (Fin.snoc (α := fun _ => ℝ) y' (grid (Fin.last K) i)) := by
      intro y'
      obtain ⟨cc, h1, h2⟩ := hP (Fin.last K) (Fin.snoc (α := fun _ => ℝ) y' c)
      rw [Fin.val_last] at h1 h2
      rw [← h1, ChebyshevExtremalPolynomials.lead_complex (grid (Fin.last K)) (hg _) cc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h2, Fin.update_snoc_last]
    rw [Fin.prod_univ_castSucc, mul_comm, mul_smul, ih', Finset.smul_sum]
    rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [smul_comm, ← hc, hl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun a => grid a (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1)) (i, j') a)) =
        Fin.snoc (α := fun _ => ℝ) (fun a : Fin K => grid a.castSucc (j' a)) (grid (Fin.last K) i) := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [Fin.snocEquiv]
    rw [e, smul_smul, Fin.prod_univ_castSucc]
    congr 1
    simp [Fin.snocEquiv]

end Formalism.FourierDecayAlt.P.LagrangeExtraction

namespace Formalism.FourierDecayAlt.P

theorem extract_K_bound : Formalism.FourierDecayAlt.F7.ExtractK := LagrangeExtraction.extractK

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ReductionSurjective
section
namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

variable {c : ι → ℕ} {x y : Matrix ι ι A}


end Generic

section Prod

variable {G : Type} [Group G]

end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}




end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

variable {o} {r k : ℕ}

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2

end Formalism.FourierDecayAlt.P
end

