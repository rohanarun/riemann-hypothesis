module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo hiding IsMultiHomog

noncomputable section

section Homog

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_C (c : ℤ) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C c : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isMultiHomog_prod {σ : Type} (s : Finset σ) (f : σ → MRing ι) (d : σ → κ → ℕ)
    (h : ∀ a ∈ s, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f a) (d a)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ a ∈ s, f a) (∑ a ∈ s, d a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ProjLine.isMultiHomog_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ProjLine.mhMul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem isMultiHomog_chartMonomial (c : ∀ k, ι k) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have h := isMultiHomog_prod (Finset.univ : Finset κ) (fun k => (X ⟨k, c k⟩ : MRing ι))
    (fun k => fun k1 => if k1 = k then 1 else 0) (fun k _ => ProjLine.isMultiHomog_X ⟨k, c k⟩)
  have hs : (∑ k : κ, (fun k1 : κ => if k1 = k then 1 else 0 : κ → ℕ)) = fun _ => 1 := by
    funext k1
    simp [Finset.sum_apply]
  rwa [hs] at h

end Homog

section Values

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem mem_mCoordIdeal_of_aeval {f : MRing ι} {d : κ → ℕ} (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

theorem IsValueAt.unique {a : Ω} {v v' : ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (h : IsValueAt y a z v) (h' : IsValueAt y a z v') : v = v' := by
  obtain ⟨d, g, h1, hg, hh, hy, hyg, hz1, hzg⟩ := h
  obtain ⟨d', g', h1', hg', hh', hy', hyg', hz1', hzg'⟩ := h'
  have hm : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g * h1' - g' * h1) (d + d') := by
    rw [sub_eq_add_neg]
    refine ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg ?_)
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  have h0 : aeval y (g * h1' - g' * h1) = 0 := by
    rw [map_sub, map_mul, map_mul, hyg, hyg']
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval hm h0)
  rw [map_sub, map_mul, map_mul, eval_sub, eval_mul, eval_mul, hzg, hzg', sub_eq_zero] at hz0
  have hne : eval z (map (Int.castRingHom ℂ) h1) * eval z (map (Int.castRingHom ℂ) h1') ≠ 0 :=
    mul_ne_zero hz1 hz1'
  apply mul_right_cancel₀ hne
  linear_combination hz0

theorem valAt_eq {a : Ω} {v : ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (h : IsValueAt y a z v) :
    valAt y a z = v := by
  have hr : RegularAt y a z := ⟨v, h⟩
  rw [valAt, dite_eq_left hr]
  exact IsValueAt.unique hz hr.choose_spec h

theorem RegularAt.isValueAt {a : Ω} (hz : z ∈ mcPts (mCoordIdeal y)) (h : RegularAt y a z) :
    IsValueAt y a z (valAt y a z) := by
  obtain ⟨v, hv⟩ := h
  rwa [valAt_eq hz hv]

theorem IsValueAt.mul {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a * b) z (v * w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  refine ⟨d + d', g * g', h * h', ProjLine.mhMul hg hg', ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_mul, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.add {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a + b) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  have hd : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g' * h) (d + d') := by
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  refine ⟨d + d', g * h' + g' * h, h * h', ProjLine.mhAdd (ProjLine.mhMul hg hh') hd,
    ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_add (f := _), map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add (f := _), map_mul, eval_add, eval_mul]
    rw [hzg, hzg']
    ring

theorem isValueAt_intCast (n : ℤ) : IsValueAt y (n : Ω) z (n : ℂ) := by
  refine ⟨0, C n, 1, isMultiHomog_C n, ProjLine.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_one : IsValueAt y (1 : Ω) z 1 := by
  simpa using isValueAt_intCast (y := y) (z := z) 1

theorem isValueAt_zero : IsValueAt y (0 : Ω) z 0 := by
  simpa using isValueAt_intCast (y := y) (z := z) 0

theorem IsValueAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} {v : σ → ℂ}
    (h : ∀ i ∈ s, IsValueAt y (a i) z (v i)) : IsValueAt y (∑ i ∈ s, a i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem RegularAt.mul {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a * b) z :=
  ⟨_, ha.choose_spec.mul hb.choose_spec⟩

theorem RegularAt.add {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a + b) z :=
  ⟨_, ha.choose_spec.add hb.choose_spec⟩

theorem RegularAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} (h : ∀ i ∈ s, RegularAt y (a i) z) :
    RegularAt y (∑ i ∈ s, a i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using isValueAt_zero⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))


omit [Fintype κ] [∀ k, Fintype (ι k)] in
theorem eval_conj (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => starRingEnd ℂ (z p)) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem IsValueAt.conj {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_conj]
    exact (map_ne_zero _).2 hz
  · rw [eval_conj, eval_conj, hzg, map_mul]

theorem IsValueAt.smul {a : Ω} {v : ℂ} (s : κ → ℂ) (hs : ∀ k, s k ≠ 0) (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => s p.1 * z p) v := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)) hz
  · rw [eval_smul_homog h d hh, eval_smul_homog g d hg, hzg]
    ring

theorem regularAt_of_mem_chartRing (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ chartRing ℤ (NumbersDVR.segreVec y) c) :
    RegularAt y a z := by
  have hden : NumbersDVR.segreVec y c ≠ 0 := by
    intro h0
    have hm := mem_mCoordIdeal_of_aeval (y := y) (isMultiHomog_chartMonomial c)
      (by simpa [NumbersDVR.segreVec] using h0)
    have := hz.2 _ hm
    simp only [map_prod, map_X, eval_prod, eval_X] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    have hz0 : eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))) ≠ 0 := by
      simp only [map_prod, map_X, eval_prod, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    refine ⟨eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c' k⟩ : MRing ι))) /
      eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))), fun _ => 1,
      ∏ k, (X ⟨k, c' k⟩ : MRing ι), ∏ k, (X ⟨k, c k⟩ : MRing ι), isMultiHomog_chartMonomial c',
      isMultiHomog_chartMonomial c, ?_, ?_, hz0, ?_⟩
    · simpa [NumbersDVR.segreVec] using hden
    · simp only [map_prod, aeval_X]
      show NumbersDVR.segreVec y c' = NumbersDVR.segreVec y c' / NumbersDVR.segreVec y c *
        NumbersDVR.segreVec y c
      rw [div_mul_cancel₀ _ hden]
    · rw [div_mul_cancel₀ _ hz0]
  | algebraMap r =>
    exact ⟨r, by simpa using isValueAt_intCast (y := y) (z := z) r⟩
  | add a b _ _ ha hb => exact ha.add hb
  | mul a b _ _ ha hb => exact ha.mul hb

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PWedgeTransition
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open GroundTheory.Heights₂.Heights.LowerBoundFree Submodule Module

namespace WedgeTransition

theorem alternating_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[R] R) (v : Fin n → M) (A : Matrix (Fin n) (Fin n) R) :
    f (fun q => ∑ a, A a q • v a) = A.det * f v := by
  let T : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R v
  have h := congrArg (fun g => g (fun q a => A a q))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin n)) (f.compLinearMap T))
  have hT : ∀ x, T x = ∑ a, x a • v a := fun x => by
    simp [T, Basis.constr_apply_fintype]
  have hTe : (fun i => T (Pi.basisFun R (Fin n) i)) = v := funext fun i => by simp [T]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Pi.basisFun_det_apply,
    smul_eq_mul] at h
  have e1 : (fun i => T fun a => A a i) = fun q => ∑ a, A a q • v a := funext fun q => hT _
  rw [e1, hTe] at h
  rw [h, mul_comm]
  congr 1
  exact Matrix.det_transpose A

def splitEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hj))

theorem splitEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : splitEquiv hj (Sum.inl a) = Fin.castLE hj a :=
  Fin.ext (by simp [splitEquiv])

theorem splitEquiv_inr {j N : ℕ} (hj : j ≤ N) (a : Fin (N - j)) : splitEquiv hj (Sum.inr a) = tailIdx hj a :=
  Fin.ext (by simp [splitEquiv, tailIdx])

theorem sum_split {M : Type*} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (g : Fin N → M) :
    ∑ p, g p = ∑ a, g (Fin.castLE hj a) + ∑ a, g (tailIdx hj a) := by
  rw [← (splitEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp [splitEquiv_inl, splitEquiv_inr]

theorem det_split_of_zero {R : Type*} [CommRing R] {j N : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) R)
    (h0 : ∀ a a', G (tailIdx hj a) (Fin.castLE hj a') = 0) :
    G.det = (G.submatrix (Fin.castLE hj) (Fin.castLE hj)).det *
      (G.submatrix (tailIdx hj) (tailIdx hj)).det := by
  rw [← Matrix.det_submatrix_equiv_self (splitEquiv hj) G,
    ← Matrix.fromBlocks_toBlocks (G.submatrix (splitEquiv hj) (splitEquiv hj))]
  have h21 : (G.submatrix (splitEquiv hj) (splitEquiv hj)).toBlocks₂₁ = 0 := by
    ext a a'
    simp [Matrix.toBlocks₂₁, splitEquiv_inl, splitEquiv_inr, h0]
  rw [h21, Matrix.det_fromBlocks_zero₂₁]
  congr 2

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (F : Submodule Ω V) {N j : ℕ} (hj : j ≤ N)

theorem exists_form_quotWedge_eq_one {b' : Fin N → V} (hli : LinearIndependent Ω b')
    (hsp : span Ω (Set.range b') = ⊤) (hF : span Ω (Set.range (b' ∘ Fin.castLE hj)) = F) :
    ∃ ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω, ℓ (quotWedge F hj b') = 1 := by
  let B := Basis.mk hli hsp.ge
  have : Module.Finite Ω V := Module.Finite.of_basis B
  have hV : Module.finrank Ω V = N := by simpa using Module.finrank_eq_card_basis B
  have hFr : Module.finrank Ω F = j := by
    rw [← hF, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hj))]
    simp
  have hQ := Submodule.finrank_quotient_add_finrank F
  let w : Fin (N - j) → V ⧸ F := fun a => F.mkQ (b' (tailIdx hj a))
  have hspan : ⊤ ≤ span Ω (Set.range w) := by
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective F x
    have h1 : F.mkQ v ∈ span Ω (F.mkQ '' Set.range b') := by
      rw [← Submodule.map_span, hsp]
      exact ⟨v, trivial, rfl⟩
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < j
    · have hmem : b' i ∈ F := hF ▸ subset_span ⟨⟨i, hi⟩, rfl⟩
      have : F.mkQ (b' i) = 0 := by simpa using hmem
      rw [SetLike.mem_coe, this]
      exact zero_mem _
    · have : i = tailIdx hj ⟨i - j, by omega⟩ := Fin.ext (by simp [tailIdx]; omega)
      rw [this]
      exact subset_span ⟨_, rfl⟩
  have hli' : LinearIndependent Ω w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp; omega)
  let Q := Basis.mk hli' hspan
  refine ⟨exteriorPower.alternatingMapLinearEquiv Q.det, ?_⟩
  rw [quotWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have : (fun a => F.mkQ (b' (tailIdx hj a))) = ⇑Q := funext fun a => (Basis.mk_apply hli' hspan a).symm
  rw [this, Basis.det_self]

end WedgeTransition

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section General

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

structure AdaptedBasis {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) where

  e : ∀ τ, Fin D.N → E τ
  e_indep : ∀ τ, LinearIndependent Ω (e τ)
  e_span : ∀ τ, Submodule.span Ω (Set.range (e τ)) = ⊤
  e_head : ∀ τ, Submodule.span Ω (Set.range (e τ ∘ headIdx D.j_le_N)) = H.F τ

def ComponentData.flagDim0 (D : ComponentData II Ψ K ι Ω E) : ℕ :=
  Fintype.card Ψ * (D.j * (D.j - 1) / 2 + (D.N - D.j) * (D.N - D.j - 1) / 2)

namespace PlueckerData

variable {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)

def xV : (Σ k, ι k) → (Σ k, Pl.ιY k) := fun p => ⟨Sum.inl p.1, p.2⟩

theorem isBlockMap_xV : IsBlockMap (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) Pl.xV := by
  refine ⟨Sum.inl_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    cases h
    rfl
  · rintro ⟨k', i⟩ ⟨k, rfl⟩
    exact ⟨⟨k, i⟩, rfl⟩

def ofΩHom : Ω →+* Pl.ΩY :=
  (algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY).comp C

theorem ofΩHom_apply (x : Ω) : Pl.ofΩHom x = Pl.ofΩ x := rfl

theorem ofΩHom_injective : Function.Injective Pl.ofΩHom :=
  (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY).comp (C_injective _ _)

variable {H : HodgeData D} (B : AdaptedBasis H)

def gvar0 (τ : Ψ) (a b : Fin D.N) : Pl.ΩY :=
  if (a : ℕ) < D.j ∧ D.j ≤ (b : ℕ) then 0 else Pl.gvar τ a b

def pluecker0 (τ : Ψ) (i : Fin (D.N - 1)) (m : Fin (Pl.M τ i)) : Pl.ΩY :=
  ∑ c : Fin ((i : ℕ) + 1) → Fin D.N, (∏ a, Pl.gvar0 τ (headIdx (step_le i) a) (c a)) *
    Pl.ofΩ (Pl.gen τ i m (exteriorPower.ιMulti Ω _ (B.e τ ∘ c)))

def flagGenericPoint : (Σ k, Pl.ιY k) → Pl.ΩY
  | ⟨Sum.inl k, t⟩ => Pl.ofΩ (D.y ⟨k, t⟩)
  | ⟨Sum.inr q, m⟩ => Pl.pluecker0 B q.1 q.2 m

def flagPrime : Ideal (MRing Pl.ιY) := mCoordIdeal (Pl.flagGenericPoint B)

theorem mConeMap_flagGenericPoint_rename (f : MRing ι) :
    mConeMap (Pl.flagGenericPoint B) (rename Pl.xV f) =
      rename (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) (MvPolynomial.map Pl.ofΩHom (mConeMap D.y f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, xV, flagGenericPoint, ofΩHom_apply]

theorem imageZ_forget_flagPrime : imageZ Pl.xV (Pl.flagPrime B) = mCoordIdeal D.y := by
  have hinj : Function.Injective fun g : MvPolynomial K Ω =>
      rename (Sum.inl : K → K ⊕ (Ψ × Fin (D.N - 1))) (MvPolynomial.map Pl.ofΩHom g) :=
    (rename_injective _ Sum.inl_injective).comp (map_injective _ Pl.ofΩHom_injective)
  ext f
  show mConeMap (Pl.flagGenericPoint B) (rename Pl.xV f) = 0 ↔ mConeMap D.y f = 0
  rw [mConeMap_flagGenericPoint_rename]
  exact ⟨fun h => hinj (h.trans (by simp)), fun h => by simp [h]⟩

end PlueckerData

end General

def HodgeFlagArith.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H),
    IsArithVar (Pl.flagPrime B) (D.n + 1 + D.flagDim0)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVerticalTwistGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalTwistGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (a : K → ℤ)
    (s : Finset ℕ) (b : ℕ → K → ℤ) (f g : ℕ → MRing ι),
    IsArithVar P (d + 1) → (∀ p ∈ s, p.Prime ∧ IsVerticalDivisorAt P p (b p) (f p) (g p)) →
    genDeg P d (a + ∑ p ∈ s, b p) = genDeg P d a

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

