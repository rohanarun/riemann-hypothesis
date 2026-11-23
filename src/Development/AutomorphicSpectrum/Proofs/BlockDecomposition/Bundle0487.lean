module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0472
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalForm
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

theorem exists_radical_basis {K : Type*} [Field K] {r : ℕ} (B : Matrix (Fin r) (Fin r) K)
    (hd : B.det = 0) :
    ∃ (t k : ℕ) (e : Module.Basis (Fin t ⊕ Fin k) K (Fin r → K)), 0 < k ∧
      (∀ j, B *ᵥ e (Sum.inr j) = 0) ∧
      (∀ w : Fin t → K, B *ᵥ (∑ j, w j • e (Sum.inl j)) = 0 → w = 0) := by
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin r → K), N = LinearMap.ker B.mulVecLin := ⟨_, rfl⟩
  have hmemN : ∀ v, v ∈ N ↔ B *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl N
  obtain ⟨bN⟩ : Nonempty (Module.Basis (Fin (Module.finrank K N)) K N) := ⟨Module.finBasis K N⟩
  obtain ⟨bC⟩ : Nonempty (Module.Basis (Fin (Module.finrank K C)) K C) := ⟨Module.finBasis K C⟩
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (Fin (Module.finrank K C) ⊕ Fin (Module.finrank K N)) K (Fin r → K),
      e = (bC.prod bN).map (Submodule.prodEquivOfIsCompl C N hC.symm) := ⟨_, rfl⟩
  have he_inl : ∀ j, e (Sum.inl j) = (bC j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  have he_inr : ∀ j, e (Sum.inr j) = (bN j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  refine ⟨Module.finrank K C, Module.finrank K N, e, ?_, ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v, (hmemN v).mpr hv⟩, fun h => hv0 ?_⟩
    simpa using congrArg Subtype.val h
  · intro j
    rw [he_inr]
    exact (hmemN _).mp (bN j).2
  · intro w hw
    simp only [he_inl] at hw
    have hc : ((∑ j, w j • bC j : C) : Fin r → K) = ∑ j, w j • (bC j : Fin r → K) := by
      simp
    have hNmem : ((∑ j, w j • bC j : C) : Fin r → K) ∈ N := by
      rw [hmemN, hc]
      exact hw
    have h0 : ((∑ j, w j • bC j : C) : Fin r → K) = 0 :=
      Submodule.disjoint_def.mp hC.disjoint _ hNmem (Submodule.coe_mem _)
    funext j
    exact Fintype.linearIndependent_iff.mp bC.linearIndependent w (Submodule.coe_eq_zero.mp h0) j

theorem exists_blockNF {K : Type*} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {r : ℕ}
    (B : Matrix (Fin r) (Fin r) K) (hB : (B.map s)ᵀ = B) (hd : B.det = 0) :
    ∃ (P : Matrix (Fin r) (Fin r) K) (t : ℕ) (h : t < r), P.det ≠ 0 ∧
      (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0) ∧
      (((P.map s)ᵀ * B * P).submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0 := by
  obtain ⟨t, k, e, hk, hker, hinj⟩ := exists_radical_basis B hd
  have hcard : t + k = r := by
    have h1 := Module.finrank_eq_card_basis e
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm
  subst hcard
  have ht : t < t + k := Nat.lt_add_of_pos_right hk
  have hsplit : ∀ c : Fin t ⊕ Fin k, (∃ i', c = Sum.inl i') ∨ ∃ i', c = Sum.inr i' := by
    rintro (i' | i')
    · exact Or.inl ⟨i', rfl⟩
    · exact Or.inr ⟨i', rfl⟩
  have hinr : ∀ i : Fin (t + k), t ≤ i.1 → ∃ i', finSumFinEquiv.symm i = Sum.inr i' := by
    intro i hi
    rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
    · exfalso
      have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
      rw [hc, finSumFinEquiv_apply_left] at h1
      have h2 : i.1 = i'.1 := (congrArg Fin.val h1).symm
      have h3 := i'.isLt
      omega
    · exact ⟨i', hc⟩
  have hcast : ∀ j : Fin t, finSumFinEquiv.symm (Fin.castLE ht.le j) = Sum.inl j := by
    intro j
    have h1 : Fin.castLE ht.le j = Fin.castAdd k j := Fin.ext rfl
    rw [h1, finSumFinEquiv_symm_apply_castAdd]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (t + k)) (Fin (t + k)) K,
      ∀ a b, P a b = e (finSumFinEquiv.symm b) a :=
    ⟨Matrix.of fun a b => e (finSumFinEquiv.symm b) a, fun _ _ => rfl⟩
  have hBab : ∀ a b, s (B b a) = B a b := fun a b => by
    simpa using congrFun (congrFun hB a) b
  have hentry : ∀ i j, ((P.map s)ᵀ * B * P) i j =
      (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ e (finSumFinEquiv.symm j)) := by
    intro i j
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Matrix.map_apply, hP]
  have hrow : ∀ i' : Fin k, Matrix.vecMul (fun a => s (e (Sum.inr i') a)) B = 0 := by
    intro i'
    ext b
    have h0 : (B *ᵥ e (Sum.inr i')) b = 0 := by rw [hker i', Pi.zero_apply]
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    calc ∑ a, s (e (Sum.inr i') a) * B a b = ∑ a, s (B b a * e (Sum.inr i') a) :=
          Finset.sum_congr rfl fun a _ => by rw [map_mul, hBab, mul_comm]
      _ = s (∑ a, B b a * e (Sum.inr i') a) := (map_sum s _ _).symm
      _ = s ((B *ᵥ e (Sum.inr i')) b) := rfl
      _ = 0 := by rw [h0, map_zero]
  have hzero : ∀ i j : Fin (t + k), (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0 := by
    intro i j hij
    rw [hentry]
    rcases hij with hi | hj
    · obtain ⟨i', hi'⟩ := hinr i hi
      rw [hi', Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]
    · obtain ⟨j', hj'⟩ := hinr j hj
      rw [hj', hker j', dotProduct_zero]
  have hli : LinearIndependent K (fun b => e (finSumFinEquiv.symm b)) :=
    e.linearIndependent.comp _ finSumFinEquiv.symm.injective
  have hmv : ∀ v : Fin (t + k) → K, P *ᵥ v = ∑ b, v b • e (finSumFinEquiv.symm b) := by
    intro v
    ext a
    simp [Matrix.mulVec, dotProduct, hP, Finset.sum_apply, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    funext b
    exact Fintype.linearIndependent_iff.mp hli v (by rw [← hmv v]; exact hv) b
  have hPs : ((P.map s)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero s).mpr hPdet
  have hTy : ∀ i (y : Fin (t + k) → K),
      ((P.map s)ᵀ *ᵥ y) i = (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ y := by
    intro i y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hP]
  refine ⟨P, t, ht, hPdet, hzero, ?_⟩
  intro hB0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB0
  apply hw0
  apply hinj w
  obtain ⟨u, hu⟩ : ∃ u : Fin (t + k) → K, u = ∑ j, w j • e (Sum.inl j) := ⟨_, rfl⟩
  rw [← hu]
  have hexp : ∀ i, (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ u) =
      ∑ j, ((P.map s)ᵀ * B * P) i (Fin.castLE ht.le j) * w j := by
    intro i
    rw [hu, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hentry, hcast, mul_comm]
  by_contra hBu
  apply hPs
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨B *ᵥ u, hBu, ?_⟩
  funext i
  rw [hTy, Pi.zero_apply]
  rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
  · have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
    rw [hc, finSumFinEquiv_apply_left] at h1
    have hi : i = Fin.castLE ht.le i' := h1.symm.trans (Fin.ext rfl)
    rw [hexp, hi]
    have h2 := congrFun hw i'
    first
    | exact h2
    | (simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h2; exact h2)
  · rw [hc, Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem exists_congrH_isBlockNF (D : D7) (r : ℕ) (β : HermE D r) (hd : β.1.det = 0) :
    ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r),
      a.det ≠ 0 ∧ IsBlockNF t γ ∧ β = congrH a γ := by
  obtain ⟨P, t, ht, hP, hzero, hblock⟩ := NF.exists_blockNF (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun x => star_star x) β.1 β.2 hd
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, t, congrH P β, ?_, ⟨ht, hzero, hblock⟩, ?_⟩
  · intro h0
    have h1 := congrArg Matrix.det (Matrix.nonsing_inv_mul P hu)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  · apply Subtype.ext
    change β.1 = ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
      ((P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ * β.1 * P) * P⁻¹
    have h1 : ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
        (P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv P hu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStable
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanRangeComplementTransform
section
noncomputable section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC

namespace GlobalTheory.CompanionTheory.BruhatCell

variable {K : Type} [Field K]

theorem span_range_mul_le {n : ℕ} (q M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (q * M)) ≤ Submodule.span K (Set.range M) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h : (q * M) i = ∑ k, q i k • M k := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem span_range_mul_of_isUnit {n : ℕ} {p : Matrix (Fin n) (Fin n) K} (hp : IsUnit p.det)
    (M : Matrix (Fin n) (Fin n) K) :
    Submodule.span K (Set.range (p * M)) = Submodule.span K (Set.range M) := by
  refine le_antisymm (span_range_mul_le p M) ?_
  have h := span_range_mul_le p⁻¹ (p * M)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul] at h

theorem span_range_eId_mul {n r : ℕ} (hr : r ≤ n) {c : Matrix (Fin r) (Fin n) K}
    {a : Matrix (Fin n) (Fin n) K} (h : IsCompl c a) :
    Submodule.span K (Set.range (eId K n r * a)) = Submodule.span K (Set.range c) := by
  have row : ∀ i : Fin n, (eId K n r * a) i = if (i : ℕ) < r then a i else 0 := by
    intro i
    funext j
    by_cases hi : (i : ℕ) < r <;> simp [eId, Matrix.diagonal_mul, hi]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (eId K n r * a) i ∈ _
    rw [row i]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, h.2 i hi]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [if_neg hi]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j, j.2.trans_le hr⟩, ?_⟩
    change (eId K n r * a) ⟨j, j.2.trans_le hr⟩ = c j
    rw [row, if_pos j.2, h.2 ⟨j, j.2.trans_le hr⟩ j.2]

theorem span_range_lowerLeft : ∀ {K : Type} [Field K] {n r : ℕ}, r ≤ n →
    ∀ (c : Matrix (Fin r) (Fin n) K) (a p : Matrix (Fin n) (Fin n) K), IsCompl c a → IsUnit p.det →
      Submodule.span K (Set.range (p * -(eId K n r * a))) = Submodule.span K (Set.range c) := by
  intro K _ n r hr c a p h hp
  have hneg : p * -(eId K n r * a) = (-p) * (eId K n r * a) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  have hdet : IsUnit (-p).det := by
    rw [Matrix.det_neg]
    exact ((IsUnit.neg isUnit_one).pow _).mul hp
  rw [hneg, span_range_mul_of_isUnit hdet, span_range_eId_mul hr h]

end GlobalTheory.CompanionTheory.BruhatCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTest
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

theorem isTest_dTest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantLeviElementStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_invariant_levi_element : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω,
  PositivityTheory.GramSchwartzFunctions.HidaSetting D n V ψ χ θ μ ω →
  ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) →
  ∀ Φ : schwartzA θ V.rank n,
    ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g a hg Φ
  obtain ⟨-, -, -, ⟨-, hχ⟩, -, -, -, hW⟩ := hS
  let a' : GL (Fin n) (AE D) := Matrix.GeneralLinearGroup.map (incA D) a
  have hg' : mat g = blk4 (a' : Matrix (Fin n) (Fin n) (AE D)) 0 0
      (adj ((a'⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) := hg
  have hdet : Matrix.GeneralLinearGroup.det a' =
      Units.map (incA D : D.host.E →* AE D) (Matrix.GeneralLinearGroup.det a) :=
    Units.ext (by exact (RingHom.map_det (incA D) a.1).symm)
  have hχ1 : χ (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact hχ _
  have habs : absA D (Matrix.GeneralLinearGroup.det a') = 1 := by
    rw [hdet]
    exact absE_inclR _
  have hc : ∀ x, (ω g Φ).1 x = Φ.1 (x * (a' : Matrix (Fin n) (Fin n) (AE D))) := by
    intro x
    rw [hW.levi g a' hg' Φ x, hχ1, habs]
    simp [npow]
  have hterm : ∀ ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
      (ω g Φ).1 (ξ.map (incA D)) = Φ.1 ((ξ * (a : Matrix (Fin n) (Fin n) D.host.E)).map (incA D)) := by
    intro ξ
    rw [hc, Matrix.map_mul]
    rfl
  let e : Matrix (Fin V.rank) (Fin n) D.host.E ≃ Matrix (Fin V.rank) (Fin n) D.host.E :=
    { toFun := fun ξ => ξ * (a : Matrix (Fin n) (Fin n) D.host.E)
      invFun := fun ξ => ξ * ((a⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)
      left_inv := fun ξ => by simp [Matrix.mul_assoc]
      right_inv := fun ξ => by simp [Matrix.mul_assoc] }
  rw [tsum_congr hterm]
  exact e.tsum_eq (fun ξ => Φ.1 (ξ.map (incA D)))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Gen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def trM {R : Type} {M n : ℕ} (X : Fin n → Fin M → R) : Matrix (Fin M) (Fin n) R :=
  Matrix.of fun i a => X a i

def framesE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    Set (Fin n → Fin M → E) :=
  {X | LinearIndependent E X ∧ gramE σ J X = T}

def IsBlockM {n : ℕ} (t : ℕ) (T : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ h : t < n, (∀ i j : Fin n, (t ≤ i.1 ∨ t ≤ j.1) → T i j = 0) ∧
    (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

def IsGramFibFree (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ m

end Gen

section Glob

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def SWFree (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : Prop :=
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf →
      (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) →
      IsEulerProd b (thetaMeas σ J μ 𝓕 (framesE σ J T)) 1 (minf (hermOf (Ainf F) σ T hT))
        (fun v => m v (hermOf (Fv F v) σ T hT))

end Glob

section D

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermE_symm {D : D7} {r : ℕ} (β : PositivityTheory.GramSchwartzFunctions.HermE D r) (a b : Fin r) :
    D.sp.cm.sig (β.1 b a) = β.1 a b := by
  have h := congrFun (congrFun β.2 a) b
  simpa [Matrix.map_apply, Matrix.transpose_apply] using h

theorem trM_mem_framesE_iff {D : D7} (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E)
    (T : Matrix (Fin r) (Fin r) D.host.E) :
    X ∈ framesE D.sp.cm.sig V.gram T ↔ (trM X).rank = r ∧ PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) = T := by
  have hg : HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) := by
    refine Matrix.ext fun a b => ?_
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, PositivityTheory.GramSchwartzFunctions.BC.gramQ, trM,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_assoc]; rfl
  have hr : LinearIndependent D.host.E X ↔ (trM X).rank = r := by
    have h1 : (trM X).rank = (Matrix.of X).rank := by
      have : trM X = Matrix.transpose (Matrix.of X) := rfl
      rw [this, Matrix.rank_transpose]
    rw [h1, Matrix.rank_eq_finrank_span_row]
    have := linearIndependent_iff_card_eq_finrank_span (R := D.host.E) (b := X)
    refine this.trans ?_
    rw [Fintype.card_fin, eq_comm]
    exact Iff.rfl
  simp only [framesE, Set.mem_ofPred_eq, hr, hg]

end D

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

