module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivExpEntry
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.VminusK

theorem flow_vanish {W : Type} [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ W) [FiniteDimensional ℂ S]
    (A : W →ₗ[ℂ] W) (hA : ∀ x ∈ S, A x ∈ S) (φ : ℝ → W →ₗ[ℂ] ℂ)
    (hφ : ∀ t x, HasDerivAt (fun s => φ s x) (φ t (A x)) t) (h0 : ∀ x ∈ S, φ 0 x = 0) :
    ∀ t, ∀ x ∈ S, φ t x = 0 := by
  let b := Module.finBasis ℂ S
  let M : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    Matrix.of fun i j => b.repr ⟨A (b i), hA _ (b i).2⟩ j
  let L : (Fin (Module.finrank ℂ S) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hexp : ∀ t (x : S), φ t x = ∑ j, b.repr x j * φ t (b j) := by
    intro t x
    have h := congrArg (φ t ∘ₗ S.subtype) (b.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  have key : (fun t i => φ t (b i)) = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ y => L y) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun t => ⟨?_, trivial⟩) (fun t => ⟨?_, trivial⟩) ?_
    · refine hasDerivAt_pi.2 fun i => ?_
      refine (hφ t (b i)).congr_deriv ?_
      rw [hexp t ⟨A (b i), hA _ (b i).2⟩]
      simp [L, M, Matrix.mulVec, dotProduct]
    · simpa using hasDerivAt_const t (0 : Fin (Module.finrank ℂ S) → ℂ)
    · funext i
      exact h0 _ (b i).2
  intro t x hx
  rw [hexp t ⟨x, hx⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := congrFun (congrFun key t) j
  simp only [Pi.zero_apply] at this
  rw [this, mul_zero]

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem deriv_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

theorem deriv_exp_entry' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) s := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) Y (s : ℂ)
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have h1 : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y) i j)
      ((Y * NormedSpace.exp ((s : ℂ) • Y)) i j) (s : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt (s : ℂ) h
  exact h1.comp_ofReal

end Linfty

theorem deriv_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using this

theorem deriv_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ V}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDer ε σ V E) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y)
    (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • Y)) ((∑ a, ∑ b, Y a b • E a b v : V) : H)) t := by
  have h1 := hD.2.2.1 Y hY v
  have h2 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) t := by
    have h3 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • Y)) (v : H))
      ((∑ a, ∑ b, Y a b • E a b v : V) : H) (t - t) := by rw [sub_self]; exact h1
    exact h3.comp_sub_const t t
  have h4 := ((σ (NormedSpace.exp ((t : ℂ) • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h2
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  have h5 := oneParam n Y t (s - t)
  rw [add_sub_cancel] at h5
  rw [h5, hσ.1.2 _ (expUJ n ε Y hY t) _ (expUJ n ε Y hY (s - t))]
  rfl

def matOf {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ℓ : V →ₗ[ℂ] ℂ) :
    Arr V n 1 →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun G := Matrix.of fun a b => ℓ (at1 G a b)
  map_add' G G' := by
    ext a b
    simp [at1]
  map_smul' c G := by
    ext a b
    simp [at1]

theorem matOf_act {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) (G : Arr V n 1) :
    matOf ℓ ((∑ c, ∑ d, Y c d • arrE E 1 c d) G) =
      Y * matOf ℓ G - matOf ℓ G * Y +
        Matrix.of fun a b => ℓ (∑ c, ∑ d, Y c d • E c d (at1 G a b)) := by
  have h : ∀ c d a b, matOf ℓ (arrE E 1 c d G) a b =
      (if a = c then matOf ℓ G d b else 0) - (if b = d then matOf ℓ G a c else 0) + ℓ (E c d (at1 G a b)) := by
    intro c d a b
    have := congrArg ℓ (arr_operator_one_apply E c d G a b)
    rw [map_add (f := _), map_sub, apply_ite ℓ, apply_ite ℓ, map_zero] at this
    exact this
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Matrix.sum_apply,
    Matrix.smul_apply, h, smul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, mul_ite, mul_zero]
  congr 2
  · rw [Finset.sum_comm]
    simp
  · simp [mul_comm]

theorem inK_entry {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {c d : Fin n}
    (h : ε c ≠ ε d) : Y c d = 0 := by
  have h1 := congrFun (congrFun hY.2 c) d
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  cases hc : ε c <;> cases hd : ε d <;> simp [hc, hd] at h h1
  · linear_combination h1 / 2
  · linear_combination -h1 / 2

theorem vminus_K : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (abelian₂ : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E abelian₂ u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E abelian₂ u, ∀ k ∈ Kset ε, ∀ c d : Fin n, ¬ d < c → ∑ a, ∑ b, k⁻¹ c a * k b d * ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ = 0 := by
  intro n ε H _ _ _ σ V E abelian₂ u hσ hD hΛ hfd G hG k hk c d hcd
  obtain ⟨hst, -, hfm, hvan⟩ := VminusComp.vminus_comp V n ε E abelian₂ u hD.1 hD.2.1 hΛ hfd
  have hks := Kset_star ε hk
  have hinv : k⁻¹ = star k := Matrix.inv_eq_left_inv hk.1.1
  obtain ⟨Y, hY, hexp, -⟩ := compact_exponential_surjective n ε _ hks
  have hexp' : NormedSpace.exp (-Y) = k := by
    rw [Matrix.exp_neg, hexp]
    exact Matrix.inv_eq_left_inv hk.1.2
  let ℓ : ℝ → V →ₗ[ℂ] ℂ := fun t =>
    (innerₛₗ ℂ (u : H)) ∘ₗ (σ (NormedSpace.exp ((t : ℂ) • Y))).toLinearMap ∘ₗ V.subtype
  have hℓ : ∀ t (v : V), ℓ t v = ⟪(u : H), σ (NormedSpace.exp ((t : ℂ) • Y)) v⟫_ℂ := fun _ _ => rfl
  let φ : ℝ → Arr V n 1 →ₗ[ℂ] ℂ := fun t =>
    Matrix.entryLinearMap ℂ ℂ c d ∘ₗ LinearMap.mulRight ℂ (NormedSpace.exp ((t : ℂ) • (-Y))) ∘ₗ
      LinearMap.mulLeft ℂ (NormedSpace.exp ((t : ℂ) • Y)) ∘ₗ matOf (ℓ t)
  have hφ : ∀ t G, φ t G = (NormedSpace.exp ((t : ℂ) • Y) * matOf (ℓ t) G *
      NormedSpace.exp ((t : ℂ) • (-Y))) c d := fun _ _ => rfl
  have main := flow_vanish (Vminus ε E abelian₂ u) (∑ c, ∑ d, Y c d • arrE E 1 c d) ?_ φ ?_ ?_ 1 G hG
  · rw [hφ, Complex.ofReal_one, one_smul, one_smul, hexp, hexp', ← hinv] at main
    rw [← main]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    have e1 : matOf (ℓ 1) G a b = ⟪σ k (u : H), (at1 G a b : V)⟫_ℂ := by
      show ℓ 1 (at1 G a b) = _
      rw [hℓ, Complex.ofReal_one, one_smul, hexp]
      have hkU : k ∈ UJset ε := (kFacts n ε).1 k hk
      have hsU : star k ∈ UJset ε := (kFacts n ε).1 _ hks
      have h1 : σ k (σ (star k) (at1 G a b : V)) = (at1 G a b : V) := by
        have := hσ.1.2 k hkU _ hsU
        rw [hk.1.2, hσ.1.1] at this
        exact (congrArg (fun T : H →L[ℂ] H => T (at1 G a b : V)) this).symm
      let I : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k hkU⟩
      have h2 := I.inner_map_map (u : H) (σ (star k) (at1 G a b : V))
      rw [← h2]
      show ⟪σ k (u : H), σ k (σ (star k) (at1 G a b : V))⟫_ℂ = _
      rw [h1]
    rw [e1]
    ring
  · intro x hx
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    by_cases h : ε a = ε b
    · exact Submodule.smul_mem _ _ (hst a b h x hx)
    · rw [inK_entry hY h, zero_smul]
      exact Submodule.zero_mem _
  · intro t x
    have hM : ∀ a b, HasDerivAt (fun s => matOf (ℓ s) x a b)
        ((Matrix.of fun a b => ℓ t (∑ c, ∑ d, Y c d • E c d (at1 x a b))) a b) t := by
      intro a b
      exact ((innerSL ℂ (u : H)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (deriv_orbit hσ hD hY.1 (at1 x a b) t)
    have h1 := deriv_mul_entry _ _ _ _ t
      (deriv_mul_entry _ _ _ _ t (deriv_exp_entry Y t) hM) (deriv_exp_entry' (-Y) t) c d
    simp only [hφ]
    refine h1.congr_deriv ?_
    rw [matOf_act]
    refine congrFun (congrFun ?_ c) d
    noncomm_ring
  · intro x hx
    rw [hφ]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]
    show ℓ 0 (at1 x c d) = 0
    rw [hℓ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1]
    exact hvan x hx c d hcd

end GlobalTheory.Jet.VminusK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.PhMajProof

theorem local_integrable (n : ℕ) (ε : Fin n → Bool) (h s : ℝ) (hs : 0 ≤ s)
    (hyp : rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) :
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  rcases hyp with h0 | hlt
  · have key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) =
        fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      funext g
      rw [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]
      simp [decE]
    rw [key]
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)
  · have hh : 0 ≤ h := by
      have : 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) :=
        mul_nonneg (by positivity) (add_nonneg hs (by positivity))
      linarith
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)

theorem phMaj : PhMaj := by
  intro B d h hds hloc
  have hd : ∀ v, 0 < d v := fun v => (hds v).2.2.2.1
  have hdp : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).le
  have hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) := by
    intro v
    have hon := (hds v).2.1.2.2.1.2.2 (B.w v)
    refine hon.comp_continuous ?_ ?_
    · unfold uMat
      exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    · intro g
      exact (g v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold ph
    exact continuous_const.mul (continuous_star.comp
      (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))
  · intro g
    unfold ph majPh
    rw [norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp
  · intro s hs hyp
    have key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf =>
        (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v)))) := by
      funext g
      unfold majPh dSum
      rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [key]
    unfold muInf
    have hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v,
        (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v)))))
        (Measure.pi fun v => muG (B.I.ε v)) :=
      Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)
    exact hprod.const_mul _

end GlobalTheory.Dec.PhMajProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualVectorsNormalFormMemSecondFlag
section
open Matrix

namespace GlobalTheory

theorem dual_vectors_in_second_flag : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := by
  intro K V _ _ _ _ H r j hj e e' s hdet he' hz hs he's hss
  set P : Matrix (Fin j) (Fin j) K := Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b)) with hPdef
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
  have hR : ∀ (x : V) (g : Fin j → K), H.B x (∑ c, g c • e' (Fin.castLE hj c)) = ∑ c, star (g c) * H.B x (e' (Fin.castLE hj c)) := by
    intro x g; simp [map_sum, map_smulₛₗ, starRingEnd_apply]
  have hL : ∀ (y : V) (g : Fin j → K), H.B (∑ c, g c • e' (Fin.castLE hj c)) y = ∑ c, g c * H.B (e' (Fin.castLE hj c)) y := by
    intro y g; simp [map_sum, LinearMap.sum_apply]
  let f : Fin r → V := fun b => if h : b.val < j then ∑ c : Fin j, star (P⁻¹ c ⟨b.val, h⟩) • e' (Fin.castLE hj c) else s b
  have hf : ∀ b : Fin j, f (Fin.castLE hj b) = ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := fun b => by
    simp [f]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp [f, Nat.not_lt.mpr ha]
  · intro a ha
    simp only [f, dif_pos ha]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj c, c.isLt, rfl⟩)
  · intro a b
    by_cases hb : b.val < j
    · simp only [f, dif_pos hb, hR, star_star]
      by_cases ha : a.val < j
      · calc ∑ c, P⁻¹ c ⟨b.val, hb⟩ * H.B (e a) (e' (Fin.castLE hj c))
            = ∑ c, P ⟨a.val, ha⟩ c * P⁻¹ c ⟨b.val, hb⟩ := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [mul_comm]; rfl
          _ = (P * P⁻¹) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by rw [Matrix.mul_apply]
          _ = if a = b then 1 else 0 := by rw [hPQ, Matrix.one_apply]; simp [Fin.ext_iff]
      · rw [Finset.sum_eq_zero]
        · have : a ≠ b := fun h => ha (h ▸ hb)
          simp [this]
        intro c _
        rw [hz a (Fin.castLE hj c) (Nat.not_lt.mp ha) (by simp), mul_zero]
    · simp only [f, dif_neg hb]; exact hs a b (Nat.not_lt.mp hb)
  · intro a b
    by_cases ha : a.val < j <;> by_cases hb : b.val < j
    · simp only [f, dif_pos ha, dif_pos hb, hL, hR, he', mul_zero, Finset.sum_const_zero]
    · simp only [f, dif_pos ha, dif_neg hb, hL]
      exact Finset.sum_eq_zero fun c _ => by rw [he's _ _ (by simp) (Nat.not_lt.mp hb), mul_zero]
    · simp only [f, dif_neg ha, dif_pos hb, hR]
      exact Finset.sum_eq_zero fun c _ => by rw [← H.herm, he's _ _ (by simp) (Nat.not_lt.mp ha), star_zero, mul_zero]
    · simp only [f, dif_neg ha, dif_neg hb]; exact hss a b (Nat.not_lt.mp ha) (Nat.not_lt.mp hb)
  · intro a ha
    have key : e' a = ∑ b : Fin j, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by
      calc e' a = ∑ c, star ((1 : Matrix (Fin j) (Fin j) K) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by
              simp [Matrix.one_apply, apply_ite star]
        _ = ∑ c, star ((P⁻¹ * P) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by rw [hQP]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := by
              simp_rw [Matrix.mul_apply, star_sum, Finset.sum_smul, Finset.smul_sum, smul_smul, star_mul]
              rw [Finset.sum_comm]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by simp_rw [hf]
    rw [key]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj b, b.isLt, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockAntidiagonalScaledPairingMatrix
section
open Matrix

namespace GlobalTheory.Amp.BlockFrame

theorem blockAnti_scaled_pairing : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  intro K _ j r hj w
  obtain ⟨τ, γ, t, ht⟩ := GlobalTheory.HL.BlockStab.exists_monomial (E := K) w.blocks
  rw [w.size] at ht

  have hγN : ∀ a, a < j → γ a < (Finset.range j).sup γ + 1 := fun a ha =>
    Nat.lt_succ_of_le (Finset.le_sup (f := γ) (Finset.mem_range.mpr ha))
  refine ⟨fun a => if (a : ℕ) < j then γ a else (Finset.range j).sup γ + 1, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    dsimp only
    split_ifs with h1 h2 h2
    · exact ((ht a h1).2.2.2 b h2).2.1 hab'
    · exact (hγN a h1).le
    · omega
    · exact le_rfl
  · intro a b hb
    have hb' : ¬ ((b : ℕ) < j) := by omega
    dsimp only
    rw [if_neg hb']
    by_cases ha : (a : ℕ) < j
    · rw [if_pos ha]
      exact ⟨fun h => absurd h (hγN a ha).ne, fun h => absurd h (by omega)⟩
    · rw [if_neg ha]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro σ sgn ρ hρ
    simp only [Fin.val_castLE, Fin.is_lt, if_true]

    have hent : ∀ a b : Fin j, w.mat b a = if (a : ℕ) = τ b then (t (γ b) : K) else 0 :=
      fun a b => ((ht b b.isLt).2.2.2 a a.isLt).2.2.2
    have key : ∀ a b : Fin j,
        (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * σ (w.mat b a * ((sgn a : ℤ) : K)) ≠ 0 →
          (a : ℕ) = τ b := by
      intro a b h
      by_contra hne
      apply h
      rw [hent a b, if_neg hne, zero_mul, map_zero, mul_zero]
    have hs : ∀ a : Fin j, ‖σ ((sgn a : ℤ) : K)‖ = 1 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]
    have hsK : ∀ a : Fin j, ((sgn a : ℤ) : K) ≠ 0 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]

    have hZ : (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) =
        Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) *
          (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ *
          Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
        Matrix.transpose_apply, Complex.ofReal_mul, map_mul]
      ring
    have hd : ∀ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 := fun a =>
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hρ.ne'))
    unfold GlobalTheory.Amp.BlockAnti
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact ((ht a a.isLt).2.2.2 b b.isLt).2.1 hab
    · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        show ((Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ).det =
          σ (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).det from
          (RingHom.map_det σ _).symm,
        Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hP : ∏ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun a _ => hd a
      refine mul_ne_zero (mul_ne_zero hP ?_) hP
      exact (map_ne_zero σ).mpr (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => hsK a)
        (GlobalTheory.SgLoc.PtAlg.isUnit_det w).ne_zero)
    · intro a b h
      have e := key a b h
      show γ a = γ b
      rw [e]
      exact (ht b b.isLt).2.2.1
    · intro a b a' b' h1 h2 hγ
      have hγ' : γ a = γ a' := hγ
      have e1 := key a b h1
      have e2 := key a' b' h2
      have hb : (b : ℕ) = τ a := by rw [e1, (ht b b.isLt).2.1]
      have hb' : (b' : ℕ) = τ a' := by rw [e2, (ht b' b'.isLt).2.1]
      have hsum : (a : ℕ) + τ a = a' + τ a' := ((ht a a.isLt).2.2.2 a' a'.isLt).2.2.1 hγ'
      refine ⟨?_, ?_, ?_⟩
      · have hγb : γ b = γ a := by rw [hb]; exact (ht a a.isLt).2.2.1
        have hγb' : γ b' = γ a := by rw [hb', hγ']; exact (ht a' a'.isLt).2.2.1
        have hw1 : w.mat b a = (t (γ a) : K) := by rw [hent a b, if_pos e1, hγb]
        have hw2 : w.mat b' a' = (t (γ a) : K) := by rw [hent a' b', if_pos e2, hγb']
        have ha := a.isLt
        have hb2 := b.isLt
        have ha' := a'.isLt
        have hb2' := b'.isLt
        have hexp : (r - b.val) + (r - a.val) = (r - b'.val) + (r - a'.val) := by omega
        have hc : ((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) =
            (ρ ^ (r - b'.val))⁻¹ * (ρ ^ (r - a'.val))⁻¹ := by
          rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, hexp]
        simp only [Matrix.of_apply]
        rw [hw1, hw2, hc, norm_mul, norm_mul, map_mul, map_mul, norm_mul, norm_mul, hs a, hs a']
      · intro haa
        subst haa
        exact Fin.ext (hb.trans hb'.symm)
      · intro hlt
        have hlt' : (a : ℕ) < a' := hlt
        exact Fin.lt_def.mpr (by omega)

end GlobalTheory.Amp.BlockFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquivStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_image_of_sqrt_two_isometric_linearEquiv : ∀ (A B F : Type) [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A] [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (r : ℕ) (L : ((A × A) × ((Fin r → ℂ) × B)) ≃L[ℝ] F), (∀ v, ‖L v‖ ^ 2 = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2) → ∀ s : Set ((A × A) × ((Fin r → ℂ) × B)), MeasurableSet s → volume (L '' s) = 2 ^ r * volume s := by
  first | exact @GlobalTheory.CellDens.ScaledVol.volume_image_eq | exact GlobalTheory.CellDens.ScaledVol.volume_image_eq | (intros; apply GlobalTheory.CellDens.ScaledVol.volume_image_eq <;> assumption)
end

