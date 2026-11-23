module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0125
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0118
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramMatrixIntegralAlmostAllPlaces
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

private theorem tensorBasis_repr_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (c : R) (e : E) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m = c * algebraMap F R (b.repr e m) := by
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp [Algebra.smul_def]

private theorem eq_sum_repr_tmul_basis {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (z : R ⊗[F] E) :
    z = ∑ k, ((Algebra.TensorProduct.basis R b).repr z k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem tensorBasis_repr_sum_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) {ι : Type} (s : Finset ι)
    (f : ι → R ⊗[F] E) (h : ∀ x ∈ s, ∀ m, (Algebra.TensorProduct.basis R b).repr (f x) m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (∑ x ∈ s, f x) m ∈ O := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact O.sum_mem fun x hx => h x hx m

private theorem tensorBasis_repr_tmul_mem_of_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (c : R) (e : E) (hc : c ∈ O)
    (he : ∀ m, algebraMap F R (b.repr e m) ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (c ⊗ₜ[F] e) m ∈ O := by
  rw [tensorBasis_repr_tmul]
  exact O.mul_mem hc (he m)

private theorem tensorBasis_repr_mul_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R)
    (hb : ∀ k l m, algebraMap F R (b.repr (b k * b l) m) ∈ O) (z w : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O)
    (hw : ∀ m, (Algebra.TensorProduct.basis R b).repr w m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m ∈ O := by
  rw [eq_sum_repr_tmul_basis b z, eq_sum_repr_tmul_basis b w, Finset.sum_mul_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun l _ m'' => ?_) m') m
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (O.mul_mem (hz k) (hw l)) (hb k l) m''

private theorem tensorBasis_repr_sigR_mem_of_repr_mem {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (O : Subring R) (σ : E →ₐ[F] E)
    (hs : ∀ k m, algebraMap F R (b.repr (σ (b k)) m) ∈ O) (z : R ⊗[F] E)
    (hz : ∀ m, (Algebra.TensorProduct.basis R b).repr z m ∈ O) (m : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (sigR R σ z) m ∈ O := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eq_sum_repr_tmul_basis b z, map_sum]
  refine tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun k _ m' => ?_) m
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  exact tensorBasis_repr_tmul_mem_of_mem b O _ _ (hz k) (hs k) m'

theorem hermOf_sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ),
    2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a c, σ (T c a) = T a c),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
        hermOf (Fv F v) σ T hT - gramH hCM hJ (Fv F v) X ∈ latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b T hT
  have intF : ∀ t : F, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) t ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
    intro t
    filter_upwards [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b t] with v hv
    have h0 := hv 0 (fun a i k => by simp)
    simpa [qR, hR, Formalism.UG.hform] using h0
  have hdiag := Filter.eventually_all.2 fun i : Fin n =>
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.sub_qR_mem_integers F E σ hCM M J hJ d b ((1 / 2) * Algebra.trace F E (T i i))
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k l m,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l => Filter.eventually_all.2 fun m => intF _
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k m,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => intF _
  have h3 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ p q m,
      algebraMap F (Fv F v) (b.repr (J p q) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q => Filter.eventually_all.2 fun m => intF _
  have h4 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j m,
      algebraMap F (Fv F v) (b.repr (T i j) m) ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun m => intF _
  filter_upwards [hdiag, h1, h2, h3, h4] with v hd hb hs hJv hTv
  intro X hX
  clear intF hdiag h1 h2 h3 h4
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  unfold latH gramH
  refine ⟨fun i => ?_, fun i j _ k => ?_⟩
  · have hX' := hd i (fun _ => X i) (fun _ a k => hX i a k)
    convert hX' using 1
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, qR, Matrix.map_apply, map_sub, mul_sub]
    congr 1
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, map_mul]
  · let O : Subring (Fv F v) := (HeightOneSpectrum.adicCompletionIntegers F v).toSubring
    have gX : ∀ a p m, (Algebra.TensorProduct.basis (Fv F v) b).repr (X a p) m ∈ O := fun a p m => hX a p m
    have gI : ∀ e : E, (∀ m, algebraMap F (Fv F v) (b.repr e m) ∈ O) →
        ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) e) m ∈ O := by
      intro e he m
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [tensorBasis_repr_tmul, one_mul]
      exact he m
    have gH : ∀ m, (Algebra.TensorProduct.basis (Fv F v) b).repr (hR (Fv F v) σ J (X i) (X j)) m ∈ O := by
      intro m
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply]
      exact tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun p _ m' => tensorBasis_repr_sum_mem_of_repr_mem b O _ _ (fun q _ m'' =>
        tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (fun m3 => tensorBasis_repr_mul_mem_of_repr_mem b O hb _ _ (tensorBasis_repr_sigR_mem_of_repr_mem b O σ hs _ (gX i p))
          (gI _ (hJv p q)) m3) (gX j q) m'') m') m
    have gT := gI (T i j) (hTv i j)
    simp only [AddSubgroup.coe_sub, Matrix.sub_apply, hermOf, gramR, Matrix.map_apply, map_sub,
      Finsupp.coe_sub, Pi.sub_apply]
    exact O.sub_mem (gT k) (gH k)

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFamilyAnisotropicJoint
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ A x y = (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) := by
  have : hE σ A x y = ∑ i, ∑ j, σ (x i) * A i j * y j := rfl
  rw [this]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_normMat (σ : E →ₐ[F] E) {n : ℕ} (l ξ : Fin n → E) :
    hE σ (normMat σ l) ξ ξ = σ (l ⬝ᵥ ξ) * (l ⬝ᵥ ξ) := by
  have : hE σ (normMat σ l) ξ ξ = ∑ i, ∑ j, σ (ξ i) * (σ (l i) * l j) * ξ j := rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_eq_zero_of_hE_normMat (σ : E →ₐ[F] E) {n : ℕ} {l ξ : Fin n → E}
    (h : hE σ (normMat σ l) ξ ξ = 0) : l ⬝ᵥ ξ = 0 := by
  rw [hE_normMat] at h
  rcases mul_eq_zero.1 h with h | h
  · exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h
  · exact h

theorem hE_conj (σ : E →ₐ[F] E) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    hE σ (cT (σ : E →+* E) P * J * P) ξ ξ = hE σ J (P *ᵥ ξ) (P *ᵥ ξ) := by
  rw [hE_eq_dot, hE_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT (σ : E →+* E) P)]
  congr 1
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem anisoProj_mulVec (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (ξ : Fin n → E) (hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0) (hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0) :
    anisoProj σ J X Y *ᵥ ξ = ξ := by
  have h0 : ∀ k, projFam σ J X Y k *ᵥ ξ = 0 := by
    rintro (i | i)
    · simp only [projFam, Sum.elim_inl, lineProj, Matrix.vecMulVec_mulVec, hY i]
      ext k
      simp
    · simp only [projFam, Sum.elim_inr, lineProj, Matrix.vecMulVec_mulVec, hX i]
      ext k
      simp
  rw [anisoProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Finset.sum_eq_zero fun k _ => h0 k, sub_zero]

end GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem hermFam_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E,
    (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y hW ξ h
  have hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inl i)))
  have hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inr i)))
  have hπ := HermNondeg.anisoProj_mulVec σ J X Y ξ hX hY
  have hn : hE σ J ξ ξ = 0 := by
    have := h none
    change hE σ (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) ξ ξ = 0 at this
    rwa [HermNondeg.hE_conj, hπ] at this
  refine hW.aniso ξ ?_ ?_ hn
  · ext i
    exact hX i
  · ext i
    exact hY i

end GlobalTheory.CompanionTheory.ParCocompact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def BsetF (σ : E →ₐ[F] E) {n : ℕ} (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibSF (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (BsetF R σ B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def UsetF (B₀ : Set R) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) ∩
    {X | LinearIndependent (R ⊗[F] E) X}

def MidF {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S',
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure HermitianMeasureData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.StageF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationVanishesAboveDimension
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FilTop

section Inj
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem toSq_pullC_bij (a b : IdF A) (ha : ∀ T, a.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (n : ℕ) :
    Function.Bijective ((toSq a b ha).pullC n) := by
  have hτ : ∀ T, Function.Bijective ((toSq a b ha).τ T) := by
    intro T
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : (Ideal.Quotient.mk (b.S T) (show A.obj T from x)) = Ideal.Quotient.mk (b.S T) (show A.obj T from y) :=
        congrArg Subtype.val hxy
      rw [Ideal.Quotient.eq, hb T, Ideal.mem_bot, sub_eq_zero] at h1
      exact h1
    · obtain ⟨z, hz⟩ := z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨x, rfl⟩
  refine ⟨fun f g hfg => ?_, fun f' => ?_⟩
  · funext s
    exact (hτ _).1 (congrFun hfg s)
  · refine ⟨fun s => Function.surjInv (hτ _).2 (f' s), ?_⟩
    funext s
    exact Function.surjInv_eq (hτ _).2 (f' s)

end Inj

theorem pull_inj_of_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {C' : Type 1} [Category.{0} C']
    {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
    (hb : ∀ n, Function.Bijective (m.pullC n)) (n : ℕ) : Function.Injective (m.pull n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  change m.pull n (Submodule.Quotient.mk z) = 0 at hx
  unfold CH.Mor.pull Cx.Hom.mapH at hx
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  change m.pullC n z.1 ∈ (CH.cx F').B n at hx
  change z.1 ∈ (CH.cx F).B n
  cases n with
  | zero =>
    have h0 : m.pullC 0 z.1 = 0 := hx
    have : z.1 = 0 := (hb 0).1 (h0.trans (map_zero _).symm)
    rw [this]; exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g0, rfl⟩ := (hb n).2 g
    refine ⟨g0, (hb (n + 1)).1 ?_⟩
    change m.pullC (n + 1) (CH.d F n g0) = m.pullC (n + 1) z.1
    rw [← CH.Mor.d_pullC]
    exact hg

theorem fil_top_vanish : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  intro _ _ _ _ _ hKIso _ K _ _ X q _ d _ j x hx
  obtain ⟨U, hU⟩ := (_root_.GlobalTheory.CompanionTheory.CovEx.exists_cov q).2 d inferInstance
  have h𝒱 : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hk := hKIso q U (d + 1) (fun α => by rw [hU α]; omega) (Set.range U.U) h𝒱 j
  have h0 : quoK q (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ) j x = 0 := (hk.2 (d + 1) le_rfl x).1 hx
  have hb : ∀ T, (sFil (KS q (d + 1) (Set.range U.U)) ((d + 1 : ℕ) : ℤ)).S T = ⊥ := by
    intro T
    change T.obj.pdPow ((d + 1 : ℕ) : ℤ).toNat = ⊥
    rw [Int.toNat_natCast]
    exact T.property.1.1
  have hinj := GlobalTheory.CompanionTheory.FilTop.pull_inj_of_bij _
    (GlobalTheory.CompanionTheory.FilTop.toSq_pullC_bij (sFil (KS q (d + 1) (Set.range U.U)) 0) _ (fun T => T.obj.pdPow_zero) hb) j
  have h1 : resK q (KS q (d + 1) (Set.range U.U)) j x = 0 := hinj (by
    rw [map_zero]; exact h0)
  exact hk.1.1 (h1.trans (map_zero _).symm)

end GlobalTheory.CompanionTheory.FilTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

def hypOne {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (A i))))

section Entries

variable {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)

theorem hypOne_zero_zero : hypOne A 0 0 = 0 := rfl
theorem hypOne_zero_one : hypOne A 0 1 = 1 := rfl
theorem hypOne_one_zero : hypOne A 1 0 = 1 := rfl
theorem hypOne_one_one : hypOne A 1 1 = 0 := rfl
theorem hypOne_zero_rest (j : Fin M) : hypOne A 0 j.succ.succ = 0 := rfl
theorem hypOne_one_rest (j : Fin M) : hypOne A 1 j.succ.succ = 0 := rfl
theorem hypOne_rest_zero (i : Fin M) : hypOne A i.succ.succ 0 = 0 := rfl
theorem hypOne_rest_one (i : Fin M) : hypOne A i.succ.succ 1 = 0 := rfl
theorem hypOne_rest_rest (i j : Fin M) : hypOne A i.succ.succ j.succ.succ = A i j := rfl

end Entries

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianMonicAnnihilatorMeasureStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacian_monic_annihilator_measure : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | exact GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | (intros; apply GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian <;> assumption)
end

