module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

open scoped Kronecker

namespace GlobalTheory.ModuLR

section Conj

theorem addEquivAddHaarChar_transport {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup B] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [LocallyCompactSpace B] [MeasurableSpace B] [BorelSpace B]
    (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) :
    addEquivAddHaarChar ((e.symm.trans φ).trans e) = addEquivAddHaarChar φ := by
  set ν : Measure A := Measure.addHaar
  set μ : Measure B := ν.map e
  haveI : μ.IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  haveI : μ.Regular := Measure.Regular.map e.toHomeomorph
  set ψ : B ≃ₜ+ B := (e.symm.trans φ).trans e
  have he : Measurable e := e.continuous.measurable
  have hφ : Measurable φ := φ.continuous.measurable
  have hψ : Measurable ψ := ψ.continuous.measurable
  have h1 := addEquivAddHaarChar_smul_map ν φ
  have h2 := addEquivAddHaarChar_smul_map μ ψ
  have hm : μ.map ψ = (ν.map φ).map e := by
    rw [Measure.map_map hψ he, Measure.map_map he hφ]
    congr 1
    funext x
    simp [ψ]
  have h3 : addEquivAddHaarChar φ • μ.map ψ = μ := by rw [hm, ← Measure.map_smul _ he.aemeasurable, h1]
  haveI : (μ.map ψ).IsAddHaarMeasure := ψ.isAddHaarMeasure_map μ
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : B)
  have hpos : (μ.map ψ) K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := μ.map ψ) hKn).ne'
  have htop : (μ.map ψ) K ≠ ⊤ := (hK.measure_lt_top).ne
  have h4 : (addEquivAddHaarChar ψ : ℝ≥0∞) * (μ.map ψ) K = (addEquivAddHaarChar φ : ℝ≥0∞) * (μ.map ψ) K := by
    have a2 := congrArg (fun m : Measure B => m K) h2
    have a3 := congrArg (fun m : Measure B => m K) h3
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at a2 a3
    rw [a2, a3]
  exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 h4

end Conj

section Det

variable {S : Type} [CommRing S] {m n : ℕ}

def lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin m) (Fin n) S →ₗ[S] Matrix (Fin m) (Fin n) S where
  toFun u := g * u * a
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c u := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem det_lrLin (g : Matrix (Fin m) (Fin m) S) (a : Matrix (Fin n) (Fin n) S) :
    LinearMap.det (lrLin g a) = g.det ^ n * a.det ^ m := by
  let e : Matrix (Fin m) (Fin n) S ≃ₗ[S] (Fin m × Fin n → S) := (LinearEquiv.curry S S (Fin m) (Fin n)).symm
  have key : (e : Matrix (Fin m) (Fin n) S →ₗ[S] (Fin m × Fin n → S)) ∘ₗ lrLin g a ∘ₗ
      (e.symm : (Fin m × Fin n → S) →ₗ[S] Matrix (Fin m) (Fin n) S) = Matrix.toLin' (g ⊗ₖ aᵀ) := by
    refine LinearMap.ext fun x => funext fun p => ?_
    obtain ⟨i, j⟩ := p
    change (g * Matrix.of (Function.curry x) * a) i j = _
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul, Function.curry_apply, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← LinearMap.det_conj (lrLin g a) e, key, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

end Det

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

section Restr

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev tensBasis : Module.Basis (Fin (Module.finrank F E)) (AF F) (AF F ⊗[F] E) :=
  Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)

def matCoord (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₗ[AF F] (Fin m × Fin n × Fin (Module.finrank F E) → AF F) where
  toFun u p := (tensBasis F E).equivFun (u p.1 p.2.1) p.2.2
  invFun x := Matrix.of fun i j => (tensBasis F E).equivFun.symm fun k => x (i, j, k)
  left_inv u := by
    ext i j
    simp only [Matrix.of_apply]
    exact (tensBasis F E).equivFun.symm_apply_apply (u i j)
  right_inv x := by
    funext p
    obtain ⟨i, j, k⟩ := p
    show (tensBasis F E).equivFun ((tensBasis F E).equivFun.symm fun k => x (i, j, k)) k = x (i, j, k)
    rw [LinearEquiv.apply_symm_apply]
  map_add' u v := by funext p; simp
  map_smul' c u := by funext p; simp

theorem continuous_matCoord (m n : ℕ) : Continuous (matCoord F E m n) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.toLinearMap
  exact continuous_pi fun p => (continuous_apply p.2.2).comp
    (hb.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))

theorem continuous_matCoord_symm (m n : ℕ) : Continuous (matCoord F E m n).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have hb : Continuous (tensBasis F E).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (tensBasis F E).equivFun.symm.toLinearMap
  exact continuous_pi fun i => continuous_pi fun j =>
    hb.comp (continuous_pi fun k => continuous_apply (i, j, k))

def matCoordCE (m n : ℕ) :
    Matrix (Fin m) (Fin n) (AF F ⊗[F] E) ≃ₜ+ (Fin m × Fin n × Fin (Module.finrank F E) → AF F) :=
  { (matCoord F E m n).toAddEquiv with
    continuous_toFun := continuous_matCoord F E m n
    continuous_invFun := continuous_matCoord_symm F E m n }

end Restr

end GlobalTheory.ModuLR

namespace GlobalTheory.ModuLR

theorem exists_matrix_restrictScalars_lrCE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  intro F E _ _ _ _ _ m n _ _ _ _ g a
  haveI : IsScalarTower (AF F) (AF F ⊗[F] E) (Matrix (Fin m) (Fin n) (AF F ⊗[F] E)) := inferInstance
  haveI : Module.Free (AF F) (AF F ⊗[F] E) := Module.Free.of_basis (tensBasis F E)
  haveI : Module.Finite (AF F) (AF F ⊗[F] E) := Module.Finite.of_basis (tensBasis F E)
  set Φ := matCoord F E m n
  set f : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) →ₗ[AF F ⊗[F] E] Matrix (Fin m) (Fin n) (AF F ⊗[F] E) :=
    lrLin (g : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) (a : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
  set Λ := LinearMap.toMatrix' (Φ.toLinearMap ∘ₗ f.restrictScalars (AF F) ∘ₗ Φ.symm.toLinearMap)
  have hdet : Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m :
      (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, det_lrLin]
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hΛ : IsUnit Λ.det := hdet ▸ (Units.isUnit _).map (Algebra.norm (AF F))
  refine ⟨_, inferInstance, inferInstance, Λ, hΛ, hdet, ?_⟩
  have hc : mulVecCE Λ hΛ = ((matCoordCE F E m n).symm.trans (lrCE g a)).trans (matCoordCE F E m n) := by
    ext x
    rw [mulVecCE_apply, LinearMap.toMatrix'_mulVec]
    rfl
  rw [hc, addEquivAddHaarChar_transport]

end GlobalTheory.ModuLR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUniqueIsContr
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ContrObj

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF]

theorem norm_of_isIsoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_riesz [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (φ : FF) (y : H₂) :
    ∃ w : H₁, ∀ x, ⟪x, w⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := by
  let ℓ : H₁ →L[ℂ] ℂ := ((innerₛₗ ℂ φ) ∘ₗ Tm.flip y).mkContinuous (‖φ‖ * ‖y‖) fun x => by
    have := norm_inner_le_norm (𝕜 := ℂ) φ (Tm x y)
    rw [norm_of_isIsoBilin hI] at this
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  obtain ⟨w, hw⟩ := (InnerProductSpace.toDual ℂ H₁).surjective ℓ
  refine ⟨w, fun x => ?_⟩
  have h : ⟪w, x⟫_ℂ = ⟪φ, Tm x y⟫_ℂ := by
    have := congrArg (fun f : H₁ →L[ℂ] ℂ => f x) hw
    simpa [ℓ] using this
  rw [← inner_conj_symm, h, inner_conj_symm]

theorem existsUnique_isContr [CompleteSpace H₁] {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃! It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  choose w hw using exists_riesz hI
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) w ?_ ?_ ?_ ?_, fun φ y x => hw φ y x, ?_⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp [hw, inner_add_right, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp [hw, inner_smul_right, inner_smul_left, mul_comm]
  · intro It hIt
    ext φ y
    exact ext_inner_left ℂ fun x => (hIt φ y x).trans (hw φ y x).symm

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  exact ⟨existsUnique_isContr hI, fun It hC => contrProps_of hI hE hC⟩

section Tensor

open MvPolynomial

variable {ι : Type} [Fintype ι] {σ : ι → Type} {Var : Type} (e : (Σ τ, σ τ) ≃ Var)

omit [Fintype ι] in
theorem emb_injective (i : ι) : Function.Injective fun s : σ i => e ⟨i, s⟩ :=
  e.injective.comp sigma_mk_injective

def res (α : Var →₀ ℕ) (i : ι) : σ i →₀ ℕ :=
  Finsupp.comapDomain (fun s : σ i => e ⟨i, s⟩) α (emb_injective e i).injOn

theorem res_sum (a : ∀ i, σ i →₀ ℕ) :
    res e (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) = a := by
  classical
  funext j
  ext s
  change (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i)) (e ⟨j, s⟩) = a j s
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · exact Finsupp.mapDomain_apply_of_injective (emb_injective e j) _ _
  · intro i _ hi
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨t, ht⟩
    exact hi (congrArg Sigma.fst (e.injective ht))
  · simp

variable {A B : ι → Type} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]

def tens (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) :
    MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] i, A i) →ₗ[ℂ] ⨂[ℂ] i, B i :=
  (basisMonomials Var ℂ).constr ℂ fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1)

theorem tens_prod (I : ∀ i, MvPolynomial (σ i) ℂ →ₗ[ℂ] A i →ₗ[ℂ] B i) (P : ∀ i, MvPolynomial (σ i) ℂ) :
    tens e I (∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i)) = PiTensorProduct.map fun i => I i (P i) := by
  classical
  let pr : MultilinearMap (RingHom.id ℂ) (fun i : ι => MvPolynomial (σ i) ℂ) (MvPolynomial Var ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun i => (rename (fun s : σ i => e ⟨i, s⟩) : MvPolynomial (σ i) ℂ →ₐ[ℂ] _).toLinearMap
  have hpr : ∀ P, pr P = ∏ i, rename (fun s : σ i => e ⟨i, s⟩) (P i) := fun P => by simp [pr]
  have key : (tens e I).compMultilinearMap pr
      = (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap I := by
    refine Module.Basis.ext_multilinear (fun i => basisMonomials (σ i) ℂ) fun a => ?_
    simp only [LinearMap.compMultilinearMap_apply, hpr, coe_basisMonomials,
      MultilinearMap.compLinearMap_apply, PiTensorProduct.mapMultilinear_apply, rename_monomial]
    rw [← monomial_sum_one]
    have := (basisMonomials Var ℂ).constr_basis ℂ
      (fun α => PiTensorProduct.map fun i => I i (monomial (res e α i) 1))
      (∑ i, Finsupp.mapDomain (fun s : σ i => e ⟨i, s⟩) (a i))
    rw [res_sum, coe_basisMonomials] at this
    exact this
  have := congrArg (fun f => f P) key
  simpa [hpr] using this

theorem tprod_ne_zero (v : ∀ i, B i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

end Tensor

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ I
  have h : IsTensorIt e I (tens e I) := fun P v => by
    rw [tens_prod, PiTensorProduct.map_tprod]
  refine ⟨tens e I, h, fun hI h0 => ?_⟩
  have hex : ∀ i, ∃ P v, I i P v ≠ 0 := by
    intro i
    by_contra hc
    push Not at hc
    exact hI i (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using hex
  have h1 := h P v
  rw [h0] at h1
  exact tprod_ne_zero _ hPv h1.symm

theorem contraction : GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.Contraction := ⟨contrHilbert, contrTensor⟩

end GlobalTheory.ContrObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteIntegersTopology
section
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.ModuLR

theorem finiteIntegers_compact_secondCountable_t2 : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), CompactSpace (OPart F S) ∧ SecondCountableTopology (OPart F S) ∧ T2Space (OPart F S) := by
  intro F _ _ S
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, CompactSpace (v.1.adicCompletionIntegers F) :=
    fun v => GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v.1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    fun v => secondCountable_of_proper
  haveI : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, SecondCountableTopology (v.1.adicCompletionIntegers F) :=
    fun v => TopologicalSpace.Subtype.secondCountableTopology _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.ModuLR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceRelativeNormLeLocalSizePow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix NumberField IsDedekindDomain
open scoped NNReal TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormFin
open GlobalTheory.AdelicU

theorem nnnorm_algebraMap_norm_le (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (y : E) :
    ‖algebraMap F (Fv F v) (Algebra.norm F y)‖₊ ≤
      absFin F v ((1 : Fv F v) ⊗ₜ[F] y) ^ Module.finrank F E := by
  rw [← absBar_algebraMap F v, ← IsScalarTower.algebraMap_apply,
    Algebra.norm_eq_prod_embeddings F (FvBar F v) y]
  rw [show absBar F v (∏ τ : E →ₐ[F] FvBar F v, τ y) = ∏ τ : E →ₐ[F] FvBar F v, absBar F v (τ y) from
    map_prod (valBar F v) _ _]
  rw [← AlgHom.card F E (FvBar F v), ← Finset.card_univ]
  refine Finset.prod_le_pow_card _ _ _ fun τ _ => ?_
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] y)
  simpa using this

theorem normFin_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (y : D.host.E) :
    ‖algebraMap D.host.F (Fv D.host.F v) (Algebra.norm D.host.F y)‖₊ ≤
      GlobalTheory.AdelicU.absFin D.host.F v ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] y) ^ Module.finrank D.host.F D.host.E :=
  nnnorm_algebraMap_norm_le D.host.F v y

end GlobalTheory.NormFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
section
open Classical MeasureTheory

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def colMat {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Matrix (Var ι d a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.1 = v.2.1 then g v.1 w.2.2 v.2.2 else 0

theorem colSub_eq_lsub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a) = GlobalTheory.JointHarm.FMul.lsub (colMat g) := by
  refine algHom_ext fun v => ?_
  rw [GlobalTheory.JointHarm.FMul.lsub_X, colSub, aeval_X]
  obtain ⟨τ, r, c⟩ := v
  simp only [colMat, Fintype.sum_prod_type, ite_and, apply_ite C, map_zero, ite_mul, zero_mul]
  simp

theorem colMat_conjTranspose {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colMat (d := d) g)ᴴ = colMat fun τ => (g τ)ᴴ := by
  ext w v
  simp only [colMat, conjTranspose_apply]
  by_cases h : v.1 = w.1 ∧ v.2.1 = w.2.1
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, star_zero]

theorem colSub_comp {d a : ℕ} (h g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub h : Pol ι d a →ₐ[ℂ] Pol ι d a).comp (colSub g) = colSub fun τ => h τ * g τ := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply]
  unfold colSub
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_X, aeval_X, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colSub_one {d a : ℕ} : (colSub (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) =
    AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [colSub, aeval_X, Finset.sum_eq_single v.2.2]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne hb]
    simp
  · simp

theorem fockS_colSub_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ)
    (P Q : GlobalTheory.MinorFrame.Pol ι d a),
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
      (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  intro ι _ a d u P Q
  rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, colSub_eq_lsub, GlobalTheory.JointHarm.FMul.fockL_lsub_adj,
    ← colSub_eq_lsub, colMat_conjTranspose, ← colSub_eq_lsub, ← AlgHom.comp_apply, colSub_comp]
  have hu : (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)ᴴ * (u τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => 1 := by
    funext τ
    exact Matrix.mem_unitaryGroup_iff'.1 (u τ).2
  rw [hu, colSub_one, AlgHom.id_apply]

end GlobalTheory.MinorFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.HeckeUnitaryInf

theorem isUnitary_of_hasInf : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I]
    (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  intro L _ _ χ I _ φ n h
  have hinf : ∀ k : Lˣ, ‖((χ.1 (Formalism.L2.Host.infDiag k) : ℂˣ) : ℂ)‖ = 1 := by
    intro k
    have e : ((χ.1 (Formalism.L2.Host.infDiag k) : ℂˣ) : ℂ) = _ := h k
    rw [e, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    have h0 : φ i (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    rw [norm_zpow, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 h0), one_zpow]
  have hI : ∀ y : (InfiniteAdeleRing L)ˣ, ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖ = 1 := by
    have := (GlobalTheory.HeckeGal.denseRange_units_inf L).equalizer
      (g := fun y => ‖((χ.1 (GlobalTheory.HeckeGal.inlInf L y) : ℂˣ) : ℂ)‖) (h := fun _ => (1 : ℝ))
      ((Units.continuous_val.comp (χ.2.1.comp GlobalTheory.HeckeGal.continuous_inlInf)).norm) continuous_const
      (funext fun k => by
        simp only [Function.comp_apply]
        rw [← GlobalTheory.HeckeGal.infDiag_eq]
        exact hinf k)
    exact fun y => congrFun this y
  have hF : ∀ x : Neutral.B1.Ideles L, Formalism.L2.Host.IsFinIdele x → ‖((χ.1 x : ℂˣ) : ℂ)‖ = 1 := by
    intro x hx
    obtain ⟨m, hm, u, k, u1, u2, e⟩ := GlobalTheory.UnUnitCmp.Val.exists_pow_eq x hx
    have e1 := congrArg (fun a => ‖((χ.1 a : ℂˣ) : ℂ)‖) e
    simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hinf k,
      GlobalTheory.HeckeFin.norm_eq_one χ u u1 u2, χ.2.2 k, Units.val_one, norm_one, mul_one] at e1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e1
  intro z
  have hz : z = GlobalTheory.HeckeGal.inlInf L (Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) z) *
      finPartI L z := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [hz, map_mul, Units.val_mul, norm_mul, hI, hF _ (fun _ => rfl), one_mul]

end GlobalTheory.HeckeUnitaryInf
end
end

