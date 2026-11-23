module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNLevi

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

def qI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    ((RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F)))

def qF (F : Type) [Field F] [NumberField F] : F →+* FiniteAdeleRing (𝓞 F) F :=
  (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap F (AdeleRing (𝓞 F) F))

def compM (P : Matrix κ κ F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x)

theorem compM_apply (P : Matrix κ κ F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (x : κ → AdeleRing (𝓞 F) F) :
    compM P φ x = φ (P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) := rfl

def archEquiv (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun y := P.map (qI F) *ᵥ y
  invFun y := Q.map (qI F) *ᵥ y
  map_add' y y' := Matrix.mulVec_add _ _ _
  map_smul' r y := by rw [RingHom.id_apply, Matrix.mulVec_smul]
  left_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv y := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def finHomeo (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) where
  toFun z := P.map (qF F) *ᵥ z
  invFun z := Q.map (qF F) *ᵥ z
  left_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  right_inv z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem comp_pureA (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    compM P (pureA F f g) =
      pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv P Q hPQ hQP) f) (g ∘ finHomeo P Q hPQ hQP) := by
  funext x
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let p : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).1) =
      P.map (qI F) *ᵥ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext i
    change q ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  have h2 : (fun i => ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i).2) =
      P.map (qF F) *ᵥ (fun i => (x i).2) := by
    funext i
    change p ((P.map (algebraMap F (AdeleRing (𝓞 F) F)) *ᵥ x) i) = _
    rw [RingHom.map_mulVec, Matrix.map_map]
    rfl
  simp only [compM_apply, pureA, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [h1, h2]
  rfl

theorem comp_mem (P Q : Matrix κ κ F) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∀ φ ∈ schA F κ, compM P φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (compM P) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    refine Submodule.subset_span ⟨_, _, ⟨hg.1.comp_continuous (finHomeo P Q hPQ hQP).continuous,
      hg.2.comp_homeomorph (finHomeo P Q hPQ hQP)⟩, comp_pureA P Q hPQ hQP f g⟩
  exact fun φ hφ => hle hφ

theorem act_levi {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks A 0 0 B) w = (A.map (algebraMap K R) *ᵥ w.1, B.map (algebraMap K R) *ᵥ w.2) := by
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, add_zero, zero_add]

theorem dot_transpose {R ι : Type} [CommRing R] [Fintype ι] (M : Matrix ι ι R) (x v : ι → R) :
    x ⬝ᵥ (Mᵀ *ᵥ v) = (M *ᵥ x) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem realised_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ]
    [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det → Realised ψ (Matrix.fromBlocks A 0 0 (A⁻¹)ᵀ) := by
  intro F _ _ ψ κ _ _ A hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  let Am : Matrix κ κ (AdeleRing (𝓞 F) F) := A.map (algebraMap F (AdeleRing (𝓞 F) F))
  let Aim : Matrix κ κ (AdeleRing (𝓞 F) F) := A⁻¹.map (algebraMap F (AdeleRing (𝓞 F) F))
  have e1 : Am * Aim = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Aim * Am = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨compM A⁻¹, comp_mem A⁻¹ A h2 h1, fun φ hφ => ⟨compM A φ, comp_mem A A⁻¹ h1 h2 φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ compM A⁻¹, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    change φ (Am *ᵥ (Aim *ᵥ x)) = φ x
    rw [Matrix.mulVec_mulVec, e1, Matrix.one_mulVec]
  · obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo A⁻¹ A h2 h1).continuous,
      hg.2.comp_homeomorph (finHomeo A⁻¹ A h2 h1)⟩
    refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv A⁻¹ A h2 h1)), fun f => ?_⟩
    rw [LinearMap.comp_apply, comp_pureA A⁻¹ A h2 h1, hT]
    rfl
  · rw [act_levi, Matrix.transpose_map]
    change ψ ((Aim *ᵥ x) ⬝ᵥ w.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)) * φ (Aim *ᵥ x + w.1) =
      ψ (x ⬝ᵥ (Aimᵀ *ᵥ w.2) + ⅟(2 : AdeleRing (𝓞 F) F) * ((Am *ᵥ w.1) ⬝ᵥ (Aimᵀ *ᵥ w.2))) *
        φ (Aim *ᵥ (x + Am *ᵥ w.1))
    rw [dot_transpose, dot_transpose, Matrix.mulVec_add, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

end GlobalTheory.AdelicSvNLevi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped _root_.Matrix

namespace GlobalTheory.AdelicSvN.Weyl

variable {F : Type} [Field F] [NumberField F]

theorem trace_eq_mixedTrace (m : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) m = mixedTrace F m := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, mixedTrace_apply]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem isStd_infinite {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (z : InfiniteAdeleRing F) :
    ψ (infiniteAdeleInl z) = (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have hat : At (evI F) (infiniteAdeleInl z : AF F) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [hψ.2.2 _ hat, h2, trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a = (adelicChar F a : ℂ) := by
  have hfin : ∀ y : FiniteAdeleRing (𝓞 F) F,
      ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ) := by
    intro y
    refine (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).induction_on
      (p := fun y => ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ)) y
      (isClosed_eq (hψ.1.comp continuous_finiteAdeleInr)
        (continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp continuous_finiteAdeleInr))) fun k => ?_
    have hs := infiniteAdeleInl_add_finiteAdeleInr (algebraMap F (AF F) k)
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hs
    have e : (finiteAdeleInr (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AF F) =
        algebraMap F (AF F) k + infiniteAdeleInl (-algebraMap F (InfiniteAdeleRing F) k) := by
      rw [← hs, map_neg]; abel
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.1, adelicChar_algebraMap, one_mul, one_mul,
      isStd_infinite hψ]
  rw [← infiniteAdeleInl_add_finiteAdeleInr a, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
    isStd_infinite hψ, hfin]

variable {κ : Type} [Fintype κ]

theorem pureA_eq (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g = schwartzBruhatTensorPi f g := by
  funext x
  simp only [pureA, schwartzBruhatTensorPi]
  rfl

omit [Fintype κ] in
theorem mem_SB_iff (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ↔ g ∈ finiteSchwartzBruhatPi F :=
  (mem_finiteSchwartzBruhatPi F).symm

theorem schA_eq : schA F κ = schwartzBruhatPi (K := F) (ι := κ) := by
  unfold schA schwartzBruhatPi
  congr 1

def fourierLin : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := adelicFourierPi F φ.1
  map_add' φ φ' := adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ.2))
    (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ'.2))
  map_smul' c φ := adelicFourierPi_smul c φ.1

theorem act_weyl [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    act (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) w = (w.2, -w.1) := by
  have h0 : (0 : Matrix κ κ F).map (algebraMap F (AF F)) = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : (1 : Matrix κ κ F).map (algebraMap F (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (-1 : Matrix κ κ F).map (algebraMap F (AF F)) = -1 := by rw [Matrix.map_neg _ (map_neg _), h1]
  simp only [act, Matrix.fromBlocks_map, h0, h1, h2, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem integral_add_right_pi (f : (κ → AF F) → ℂ) (a : κ → AF F) :
    ∫ x, f (x + a) ∂(adeleMeasurePi F) = ∫ x, f x ∂(adeleMeasurePi F) := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have : MeasurableAdd (κ → AdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  exact integral_add_right_eq_self f a

theorem fourier_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    adelicFourierPi F (schr ψ w φ) = schr ψ (w.2, -w.1) (adelicFourierPi F φ) := by
  funext y
  simp only [adelicFourierPi, schr, ← isStd_eq hψ]
  rw [← integral_const_mul, ← integral_add_right_pi _ (-w.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  have e : ((x + -w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (x + -w.1) ⬝ᵥ y =
      (y ⬝ᵥ -w.1 + ⅟(2 : AF F) * (w.2 ⬝ᵥ -w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, dotProduct_comm y w.1,
      dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  have e' := congrArg ψ e
  rw [AddChar.map_add_eq_mul ψ _ ((x + -w.1) ⬝ᵥ y), AddChar.map_add_eq_mul ψ _ (x ⬝ᵥ (y + w.2))] at e'
  simp only [neg_add_cancel_right]
  change _ * _ * ψ ((x + -w.1) ⬝ᵥ y) = _ * (_ * ψ (x ⬝ᵥ (y + w.2)))
  linear_combination φ x * e'

theorem realised_weyl : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  intro F _ _ ψ hψ κ _ _
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  refine ⟨adelicFourierPi F, hk, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩, fun l hl => ?_, fun w φ _ => ?_⟩
  · rw [hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
    have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
    refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => by rw [LinearMap.comp_apply, hT' φ hφ]⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [act_weyl, fourier_schr hψ]

end GlobalTheory.AdelicSvN.Weyl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitGramAt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isUnit_gramAt (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ) := by
  rw [← M.fr_gram τ]
  have hJ : IsUnit (Formalism.REAL.Jm (M.ε τ)) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    split_ifs <;> simp
  exact (((Matrix.isUnit_conjTranspose _).2 (M.fr_unit τ)).mul hJ).mul (M.fr_unit τ)

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) {a b : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hb : b ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) ha) _
    (GlobalTheory.GardingVec.conj_mem (M.fr_unit τ) (M.fr_gram τ) hb)
  have e : M.fr τ * (a * b) * (M.fr τ)⁻¹ = M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  unfold DSModel.rep
  rw [e, h]
  rfl

theorem prod_mul_eq {G : Type} [Monoid G] (h : G) : ∀ (k : ℕ) (u v : Fin k → G), (∀ i, u i * h = h * v i) →
    (List.ofFn u).prod * h = h * (List.ofFn v).prod
  | 0, _, _, _ => by simp
  | k + 1, u, v, e => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_mul_eq h k _ _ fun i => e i.succ, ← mul_assoc, e, mul_assoc]

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {v : M.H τ} (hv : v ∈ M.sm τ) : M.rep τ g v ∈ M.sm τ := by
  have hG := isUnit_gramAt M τ
  have hgu : IsUnit g.det := by
    have h1 : IsUnit (gᴴ * gramAt D V τ * g) := by rw [show gᴴ * gramAt D V τ * g = _ from hg]; exact hG
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hab : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgu
  induction hv using Submodule.span_induction with
  | mem w hw =>
    refine Submodule.subset_span fun k Xs hX => ?_
    have hX' : ∀ i, g⁻¹ * Xs i * g ∈ lieAt V τ := fun i => GlobalTheory.Mem.RealTranslate.skew_conj hg hab (hX i)
    have h1 := ((M.rep τ g).restrictScalars ℝ).contDiff.comp (hw k (fun i => g⁻¹ * Xs i * g) hX')
    have hm : ∀ (Y : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i, Y i ∈ lieAt V τ) → ∀ t : Fin k → ℝ,
        (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun Y hY t =>
      GlobalTheory.GardingVec.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.GardingVec.exp_mem hG (hY i) (t i)
    convert h1 using 1
    funext t
    show _ = M.rep τ g (M.rep τ _ w)
    rw [← rep_mul M τ (hm Xs hX t) hg, ← rep_mul M τ hg (hm _ hX' t),
      prod_mul_eq g k _ _ fun i => GlobalTheory.Mem.RealTranslate.exp_conj_eq hab (Xs i) (t i)]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable {θ} {M : DSModel V S}

end GlobalTheory.UnifEvery
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftWeight

theorem one_le_aPl_last (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n + 1 = p) :
    1 ≤ aPl D i p τ n := by
  subst hp
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hlt : n < D.R.k + (i : ℕ) := by omega
  have h1 : ¬ n < D.R.k - 1 := by omega
  have h2 : n - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨n - (D.R.k - 1), h2⟩ : Fin D.R.m) = i := Fin.ext (by simp only; omega)
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) n = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right h1, dite_eq_left h2, hidx]
  have hg := (D.hc τ).gap_be i
  have hq : ((D.R.k + (i : ℕ) : ℕ) : ℚ) = (n : ℚ) + 1 := by
    rw [← hn]; push_cast; ring
  simp only [aPl, if_pos hlt]
  rw [hlam, hq]
  have hfl : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - ((n : ℚ) + 1 - ((n : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

theorem kapTop_lastPos (D : D7) (i : Fin D.R.m) : (kapTop D i).LastPos := by
  intro τ k hk
  have hi : (i : ℕ) < D.R.m := i.isLt
  have hW := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D τ)
  have hs : ((Wc D i).sig (tauE D τ)).1 = D.R.k + (i : ℕ) := by
    show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = D.R.k + (i : ℕ)
    rw [hW]
    show D.R.k + ((i : ℕ) + 1) - 1 = D.R.k + (i : ℕ)
    omega
  have hk' : (k : ℕ) + 1 = D.R.k + (i : ℕ) := by
    have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + ((i : ℕ) + 1) - 1 := rfl
    omega
  exact one_le_aPl_last D i τ _ k hs (hk'.trans hs.symm)

end GlobalTheory.LiftWeight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrime
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.PrimePart

theorem exists_integral_inverse_lieVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), UnramIn E p → ∀ [DecidableEq (Lt1 Dw)], ∃ L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C, (∀ a b, IsIntV (vX_vp X) (L a b)) ∧ L * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 ∧ (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1 := by
  intro E _ _ _ H Dw l Xo c _ p _ T io X y Ch hp inst
  have hbij := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose σV hσV using fun τ : E →+* ℂ =>
    GlobalTheory.PowGerm.exists_lift_ringOfIntegers (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hι : ∀ τ a, X.ι (σV τ a) = embO io X τ a := fun τ a => X.ints.hom_inj (by
    rw [algebraMap_embO, ← X.comp, hσV']; rfl)
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit (σV τ a - σV τ' a) := by
    intro τ τ' hne
    have h1 : red io X τ ≠ red io X τ' := fun h => hne (hbij.1 h)
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 h1
    refine ⟨a, ?_⟩
    have := X.ι_local
    refine (isUnit_map_iff X.ι _).1 ?_
    rw [map_sub, hι, hι]
    by_contra hu
    apply ha
    rw [← sub_eq_zero]
    show residue X.O _ - residue X.O _ = 0
    rw [← map_sub, residue_eq_zero_iff]
    exact (mem_maximalIdeal _).2 hu
  have hex : ∃ lam : Lt1 Dw → Fin (chD Ch.ch) → T.V, ∀ l l', ∑ s, lam l s * Ch.uvecT l' s = if l = l' then 1 else 0 := by
    classical
    obtain ⟨lam, hlam⟩ := GlobalTheory.exists_dual_forms_of_separated_types T.V (𝓞 E) (chD Ch.ch)
      (fun a => Matrix.of fun m j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a m))
      (E →+* ℂ) Dw.mult (fun τ a => σV τ a) Ch.uvecT hsep
      (fun a ℓ => ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a _ (hσV' _ _)) (fun τ => by
        obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
        exact GlobalTheory.PowGerm.exists_dual_of_extends (fun i => Ch.uvecT ⟨τ, i⟩) w emb hw hb)
    exact ⟨lam, fun l l' => by convert hlam l l'⟩
  obtain ⟨lam, hlam⟩ := hex
  have h1 : (Matrix.of fun ℓ e => jX X (lam ℓ e)) * (Matrix.of fun e ℓ => lieVec Ch X ℓ e) = 1 := by
    ext ℓ ℓ'
    have h := congrArg (jX X) (hlam ℓ ℓ')
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_mul] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, lieVec]
    rw [h]
    split_ifs
    · exact map_one _
    · exact map_zero _
  refine ⟨Matrix.of fun ℓ e => jX X (lam ℓ e), fun a b => isIntV_jX X _, h1, ?_⟩
  have e : Lt1 Dw ≃ Fin (chD Ch.ch) := Fintype.equivFinOfCardEq (GlobalTheory.IntChartCheck.dim_eq Ch).symm
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 h1

end GlobalTheory.PrimePart
end

