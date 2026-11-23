module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0004
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0007
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ToRHomeomorphMixedSpace
public import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinInfGLMulVec
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem Phi_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    Phi c v = archS F (vInf v) * finRow c v := by
  rw [archS_apply]; rfl

theorem PhiH_eq (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    PhiH c v = archS F (vInf v) * finCol c v := by
  rw [archS_apply]; rfl

theorem finRow_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finRow c v = finRow c v' := by
  unfold finRow; rw [h 0, h 1]

theorem finCol_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {v v' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (v i) = pFin F (v' i)) : finCol c v = finCol c v' := by
  unfold finCol; rw [h 0, h 1]

theorem map_pFin_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (pFin F) = 1 :=
  congrArg Units.val (UpperTheory.V.TR.pFin_infGL y)

theorem map_pInf_infGL (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :=
  congrArg Units.val (UpperTheory.V.TR.pInf_infGL y)

theorem pFin_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) i) = pFin F (v i) := by
  rw [RingHom.map_vecMul, map_pFin_infGL, Matrix.vecMul_one]; rfl

theorem vInf_vecMul_infGL (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (v ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) =
      vInf v ᵥ* (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) := by
  funext i
  simp only [vInf]
  rw [RingHom.map_vecMul, map_pInf_infGL]; rfl

theorem pFin_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i : Fin 2) :
    pFin F ((((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) i) = pFin F (v i) := by
  rw [RingHom.map_mulVec, map_pFin_infGL, Matrix.one_mulVec]; rfl

theorem vInf_infGL_mulVec (v : Fin 2 → Ad F) (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    vInf (((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ v) =
      (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) *ᵥ vInf v := by
  funext i
  simp only [vInf]
  rw [RingHom.map_mulVec, map_pInf_infGL]; rfl

theorem row_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    Phi c (rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F))) =
      archS F (B1 (vInf (rowv g a ξ)) (UpperTheory.V.TR.toL y.val)) * finRow c (rowv g a ξ) := by
  have hv : rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowv g a ξ ᵥ* ((UpperTheory.V.TR.infGL F 2 y : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) := by
    simp only [rowv, Mrow, Units.val_mul, Matrix.vecMul_vecMul, mul_assoc]
  rw [hv, Phi_eq, finRow_congr (pFin_vecMul_infGL _ _), vInf_vecMul_infGL, left_bilinear_apply]
  rfl

theorem col_term (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) =
      archS F (B2 (vInf (colv g a ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) * finCol c (colv g a ξ) := by
  have hinv : (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ =
      UpperTheory.V.TR.infGL F 2 y⁻¹ * Mcol g a := by
    simp only [Mcol, mul_inv_rev, map_inv, mul_assoc]
  have hv : (((Matrix.GeneralLinearGroup.scalar (Fin 2) a * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ =
      ((UpperTheory.V.TR.infGL F 2 y⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ colv g a ξ := by
    rw [hinv, Units.val_mul, ← Matrix.mulVec_mulVec]; rfl
  rw [hv, PhiH_eq, finCol_congr (pFin_infGL_mulVec _ _), vInf_infGL_mulVec, right_bilinear_apply]
  rfl

theorem eisInt_row (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      (∑' ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val))) *
        ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  have h : ∀ ξ : Xi F, kap1 χ c g ((t, u), ξ) * archS F (B1 (w1 g ((t, u), ξ)) (UpperTheory.V.TR.toL y.val)) =
      Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) := by
    intro ξ
    rw [row_term]
    simp only [kap1, w1, av]
    ring
  have e : (∑' ξ : Xi F, Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y) : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)))) =
      thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  ring

theorem eisInt_col (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) {C : ℂ}
    (hC : ∀ h : GA F 2, thetaS (Phi c) h = C * ((absD h)⁻¹ : ℝ) * thetaT (PhiH c) h)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    eisInt χ (Phi c) (g * UpperTheory.V.TR.infGL F 2 y) t u =
      C * ((absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : ℝ) * ((absD (g * UpperTheory.V.TR.infGL F 2 y) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
        ∑' ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) := by
  have h : ∀ ξ : Xi F, kap2 χ c g ((t, u), ξ) * archS F (B2 (w2 g ((t, u), ξ)) (UpperTheory.V.TR.toL (y⁻¹).val)) =
      PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1) *
        (((χ.1 (moduleSection (w0 F) t * (u : Ideles F)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)⁻¹) := by
    intro ξ
    rw [col_term]
    simp only [kap2, w2, av]
    ring
  have e : (∑' ξ : Xi F, PhiH c ((((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (moduleSection (w0 F) t * (u : Ideles F)) * (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ : GA F 2) :
        Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
      thetaT (PhiH c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) *
        (g * UpperTheory.V.TR.infGL F 2 y)) := rfl
  rw [tsum_congr h, tsum_mul_right, e]
  simp only [eisInt]
  rw [hC, absD_scalar_mul]
  have ht : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr t.2.ne'
  push_cast
  field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PoissonSummationHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open NumberField.mixedEmbedding MeasureTheory GroundTheory.Global GroundTheory.Automorphic.Adele2 UpperTheory.V.Sd UpperTheory.V.Published
open scoped _root_.Matrix Classical NumberField.AdeleRing nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable {F : Type} [Field F] [NumberField F]

def nId (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_nId {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((nId c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w :=
  count_finprod_primeIdealUnit_zpow _ (Filter.eventually_cofinite.2 (hc.subset fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact_mod_cast hv)) w

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w differentIdeal_ne_bot]
  rfl

theorem mem_nId_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp (-(c w : ℤ))) ↔ a ∈ idealFiniteAdeles (nId c) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_nId hc]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp ((c w : ℤ) + dd w)) ↔
      a ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_nId hc, count_different, neg_neg]
  rfl

theorem arch_zero [IsTotallyReal F] : arch (0 : UpperTheory.V.TR.Rinf F) 0 = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

def gFin (c : HeightOneSpectrum (𝓞 F) → ℕ) : (Fin 2 → Af F) → ℂ :=
  finiteTensor2 ![cosetIndicator (nId c) 0, cosetIndicator (nId c) 1]

theorem gFin_mem (c : HeightOneSpectrum (𝓞 F) → ℕ) : gFin c ∈ finiteSchwartzBruhat2 F :=
  finiteTensor2_mem fun i => by
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _

variable [IsTotallyReal F]

theorem phi_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1))) :
    Phi c = schwartzBruhatTensor2 φ (gFin c) := by
  funext x
  rw [schwartzBruhatTensor2, hφ, gFin, finiteTensor2_apply, Phi]
  simp only [infPart, finPart, toR_homeomorphMixedSpace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, cosetIndicator_apply, sub_zero]
  congr 1
  have h0 := mem_nId_iff hc (pFin F (x 0))
  have h1 := mem_nId_iff hc (pFin F (x 1) - 1)
  simp only [map_sub, map_one] at h1
  by_cases a : (x 0).2 ∈ idealFiniteAdeles (nId c) <;> by_cases b : (x 1).2 - 1 ∈ idealFiniteAdeles (nId c)
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩, if_pos a, if_pos b, mul_one]
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2)), if_neg b, mul_zero]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]

def cst (c : HeightOneSpectrum (𝓞 F) → ℕ) : ℂ :=
  (-Complex.I) ^ Fintype.card (InfinitePlace F) *
    (((finiteAdeleMeasure F (idealFiniteAdeles (nId c))).toReal : ℝ) : ℂ) ^ 2

theorem cst_ne_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : cst c ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (pow_ne_zero _ ?_)
  rw [Complex.ofReal_ne_zero]
  exact ENNReal.toReal_ne_zero.mpr ⟨(isOpen_idealFiniteAdeles _).measure_ne_zero _ ⟨0, zero_mem _⟩,
    finiteAdeleMeasure_idealFiniteAdeles_ne_top _⟩

theorem fourier_phi {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)))
    (y : Fin 2 → Ad F) :
    adelicFourier2 F (Phi c) y = cst c * PhiH c y := by
  have hφ' : (⇑φ : (Fin 2 → mixedSpace F) → ℂ) = fun u => arch (toR F (u 0)) (toR F (u 1)) := funext hφ
  rw [phi_eq hc φ hφ, adelicFourier2_schwartzBruhatTensor2, schwartzBruhatTensor2,
    mixedFourier2Schwartz_apply, hφ', mixedFourier2_arch, gFin, finiteFourier2_finiteTensor2,
    finiteTensor2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    finiteFourier_cosetIndicator, zero_mul, one_mul, AddChar.map_zero_eq_one, Circle.coe_one,
    infPart, finPart, toR_homeomorphMixedSpace, PhiH, cst]
  have h0 := mem_dual_iff hc (pFin F (y 0))
  have h1 := mem_dual_iff hc (pFin F (y 1))
  rw [show pFin F (y 1) = (y 1).2 from rfl]
  by_cases a : (y 0).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) <;>
    by_cases b : (y 1).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c))
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, Pi.one_apply]
    ring
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring

theorem rowA_zero : rowA (0 : Fin 2 → F) = 0 := by
  funext i
  simp [rowA]

theorem phi_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : Phi c 0 = 0 := by
  simp [Phi, map_zero, arch_zero]

theorem phiH_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : PhiH c 0 = 0 := by
  simp [PhiH, map_zero, arch_zero]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

open UpperTheory.HilbertEisensteinWeightOne UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic in
theorem UpperTheory.HilbertEisensteinWeightOne.poisson_summation_holds : SPois := by
  intro F _ _ _ ω c hyp
  have hc := finite_support_of_cond F ω c hyp.fin hyp.cond
  obtain ⟨φ, hφ⟩ := exists_schwartz_arch F
  have hmem : Phi c ∈ schwartzBruhat2 F := by
    rw [phi_eq hc φ hφ]
    exact schwartzBruhatTensor2_mem φ (gFin_mem c)
  refine ⟨cst c, fun h => ?_⟩
  obtain ⟨S1, S2, E⟩ := poisson_rightTranslate hmem h
  have hF : ∀ ξ : Fin 2 → F, adelicFourier2 F (Phi c) ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ*
      ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))ᵀ) =
      cst c * PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) := by
    intro ξ
    rw [fourier_phi hc φ hφ, Matrix.vecMul_transpose]
    rfl
  simp only [hF, norm_mul] at S2 E
  have hsupp1 : Function.support (fun ξ : Fin 2 → F => Phi c (rowA ξ ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) ⊆
      {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.zero_vecMul, phi_zero]
  have hsupp2 : Function.support (fun ξ : Fin 2 → F =>
      PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ)) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.mulVec_zero, phiH_zero]
  have hC : ‖cst c‖ ≠ 0 := norm_ne_zero_iff.mpr (cst_ne_zero c)
  refine ⟨?_, ?_, ?_⟩
  · exact (S1.subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · exact (((summable_mul_left_iff hC).mp S2).subtype (fun ξ : Fin 2 → F => ξ ≠ 0) : _)
  · rw [thetaS, thetaT]
    rw [show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), Phi c (rowA (ξ : Fin 2 → F) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) from rfl,
      tsum_subtype_eq_of_support_subset hsupp1,
      show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA (ξ : Fin 2 → F)) from rfl,
      tsum_subtype_eq_of_support_subset hsupp2]
    change ∑' ξ : Fin 2 → F, Phi c ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) = _
    rw [E, tsum_mul_left, absD, Complex.ofReal_inv]
    ring
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.QuasiCharConductorLoc
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

section Abstract

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem shell_vanish (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) {n j k : ℤ} (hψ : IsTrivialOn ψ n) {v : Kˣ}
    (hv0 : ord (v : K) = 0) (hv1 : χ v ≠ 1) (hvj : (v : K) - 1 ∈ valBall K j) (hjk : n ≤ j + k) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ) ∂multHaar K = 0 := by
  refine setIntegral_ordShell_eq_zero _ hv0 (a := ((χ v : ℂˣ) : ℂ)) (fun h => hv1 (Units.val_eq_one.mp h)) k
    fun u hu => ?_
  have hmem : ((v : K) - 1) * (u : K) ∈ valBall K n := by
    have h := mul_mem_valBall hvj ((mem_valBall_iff_le_ord u.ne_zero).mpr (le_of_eq (mem_ordShell.mp hu).symm))
    exact valBall_antitone hjk h
  have hψ' : (ψ ((v * u : Kˣ) : K) : ℂ) = (ψ (u : K) : ℂ) := by
    rw [show ((v * u : Kˣ) : K) = (u : K) + ((v : K) - 1) * (u : K) by push_cast; ring,
      AddChar.map_add_eq_mul, hψ _ hmem, mul_one]
  rw [hψ', map_mul, Units.val_mul]
  ring

theorem shell_ne_zero (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hχ : Continuous χ) (hr : ¬ IsUnramifiedChar χ) :
    ∫ u in ordShell K (addCharConductor ψ - quasiCharConductor χ), ((χ u : ℂˣ) : ℂ) * (ψ (u : K) : ℂ)
      ∂multHaar K ≠ 0 := by
  have hχ' : Continuous (χ⁻¹ : Kˣ →* ℂˣ) := continuous_quasiChar_inv hχ
  have hr' : ¬ IsUnramifiedChar χ⁻¹ := by rwa [isUnramifiedChar_inv_iff]
  obtain ⟨a, ha, k, hk⟩ := exists_localEpsilon_eq_monomial (χ := χ⁻¹) (ψ := ψ) hψ hψ1 hχ'
  have h0 := hk 0
  rw [localEpsilon_of_not_isUnramified_eq hr', quasiCharConductor_inv, inv_inv] at h0
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ
  have hadd : ∫ x in (valBall K m : Set K) \ valBall K (m + 1), quasiCharExt χ x * (ψ x : ℂ) ∂haarIntegers K ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at h0
    simp only [neg_zero, Complex.cpow_zero, one_zpow, mul_one] at h0
    exact ha h0.symm
  have hsh := setIntegral_ordShell_eq_haarIntegers (fun x => quasiCharExt χ x * (ψ x : ℂ)) m
  simp only [quasiCharExt_units] at hsh
  rw [hsh]
  refine mul_ne_zero ?_ hadd
  have h1 : (multHaarConst K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨multHaarConst_ne_zero, multHaarConst_ne_top⟩
  have h2 : (residueCard K : ℝ) ^ m ≠ 0 := zpow_ne_zero _ residueCard_pos_real.ne'
  exact_mod_cast mul_ne_zero h1 h2

end Abstract

section Bridge

variable {F : Type} [Field F] [NumberField F]

theorem dd_eq (w : HeightOneSpectrum (𝓞 F)) : dd w = differentExp w := by
  unfold dd differentExp ordI
  rw [FractionalIdeal.count_coe]
  exact _root_.differentIdeal_ne_bot

theorem continuous_loc (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) : Continuous (ω.loc w) :=
  ω.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele w)

theorem mem_U_iff (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : (w.adicCompletion F)ˣ) :
    x ∈ unitFiltrationUnits (w.adicCompletion F) n ↔
      IsUnitAt w x ∧ Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : x ∈ unitFiltrationUnits (w.adicCompletion F) 0 ↔ IsUnitAt w x := by
    rw [mem_unitFiltrationUnits_zero_iff_ord, IsUnitAt, valued_eq_one_iff_ord x.ne_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [h0]
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have hx : (x : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord x.ne_zero]
      exact le_of_eq ((valued_eq_one_iff_ord x.ne_zero).mp h).symm
    have h1 : (1 : w.adicCompletion F) ∈ valBall (w.adicCompletion F) 0 := by
      rw [mem_valBall_iff_le_ord one_ne_zero]
      have := (valued_eq_one_iff_ord (one_ne_zero (α := w.adicCompletion F))).mp (map_one _)
      omega
    have := (mem_valBall_iff_valued).mp (sub_mem hx h1)
    simpa using this
  · rw [mem_unitFiltrationUnits_iff_valBall hn, mem_valBall_iff_valued]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have hU := unitFiltrationUnits_antitone (Nat.zero_le n) ((mem_unitFiltrationUnits_iff_valBall hn).mpr
        ((mem_valBall_iff_valued).mpr h))
      exact h0.mp hU
    · exact fun h => h.2

theorem quasiCharConductor_loc {ω : HChar F} {c : ℕ} {w : HeightOneSpectrum (𝓞 F)} (h : IsCondAt w ω c) :
    quasiCharConductor (ω.loc w) = c := by
  have hset : {n : ℕ | unitFiltrationUnits (w.adicCompletion F) n ≤ (ω.loc w).ker} =
      {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hle x hx hv
      exact MonoidHom.mem_ker.mp (hle ((mem_U_iff w n x).mpr ⟨hx, hv⟩))
    · intro hP x hx
      obtain ⟨h1, h2⟩ := (mem_U_iff w n x).mp hx
      exact MonoidHom.mem_ker.mpr (hP x h1 h2)
  unfold quasiCharConductor
  rw [hset]
  exact h.csInf_eq

end Bridge

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalShellIntegral

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open LocalShellIntegral

theorem local_ramified_holds : LocRam := by
  intro F _ _ _ ω c H w hcw
  set χ := ω.loc w
  set ψ := localAdelicChar F w
  have hcond : quasiCharConductor χ = c w := quasiCharConductor_loc (H.cond w)
  have hn : addCharConductor ψ = -dd w := by rw [addCharConductor_localAdelicChar, dd_eq]
  have hχ : Continuous χ := continuous_loc ω w
  have hr : ¬ IsUnramifiedChar χ := by
    rw [← quasiCharConductor_eq_zero_iff, hcond]
    all_goals first | exact hcw | exact hχ
  refine ⟨fun k hk => ?_, ?_⟩
  · set j : ℕ := (-dd w - k).toNat with hj
    have hjc : j < c w := by
      have : (j : ℤ) < c w := by
        rcases le_or_gt (-dd w - k) 0 with h | h
        · rw [hj, Int.toNat_of_nonpos h]; exact_mod_cast Nat.pos_of_ne_zero hcw
        · rw [hj, Int.toNat_of_nonneg h.le]; omega
      exact_mod_cast this
    have hnot : j ∉ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
      fun hm => absurd ((H.cond w).2 hm) (not_le.mpr hjc)
    simp only [Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨x, hx1, hx2, hx3⟩ := hnot
    have hψt : IsTrivialOn ψ (-dd w) := (isTrivialOn_localAdelicChar_iff w _).2 (by rw [dd_eq])
    refine shell_vanish χ ψ (n := -dd w) (j := j) hψt ((valued_eq_one_iff_ord x.ne_zero).mp hx1) hx3
      ((mem_valBall_iff_valued).mpr hx2) ?_
    have : (-dd w - k) ≤ (j : ℤ) := by rw [hj]; exact Int.self_le_toNat _
    omega
  · have h := shell_ne_zero χ ψ (continuous_localAdelicChar w) (localAdelicChar_ne_one w) hχ hr
    rw [hn, hcond] at h
    have e : -((c w : ℤ) + dd w) = -dd w - (c w : ℤ) := by ring
    rw [e]
    exact h

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

