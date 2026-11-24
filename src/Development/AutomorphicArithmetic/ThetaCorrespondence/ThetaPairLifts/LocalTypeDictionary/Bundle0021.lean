module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelSum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0015
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0016
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnMixed
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanWeilRepresentationContinuous
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ArchCont
open scoped SchwartzMap
theorem continuous_of_intertwining_operator (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)
    (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch l), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T t f₁) = GlobalTheory.RealWeil.rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (t : ℝ) : Continuous (T t) := by
  obtain ⟨hs, -, -⟩ := _root_.GlobalTheory.RealWeil.intertwining_symplectic_and_group_law l A T hT hT0 hI hiso
  rcases isEmpty_or_nonempty l with hl | hl
  · obtain ⟨f0, hf0⟩ := GlobalTheory.MetaplecticScalarDeriv.exists_schwartz_one l
    have hsub : ∀ x : EuclideanSpace ℝ l, x = 0 := fun x => by
      ext i
      exact isEmptyElim i
    have hdec : ∀ f : GlobalTheory.RealWeil.Sch l, f = f 0 • f0 := by
      intro f
      ext x
      rw [hsub x, SchwartzMap.smul_apply, hf0, smul_eq_mul, mul_one]
    have e : ⇑(T t) = fun f => f 0 • T t f0 := by
      funext f
      conv_lhs => rw [hdec f]
      exact map_smul _ _ _
    rw [e]
    exact (GlobalTheory.MetaplecticScalarDeriv.continuous_eval l 0).smul continuous_const
  · obtain ⟨G, _, _, _, pr, om, omS, ⟨-, hsurj, -⟩, -, h3, h4, -, -⟩ := hP.realMetaplecticRepresentation l
    obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
    obtain ⟨g, hg⟩ := hsurj N
    have hmat : ∀ w, A t ((pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
      intro w
      have e : pr g * pr g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have e' : (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr g⁻¹ : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
        congrArg (fun x : Matrix.symplecticGroup l ℝ => (x : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
      rw [← hN, ← hg, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
    have hU1 : ∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
        ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h₁) =
          GlobalTheory.RealWeil.rhoFun w ⇑((T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h) := by
      intro w h h₁ hh
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hI t _ _ _ (GlobalTheory.MetaplecticScalarDeriv.intertwine_fun l _ (om g⁻¹) (omS g⁻¹) (h3 _) (h4 _) w h h₁ hh), hmat]
    have hU2 : ∀ h : GlobalTheory.RealWeil.Sch l,
        ∫⁻ x, ‖(T t ∘ₗ (omS g⁻¹ : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)) h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
      intro h
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [lintegral_of_integral _ _ (hiso t _), GlobalTheory.MetaplecticScalarDeriv.lintegral_iso l (om g⁻¹) (omS g⁻¹) (h4 _)]
    obtain ⟨a, -, ha⟩ := _root_.GlobalTheory.T.real_weil_representation_schur_scalar hP l _ hU1 hU2
    have e : ⇑(T t) = fun f => a • omS g f := by
      funext f
      have h1 := ha (omS g f)
      have e2 : omS g⁻¹ (omS g f) = f := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, e2] at h1
      exact h1
    rw [e]
    exact (omS g).continuous.const_smul a
end GlobalTheory.ArchCont
namespace GlobalTheory.ArchCont
open scoped SchwartzMap RealInnerProductSpace
theorem continuous_schrodinger_model_action (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (P : V → V → ℝ) (hp : GlobalTheory.ArchUniq.IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hTadd : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = GlobalTheory.ArchUniq.schrF P v ⇑f →
      ⇑(T t f₁) = GlobalTheory.ArchUniq.schrF P (A t v) ⇑(T t f))
    (hTl2 : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) (t : ℝ) : Continuous (T t) := by
  obtain ⟨C, φ, hp', hq⟩ := GlobalTheory.ArchUniq.SchrTransport.coords P hp _ rfl
  have hS := GlobalTheory.ArchUniq.SchrTransport.schr_coords P C φ hp' hq
  let toE : 𝓢(V, ℂ) →L[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →L[ℂ] 𝓢(V, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V)) :=
    fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := GlobalTheory.ArchUniq.SchrTransport.haar_coords μ C
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch (Fin (Module.finrank ℝ V))), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T' t f₁) = GlobalTheory.RealWeil.rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = GlobalTheory.ArchUniq.schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have hc := _root_.GlobalTheory.ArchCont.continuous_of_intertwining_operator hP (Fin (Module.finrank ℝ V)) A' T' c2 c3 c4 c5 t
  have e : ⇑(T t) = fun f => toV (T' t (toE f)) := by
    funext f
    simp only [hT', hVE]
  rw [e]
  exact toV.continuous.comp (hc.comp toE.continuous)
end GlobalTheory.ArchCont
open scoped Classical in
theorem GlobalTheory.ArchCont.continuous_weil_action_on_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) → ∀ t, Continuous (T t) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ T hT hadd h0 t
  obtain ⟨A, -, hA⟩ := _root_.GlobalTheory.ArchFam.schr_equiv M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := MeasureTheory.Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    _root_.GlobalTheory.ArchIsom.acts_norm_sq_eq M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  exact _root_.GlobalTheory.ArchCont.continuous_schrodinger_model_action hP _ μ _ (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T
    hadd h0 hA hiso t
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_weil_representation_continuous : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) → ∀ t, Continuous (T t) := by
  first | exact @_root_.GlobalTheory.ArchCont.continuous_weil_action_on_line | exact _root_.GlobalTheory.ArchCont.continuous_weil_action_on_line | (intros; apply _root_.GlobalTheory.ArchCont.continuous_weil_action_on_line <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomDegreeMatchRealQuotient
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
namespace GlobalTheory.BotMatch
theorem real_quotient_complement_minor : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D A.rank WW.rank n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  intro h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨hnt, n₀, σ, i1, i2, i3, i4⟩ :=
    _root_.GlobalTheory.T.real_quotient_bottom_invariants_equiv h1 h2 h3 h4 D ψ θ θ' hθ A A' WW FA FA' FW a b had hA hA' hW hex Pr q q' hq hq' hm
  obtain ⟨α, β, ht, -⟩ := hex
  obtain ⟨p, r, -, h5, h6⟩ := ht.sig
  exact GlobalTheory.T.realQuotient_minor_eq_const_smul_complementMinor D had n₀ Pr q q' σ (by omega) (by omega) hnt hq hq' i1 i2 i3 i4
end GlobalTheory.BotMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_degree_match_real_quotient : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    ∃ ρ : ℂ, ρ ≠ 0 ∧ ∀ (n : D.what₂.Tau → ℕ) (T : Tup D A.rank WW.rank n), ∃ ε : ℤˣ,
      q (GlobalTheory.BotFormula.minorF rfl rfl T) = (ρ * ((ε : ℤ) : ℂ)) • q' (GlobalTheory.BotFormula.minorF rfl rfl (GlobalTheory.BotMatch.complTup D had T)) := by
  first | exact @_root_.GlobalTheory.BotMatch.real_quotient_complement_minor | exact _root_.GlobalTheory.BotMatch.real_quotient_complement_minor | (intros; apply _root_.GlobalTheory.BotMatch.real_quotient_complement_minor <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
open scoped ContDiff ComplexOrder
namespace GlobalTheory.ColLiftAut
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {Φ : WO S T → ℂ}
theorem thetaLift_isAutomorphicFunction (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hΦ : IsThetaFunO ψ S T Φ)
    (hS : ∀ τ, (gramAt D S τ).PosDef) {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) {φ : GA D S → ℂ} (hφ : IsAutFun S φ) :
    IsAutFun T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν := by
  refine ⟨fun γ hγ h => ?_, ?_, lift_continuous hW hΦ hS hν h𝓕 hφ⟩
  · simp only [kernel_left hW hΦ _ hγ]
  · obtain ⟨U, hU, hk⟩ := _root_.GlobalTheory.T.twist_weil_level_eq_conductor ψ S T χS χT om Φ hP hW hΦ
    refine ⟨U, hU, fun k hkU hkf h => ?_⟩
    simp only [kernel_right, hk k hkU hkf]
theorem thetaLift_isSmoothAutomorphicFunction (θ : InfFam D) (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ)
    (hΦ : IsThetaFunO ψ S T Φ) (hS : ∀ τ, (gramAt D S τ).PosDef) (hT : ∀ τ, (gramAt D T τ).PosDef)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν)
    {φ : GA D S → ℂ} (hφ : IsAutFunSm θ S φ) :
    IsAutFunSm θ T fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν :=
  { toIsAutFun := _root_.GlobalTheory.ColLiftAut.thetaLift_isAutomorphicFunction hP hW hΦ hS hν h𝓕 hφ.toIsAutFun
    smooth := _root_.GlobalTheory.T.twist_deformation_lift_smooth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    zfin := _root_.GlobalTheory.T.twist_definite_lift_finite_adeles ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ
    growth := _root_.GlobalTheory.T.twist_lift_moderate_growth ψ θ S T χS χT om Φ φ ν 𝓕 hP hW hθ hΦ hS hT hν h𝓕 hφ }
end GlobalTheory.ColLiftAut
namespace GlobalTheory.ColLiftAut
theorem columnLift_isSmoothAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ φ hφ _
  have hW : IsWeilDatumO R.ψ (G.Xp j).V (G.Xp (j + 1)).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) (G.col t j).ω :=
    (hG.arrows.col t j hj).weil
  have hT : ∀ τ, (gramAt D (G.Xp (j + 1)).V τ).PosDef := posDef_of_nodeIs (hG.spaces.X j (by omega)) rfl
  have hSm : (∀ τ, (gramAt D (G.Xp j).V τ).PosDef) ∧ (G.measX j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.Xp j).V) (G.measX j).fd (G.measX j).ν := by
    cases j with
    | zero =>
      exact ⟨posDef_of_nodeIs (hG.spaces.P D.R.m le_rfl) (by simp), ((hG.meas.P D.R.m le_rfl).1 rfl).1.1, ((hG.meas.P D.R.m le_rfl).1 rfl).2⟩
    | succ j' =>
      exact ⟨posDef_of_nodeIs (hG.spaces.X j' (by omega)) rfl, ((hG.meas.X j' (by omega)).1 trivial).1.1, ((hG.meas.X j' (by omega)).1 trivial).2⟩
  exact _root_.GlobalTheory.ColLiftAut.thetaLift_isSmoothAutomorphicFunction R.θ hPr hW hRB.inf hΦ hSm.1 hT hSm.2.1 hSm.2.2 hφ.1
end GlobalTheory.ColLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnLift_isAutomorphicFunction : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → IsAutFunSm R.θ (G.Xp (j + 1)).V (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  first | exact @_root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | exact _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction | (intros; apply _root_.GlobalTheory.ColLiftAut.columnLift_isSmoothAutomorphicFunction <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormApproximationSinglePlace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal
namespace GlobalTheory.KFinCuspApprox
theorem kFinite_cusp_approx_at_one_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  intro hP D θ hθ N φ hφ τ a δ hδ
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 a
  have hr := rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc
  have hη : 0 < δ / ((C : ℝ) + 1) := div_pos hδ (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.KAvgApprox.one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) φ hr d _ hη
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hav := GlobalTheory.KAvgApprox.avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e hec φ hr
  set ψ : GA D N.V → ℂ := φ - avgN θ N τ e φ with hψ
  have hψr : RapidDecSm θ N.V ψ := by
    have := hr.add (hav.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψc : IsCuspFun N.V ψ := by
    have h2 := _root_.GlobalTheory.T.kFinite_cuspForm_average_approx θ hθ hP N τ e hec φ hA hc
    have := GlobalTheory.MultMem.isCuspFun_add hr.toIsAutFun (hav.smul (-1)).toIsAutFun hc (GlobalTheory.MultMem.isCuspFun_smul (-1) h2)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := by
    intro k hk hk' x
    simp only [hψ, Pi.sub_apply, hlev k hk hk' x]
    congr 1
    show (∫ k', e k' * φ (x * k * _) ∂_) = ∫ k', e k' * φ (x * _) ∂_
    congr 1; funext k'
    rw [mul_assoc, ← Formalism.IndefR.Eqv.Act.comm_inf_fin (Formalism.IndefR.Eqv.Act.atTau_mem θ τ _) hk', ← mul_assoc, hlev k hk hk']
  refine ⟨e, hec, he, fun g => ?_⟩
  have h1 := hC ψ hψr.toIsAutFun hψlev hψr.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hψr) hψc
  have h2 : decaySize N.V a ψ ≤ ENNReal.ofReal δ := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (δ / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ a) ≤ ENNReal.ofReal δ :=
    (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ a)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at h3
  simpa [hψ] using h3
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_approximation_single_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | exact _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | (intros; apply _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsLiftOfTypeAutomorphism
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory
theorem type_automorphism_lifts_to_theta : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) :=
  _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic
end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_type_automorphism : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @_root_.GlobalTheory.type_automorphism_lifts_to_theta | exact _root_.GlobalTheory.type_automorphism_lifts_to_theta | (intros; apply _root_.GlobalTheory.type_automorphism_lifts_to_theta <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GlThetaLiftIsClosed
section
section
namespace UpperTheory.Lit.Mix
theorem gl_thetaLift_isClosed : _root_.GlobalTheory.ThetaLiftGL.ThetaLiftGeneralLinearStatement := _root_.UpperTheory.Lit.HoweDuality.thetaLift_gl_of_zelevinsky_classification polynomialRing
end UpperTheory.Lit.Mix
end
end

