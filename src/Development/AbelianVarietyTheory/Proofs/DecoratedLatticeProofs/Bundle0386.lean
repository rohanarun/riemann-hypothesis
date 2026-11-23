module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntMOfMulRight
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LabelAtRealPlaceEqEmbeddingOverReflexField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.LabAtRealPlace

theorem sigmaOf_sqrt (D : D7) (τ : D.what₂.Tau) :
    D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD = D.host.sqrtMinusD := by
  have h1 : D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) ∈
      D.R.Psi := by
    rw [show D.host.galE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG)) = (D.eTau τ).1 from D.host.gal.apply_symm_apply _]
    exact (D.eTau τ).2
  exact (D.host.galE_mem_Psi_iff _).1 h1

theorem labE_sqrt (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (τ ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = tauE D ρ D.host.sqrtMinusD := by
  have hm : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have e1 : Formalism.IndefR.Links.labE σ τ D.host.sqrtMinusD = σ (D.embE D.host.sqrtMinusD) := by
    show σ (D.embE (D.host.sigmaOf ((D.eTau τ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  have e2 : Formalism.IndefR.Conj.labE D.what₂.embLL ρ D.host.sqrtMinusD = D.what₂.embLL (D.embE D.host.sqrtMinusD) := by
    show D.what₂.embLL (D.embE (D.host.sigmaOf ((D.eTau ρ).1 : D.R.GG) D.host.sqrtMinusD)) = _
    rw [sigmaOf_sqrt]
  rw [e1, h.2 _ hm, ← e2, Formalism.IndefR.Conj.labE_base]

theorem labE_lab (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (h : IsEmbOverK D σ s) (ρ : D.what₂.Tau) :
    Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := by
  have hex : ∃ τ, Formalism.IndefR.Links.labE σ τ = tauE D ρ ∨
      Formalism.IndefR.Links.labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    obtain ⟨B, hB⟩ := Formalism.IndefR.Conj.labExists σ
    have h' := hB (B.perm.symm ρ)
    rw [Formalism.IndefR.Conj.ArchLab.emb, Equiv.apply_symm_apply] at h'
    refine ⟨B.perm.symm ρ, ?_⟩
    split_ifs at h'
    exacts [Or.inl h', Or.inr h']
  rw [Formalism.IndefR.Links.lab, dite_eq_left hex]
  refine hex.choose_spec.resolve_right fun h' => ?_
  have h2 := labE_sqrt D σ s h hex.choose ρ
  rw [h', RingHom.comp_apply] at h2
  obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 h2
  have h3 : (tauE D ρ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
  rw [hx] at h3
  have h4 : x ^ 2 = -(D.host.d : ℝ) := by exact_mod_cast h3
  have h5 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  nlinarith [sq_nonneg x]

theorem main : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), IsEmbOverK D σ s → ∀ ρ, Formalism.IndefR.Links.labE σ (Formalism.IndefR.Links.lab σ ρ) = tauE D ρ := fun D σ s h ρ => labE_lab D σ s h ρ

end GlobalTheory.LabAtRealPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDoubleLiftAdditive
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSmallPf

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

def ker {A S X : HSp D} (oma : Om A S) (omX : Om S X) (C : WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ℂ :=
  omX (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => C u v) 0) 0

theorem biLift_eq {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ C h₂ = ∫ h₁ in vS.𝓕, (∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) ∂vS.μ := rfl

section

variable {A S X : HSp D} {χA χS χS' χX : (AE D)ˣ →* Circle} {oma : Om A S} {omX : Om S X}

theorem ker_sum {n : ℕ} (C : Fin n → WO A S → WO S X → ℂ) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX (∑ i, C i) h₀ h₁ h₂ = ∑ i, ker oma omX (C i) h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (∑ i, C i) u v) 0) = ∑ i, fun v => oma (h₀, h₁) (fun u => C i u v) 0 := by
    funext v
    have e : (fun u => (∑ i, C i) u v) = ∑ i, fun u => C i u v := by
      funext u; simp only [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]; simp only [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]; simp only [Finset.sum_apply]

theorem ker_cont (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) :
    Continuous fun x : GA D A × GA D S × GA D X => ker oma omX C x.1 x.2.1 x.2.2 := by
  have := (hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).2.2.2
  exact this.comp (by fun_prop : Continuous fun x : GA D A × GA D S × GA D X =>
    ((x.1, x.2.1), (x.2.1, x.2.2), ((0 : WO A S), (0 : WO S X))))

theorem ker_left (hwa : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C)
    {γ : GA D A} (hγ : γ ∈ GQ A) (h₀ : GA D A) (h₁ : GA D S) (h₂ : GA D X) :
    ker oma omX C (γ * h₀) h₁ h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (γ * h₀, h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((γ * h₀, h₁) : GA D A × GA D S) = (γ, 1) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut γ hγ 1 (one_mem _) _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  rw [e1]

theorem ker_mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {γ : GA D S} (hγ : γ ∈ GQ S) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ (γ * h₁) h₂ = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have e1 : (fun v => oma (h₀, γ * h₁) (fun u => C u v) 0) = fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : ((h₀, γ * h₁) : GA D A × GA D S) = (1, γ) * (h₀, h₁) := by simp
    rw [e, map_mul, Module.End.mul_apply,
      hwa.om_aut 1 (one_mem _) γ hγ _ (hwa.om_pres _ _ (GlobalTheory.FrComb.slice_left hC v))]
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((γ * h₁, h₂) : GA D S × GA D X) = (γ, 1) * (h₁, h₂) := by simp
  rw [e1, e, map_mul, Module.End.mul_apply, hwX.om_aut γ hγ 1 (one_mem _) _ (hwX.om_pres _ _ hth)]

theorem ker_right (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) {δ : GA D X} (hδ : δ ∈ GQ X) (h₀ : GA D A) (h₁ : GA D S)
    (h₂ : GA D X) : ker oma omX C h₀ h₁ (δ * h₂) = ker oma omX C h₀ h₁ h₂ := by
  unfold ker
  have hth : IsThetaFunO ψ S X (fun v => oma (h₀, h₁) (fun u => C u v) 0) :=
    GlobalTheory.FrComb.slice_right ((hB ψ A S X χA χS χS' χX oma omX hwa hwX C hC).1 (h₀, h₁)) 0
  have e : ((h₁, δ * h₂) : GA D S × GA D X) = (1, δ) * (h₁, h₂) := by simp
  rw [e, map_mul, Module.End.mul_apply, hwX.om_aut 1 (one_mem _) δ hδ _ (hwX.om_pres _ _ hth)]

theorem inner (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (vA : Vol A) {φ : GA D A → ℂ}
    (hφ : IsContAut A φ) :
    (∀ h₁ h₂, IntegrableOn (fun h₀ => φ h₀ * ker oma omX C h₀ h₁ h₂) vA.𝓕 vA.μ) ∧
      Continuous fun p : GA D S × GA D X => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ p.1 p.2 ∂vA.μ := by
  have hc : Continuous (Function.uncurry fun (g : GA D A) (p : GA D S × GA D X) => φ g * ker oma omX C g p.1 p.2) := by
    show Continuous fun q : GA D A × (GA D S × GA D X) => φ q.1 * ker oma omX C q.1 q.2.1 q.2.2
    exact (hφ.2.comp continuous_fst).mul ((ker_cont hB hwa hwX hC).comp
      (by fun_prop : Continuous fun q : GA D A × (GA D S × GA D X) => (q.1, q.2.1, q.2.2)))
  have H := _root_.GlobalTheory.CocompactParam.continuous_integral_param D A hA vA (GA D S × GA D X) (fun g p => φ g * ker oma omX C g p.1 p.2) hc
    (fun γ hγ g p => by rw [hφ.1 γ hγ g, ker_left hwa hC hγ])
  exact ⟨fun h₁ h₂ => H.1 (h₁, h₂), H.2.1⟩

theorem mid (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S)
    {φ : GA D A → ℂ} (hφ : IsContAut A φ) :
    (∀ h₂, IntegrableOn (fun h₁ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ) vS.𝓕 vS.μ) ∧
      Continuous fun h₂ => biLift oma omX vA vS φ C h₂ := by
  have H := _root_.GlobalTheory.CocompactParam.continuous_integral_param D S hS vS (GA D X) (fun h₁ h₂ => ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX C h₀ h₁ h₂ ∂vA.μ)
    (inner hB hwa hwX hC hA vA hφ).2 (fun γ hγ g p => by simp only [ker_mid hB hwa hwX hC hγ])
  exact ⟨H.1, H.2.1⟩

theorem outer (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    {C : WO A S → WO S X → ℂ} (hC : IsBiTheta ψ A S X C) (hA : CoCpt A) (hS : CoCpt S) {T L'' : HSp D} (hT : CoCpt T)
    (vA : Vol A) (vS : Vol S) (vT : Vol T) (o'' : OrthDec X T L'') {φ : GA D A → ℂ} (hφ : IsContAut A φ)
    {F : GA D T → ℂ} (hF : IsContAut T F) :
    IntegrableOn (fun h' => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1))) vT.𝓕 vT.μ := by
  have hc := (mid hB hwa hwX hC hA hS vA vS hφ).2
  have hc' : Continuous fun h' : GA D T => biLift oma omX vA vS φ C (o''.emb (h', 1)) :=
    hc.comp (o''.continuous_emb.comp (by fun_prop : Continuous fun h' : GA D T => ((h', 1) : GA D T × GA D L'')))
  refine (_root_.GlobalTheory.CocompactParam.continuous_integral_param D T hT vT Unit (fun h' _ => F h' * biLift oma omX vA vS φ C (o''.emb (h', 1)))
    ((hF.2.mul hc').comp continuous_fst) (fun γ hγ g _ => ?_)).1 ()
  have e : ((γ * g, 1) : GA D T × GA D L'') = (γ, 1) * (g, 1) := by simp
  have hδ : o''.emb (γ, 1) ∈ GQ X := o''.emb_mem_GQ hγ (one_mem _)
  rw [hF.1 γ hγ g, e, map_mul, biLift_eq, biLift_eq]
  simp only [ker_right hB hwa hwX hC hδ]

theorem biLift_sum (hB : BiAct D) (hwa : IsWeilDatumO ψ A S χA χS oma) (hwX : IsWeilDatumO ψ S X χS' χX omX)
    (hA : CoCpt A) (hS : CoCpt S) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : IsContAut A φ) {n : ℕ}
    (C : Fin n → WO A S → WO S X → ℂ) (hC : ∀ i, IsBiTheta ψ A S X (C i)) (h₂ : GA D X) :
    biLift oma omX vA vS φ (∑ i, C i) h₂ = ∑ i, biLift oma omX vA vS φ (C i) h₂ := by
  have e1 : ∀ h₁, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (∑ i, C i) h₀ h₁ h₂ ∂vA.μ =
      ∑ i, ∫ h₀ in vA.𝓕, φ h₀ * ker oma omX (C i) h₀ h₁ h₂ ∂vA.μ := by
    intro h₁
    simp only [ker_sum, Finset.mul_sum]
    exact integral_finsetSum _ fun i _ => (inner hB hwa hwX (hC i) hA vA hφ).1 h₁ h₂
  rw [biLift_eq]
  simp only [e1]
  rw [integral_finsetSum _ fun i _ => (mid hB hwa hwX (hC i) hA hS vA vS hφ).1 h₂]
  rfl

end

theorem seeSmall : ∀ D : D7, SeeSmall D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ hA hS hT χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hTw hz''
    vA vS vT N Ξ Φ₂ hΞΦ φ F hφ hF
  have hB : BiAct D := _root_.GlobalTheory.SeeSaw.biAct_all D
  have hSL := _root_.GlobalTheory.SeeLastPf.seeLast D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX
    hTw hz''
  have hC : ∀ i, IsBiTheta ψ A S X (lastBi o o'' τ (Ξ i) (Φ₂ i)) := fun i =>
    GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction D ψ h₁.std V₀ A L S X T L'' o o'' τ hτ (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2
  have e0 : (o.resS S).symm (0, 0) = 0 := by rw [← Prod.zero_eq_mk, map_zero]
  have hpt : ∀ i h', biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) (o''.emb (h', 1)) =
      ∫ h in vS.𝓕, omT (h, h') (Φ₂ i) 0 * liftA o om₁ vA φ (Ξ i) h 0 ∂vS.μ := by
    intro i h'
    rw [biLift_eq]
    congr 1
    funext h
    simp only [liftA, e0]
    rw [← integral_const_mul]
    congr 1
    funext h₀
    have key : oma (h₀, h) (fun u' => omX (h, o''.emb (h', 1)) (lastBi o o'' τ (Ξ i) (Φ₂ i) u') 0) 0 =
        omT (h, h') (Φ₂ i) 0 * om₁ (o.emb (h₀, 1), h) (Ξ i) 0 :=
      ((hSL (Ξ i) (Φ₂ i) (hΞΦ i).1 (hΞΦ i).2).2 h₀ h h').symm
    have hk := (hB ψ A S X χA χS χS' (χT * χz⁻¹) oma omX ha hX _ (hC i)).2.2.1 (h₀, h) (h, o''.emb (h', 1)) 0 0
    simp only [ker]
    rw [hk, key]
    ring
  have hsum : ∀ h₂, biLift oma omX vA vS φ (∑ i, lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ =
      ∑ i, biLift oma omX vA vS φ (lastBi o o'' τ (Ξ i) (Φ₂ i)) h₂ := fun h₂ =>
    biLift_sum hB ha hX hA hS vA vS hφ (fun i => lastBi o o'' τ (Ξ i) (Φ₂ i)) hC h₂
  simp only [hsum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => outer hB ha hX (hC i) hA hS hT vA vS vT o'' hφ hF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smallPair, hpt]

end GlobalTheory.SeeSmallPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepDatumTransportBadPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.Transport.LastTw

section TopQ

open _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep GlobalTheory.TopStep.Model

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_shiftQ (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {a b : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i))
    (hb : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ * (b i - a i))) :
    locTop Ch sel mu cst m2 P y b = locTop Ch sel mu cst m2 P y a := by
  have hq := qOf_ne_zero (P := P.1)
  unfold locTop
  congr 1
  generalize atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y = η
  unfold ftY
  rw [if_neg hP, if_neg hP]
  split_ifs with h
  · congr 1
    have ev : ∀ z : Sp X.E (R.N (m2 + 1)), η z = ∑ j, z j * η (Pi.single j 1) := fun z => by
      conv_lhs => rw [pi_eq_sum_univ' z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    have hd : IntAt P.1 ((epsSg : X.E) * η (b - a)) := by
      rw [ev]
      refine he.mul (intAt_sum _ fun j _ => ?_)
      have := (hb j).mul (h j)
      convert this using 1
      rw [Pi.sub_apply, mul_mul_mul_comm, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * η a)) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (h j)))
      convert this using 1
      rw [hD', ev, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one, ← mul_add, ← map_add (f := _), add_sub_cancel] at this
    exact this
  · rfl

theorem locTop_congQ (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D P)
    (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m))
    (hyz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ (cst.M + 1))⁻¹ * (y (Pi.single s 1) l - z (Pi.single s 1) l)))
    {a : Sp X.E (R.N (m2 + 1))} (ha : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * a i)) :
    locTop Ch sel mu cst m2 P y a = locTop Ch sel mu cst m2 P z a := by
  have hq := qOf_ne_zero (P := P.1)
  choose t ht ez using fun s l => (⟨_, hyz s l, by field_simp; ring⟩ : ∃ t, IntAt P.1 t ∧
    y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t)
  have ez' : ∀ s l, z (Pi.single s 1) l = y (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * (0 - t s l) :=
    fun s l => by rw [ez]; ring
  have ht' : ∀ s l, IntAt P.1 (0 - t s l) := fun s l => intAt_sub intAt_zero (ht s l)
  have tr : ∀ (y z : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (t : Fin (R.N (m2 + 1)) → Fin (R.N R.m) → X.E),
      (∀ s l, IntAt P.1 (t s l)) → (∀ s l, y (Pi.single s 1) l = z (Pi.single s 1) l + (qOf P.1 : X.E) ^ (cst.M + 1) * t s l) →
      SuppQ (m2 := m2) P.1 cst.M z → SuppQ (m2 := m2) P.1 cst.M y := fun y z t ht ez hz s => by
    refine ⟨fun i => ?_, ?_⟩
    · rw [ez]
      exact ((hz s).1 i).add ((intAt_pow (intAt_nat _) _).mul (ht _ _))
    · rw [ez, mul_add]
      refine (hz s).2.add ?_
      rw [← mul_assoc, ← pow_add]
      exact (intAt_pow (intAt_nat _) _).mul (ht _ _)
  by_cases hz : SuppQ (m2 := m2) P.1 cst.M z
  swap
  · have h1 : locTop Ch sel mu cst m2 P z a = 0 := by
      by_contra h
      exact hz (suppQ_of_ne hm hP h)
    have h2 : locTop Ch sel mu cst m2 P y a = 0 := by
      by_contra h
      exact hz (tr z y _ ht' ez' (suppQ_of_ne hm hP h))
    rw [h1, h2]
  have hy := tr y z t ht ez hz
  unfold locTop
  refine congrArg₂ (· * ·) ?_ ?_
  · have he : ∀ p p', CongQ P.1
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p')
        (LocE.entB (qOf P.1) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) 0 0
          (prXp X.E R ∘ₗ z ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) p p') := fun p p' => by
      rw [entB_topQ hm, entB_topQ hm]
      split_ifs with h
      · refine ⟨(hy _).1 _, (hz _).1 _, ?_⟩
        show IntAt _ ((y _ _ - z _ _) / _)
        rw [ez]
        convert (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) cst.M).mul (ht ⟨p', h.2⟩ (Br.iC (N_m_succ R) ⟨p, h.1⟩)) using 1
        rw [pow_succ]
        field_simp
        ring
      · exact congQ_zero
    unfold PhiTop
    rw [if_neg hP]
    unfold LocE.PhiQ
    refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ ?_ rfl
    · simp only [(he _ _).1, (he _ _).2.1, (he _ _).div_iff]
    · exact unitV_det_congr _ fun s s' => he s.1 s'.1
  · unfold ftY
    have ev : ∀ w : HomE X.E (R.N (m2 + 1)) (R.N R.m), (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ w) a =
        ∑ j, a j * w (Pi.single j 1) (Br.iL (N_m_succ R)) := fun w => by
      rw [LinearMap.comp_apply, atNL_last, apply_eq_sum]
    have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
    rw [if_neg hP, if_neg hP, if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hy _).2),
      if_pos (fun i => by rw [LinearMap.comp_apply, atNL_last]; exact (hz _).2), ev, ev]
    congr 1
    have hd : IntAt P.1 ((epsSg : X.E) * ∑ j, ((qOf P.1 : X.E) ^ cst.M * a j) * ((qOf P.1 : X.E) * t j (Br.iL (N_m_succ R)))) :=
      he.mul (intAt_sum _ fun j _ => (ha j).mul ((intAt_nat _).mul (ht _ _)))
    have hz' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * ((epsSg : X.E) * ∑ j, a j * z (Pi.single j 1) (Br.iL (N_m_succ R)))) := by
      obtain ⟨D, hD'⟩ := Nat.exists_eq_add_of_le hD
      have := (intAt_pow (intAt_nat (P := P.1) (qOf P.1)) D).mul
        (he.mul (intAt_sum Finset.univ fun j _ => (ha j).mul (hz j).2))
      convert this using 1
      rw [hD', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := hc.psi_add P _ _ hz' ((intAt_pow (intAt_nat (P := P.1) (qOf P.1)) _).mul hd)
    rw [hc.psi_int P _ hd, mul_one] at this
    rw [← this]
    congr 1
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ez]
    ring

theorem rep_sub_intQ {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m) (p q : PtAt R sel mu cst u j) (e : cosetIn q = cosetIn p)
    {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (i : Fin (R.N j)) :
    IntAt P.1 (((qOf P.1 : X.E) ^ cst.M)⁻¹ *
      ((frsF sel mu p.1.1 P).symm (repY p.1.2) i - (frsF sel mu q.1.1 P).symm (repY q.1.2) i)) := by
  have h1 : (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
    ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [← e] at h1
  obtain ⟨z, hz1, h2⟩ := h1
  rw [if_neg hP] at h2
  have h3 := q.repY_mem h
  obtain ⟨y, -, hY⟩ := q.mem_ybSet h
  have h4 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 hz1) P
  have h5 := (mem_locLat _ _ _ _).1 ((Set.ext_iff.1 hY _).1 h3) P
  simp only [if_neg hP, zpow_natCast] at h4 h5
  have h6 : ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (z - repY q.1.2) ∈ q.1.1.deco.1.at P.1 := by
    have := sub_mem h4 h5
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this
  rw [← (frsF sel mu q.1.1 P).apply_symm_apply (_ • (z - _)), frsF_mem, map_smul, map_sub] at h6
  have h7 := add_mem h2 h6
  rw [← smul_add, sub_add_sub_cancel] at h7
  simpa using mem_stdAt.1 h7 i

end TopQ

theorem locTop_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (ok : I.Ok) (u : B.Word) (a : I.ι) (n : ℕ) (h : n + 1 + 1 = B.R.m) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (n + 1 + 1))
    (k y : TC.GA B (B.R.N (n + 1))) (k' y' : TC.GA B (B.R.N (n + 1 + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (n + 1 + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q = cosetIn p →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N (n + 1)) (B.R.N (n + 1 + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
                   (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                   ((Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P).symm (Formalism.L2.Col.repY p.1.2)) =
        GlobalTheory.TopStep.locTop I.Ch I.sel (I.tup a) (I.cst a) n P
          (castSp B.fields.E (congrArg B.R.N h) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P).symm (Formalism.L2.Col.repY q.1.2)) := by
  intro B X I l ok u a n h P p q p' q' k y k' y' hp hN hp' hN' hq hq' e
  have hc := (ok.idx_ok a).cst_ok
  have hqpos : 0 < Formalism.L2.Col.qOf P.1 := Nat.pos_of_ne_zero fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hsq := Formalism.L2.Col.ciQ_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hP
    refine ⟨Formalism.L2.Col.qOf P.1, hqpos, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hv : Valued.v ((Formalism.L2.Col.qOf P.1 * c : ℕ) : P.1.adicCompletion B.fields.E) < 1 := by
      rw [← map_natCast (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)), valued_algebraMap,
        ← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E), HeightOneSpectrum.valuation_lt_one_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ GlobalTheory.TopStep.qOf_mem
    have H := GlobalTheory.Transport.Last.read_cong hp hN hp' hN' hq hq' ⟨P.1, hP⟩ x x₀ (fun r s => by
      refine lt_of_eq_of_lt (congrArg Valued.v ?_) ((hx r s).trans_lt hv)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [GlobalTheory.Transport.Last.locM, GlobalTheory.Transport.Last.ratM, Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub,
        map_sum, map_mul, adAt_inclE])
    have f1 : ∀ {j : ℕ} (r : Formalism.L2.Col.ChPt (R := B.R) I.sel (I.tup a) u j),
        Formalism.L2.Col.frsF I.sel (I.tup a) r P = r.deco.1.liftFr ⟨P.1, hP⟩ := fun r => dif_pos hP
    rw [← f1, ← f1, ← f1, ← f1] at H
    have hq1 := GlobalTheory.TopStep.repY_int q.1.1 (q.mem_ybSet h) hP
    rw [GlobalTheory.Transport.Last.locTop_shift hc hP _ hq1 (GlobalTheory.Transport.Last.rep_sub_int h p q e hP)]
    exact GlobalTheory.Transport.Last.locTop_of_cong h.symm hc hP hsq _ _ _ hq1 H
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hD := (ok.idx_ok a).depthQ P hP
    have hq0 := GlobalTheory.TopStep.qOf_ne_zero (P := P.1)
    refine ⟨Formalism.L2.Col.qOf P.1 ^ ((I.cst a).M + 1), pow_pos hqpos _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have H := _root_.GlobalTheory.Transport.TwistRead.qread I u a (n + 1) P hQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I ok l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hqv := GlobalTheory.TopStep.Model.repY_intQ q.1.1 (q.mem_ybSet h) hP
    rw [locTop_shiftQ hc hP hD _ hqv (rep_sub_intQ h p q e hP)]
    have key : ∀ s r, Formalism.L2.Col.IntAt P.1 (((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1))⁻¹ *
        (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ (Pi.single s 1) r -
          Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x (Pi.single s 1) r)) := by
      intro s r
      rw [GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
      have H1 := H r s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, Nat.cast_mul, Nat.cast_pow, map_mul] at H1
      have hc1 : P.1.valuation B.fields.E (c : B.fields.E) ≤ 1 := by
        rw [← map_natCast (algebraMap (𝓞 B.fields.E) B.fields.E)]
        exact P.1.valuation_le_one _
      have hpos : P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq0)
      rw [map_mul, map_inv₀, ← neg_sub, Valuation.map_neg]
      calc _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * P.1.valuation B.fields.E (c : B.fields.E)) :=
            by gcongr
        _ ≤ (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)))⁻¹ *
            (P.1.valuation B.fields.E ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ ((I.cst a).M + 1)) * 1) :=
            by gcongr
        _ = 1 := by rw [mul_one, inv_mul_cancel₀ hpos]
    refine locTop_congQ h.symm hc hP hD _ _ ?_ hqv
    intro s l
    rw [LinearMap.comp_apply, LinearMap.comp_apply, castSp_apply, castSp_apply]
    exact key s _

end GlobalTheory.Transport.LastTw
end
end

