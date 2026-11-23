module

public import Mathlib
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfSurj
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0001
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ContinuousFinId
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0002
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004
public import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.RamifiedMultiplicityOneOfBernstein
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitFin
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.UpperProjectionInverseTransposeRightInverse
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0004
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ValuationIntegersEqCompletion
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
section
open ValuativeRel Matrix Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BernBridge.Split

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitLoc.Unr

def NarrowBernstein : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ)
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible

def IndIrredLt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (α β : kˣ →* ℂˣ), (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
    IsSmoothChar α → IsSmoothChar β → a' < a →
    ∀ N : Submodule ℂ (GL (Fin (a + a')) k → ℂ), N ≤ indSp a a' α β → (∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N) →
      N = ⊥ ∨ N = indSp a a' α β

theorem indIrredLt_of (NB : NarrowBernstein) : IndIrredLt := by
  intro k _ _ _ _ a a' α β hα hβ sα sβ hlt N hN hr
  by_cases h0 : N = ⊥
  · exact Or.inl h0
  refine Or.inr (le_antisymm hN ?_)
  obtain ⟨F, hFN, hF0⟩ := (Submodule.ne_bot_iff N).1 h0
  have hI : (parInd (two (stdE a a')) (rhoD a a' α β)).IsIrreducible :=
    NB k a a' α β sα sβ hα hβ (Or.inl hlt.ne')
  let S : Subrepresentation (parInd (two (stdE a a')) (rhoD a a' α β)) :=
    ⟨N.comap (toFn a a' α β), fun g f hf => hr g _ hf⟩
  rcases hI.eq_bot_or_eq_top S with e | e
  · obtain ⟨f, rfl⟩ := exists_toFn (hN hFN)
    have hf : f ∈ S.toSubmodule := hFN
    rw [e] at hf
    have hf0 : f = 0 := hf
    exact absurd (by rw [hf0, map_zero]) hF0
  · intro G hG
    obtain ⟨f, rfl⟩ := exists_toFn hG
    have hf : f ∈ S.toSubmodule := by rw [e]; trivial
    exact hf

section Onto
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem onto_of_irredLt (hI : IndIrredLt) {a a' : ℕ} {α β : kˣ →* ℂˣ} (hα : ∀ x, ‖(α x : ℂ)‖ = 1)
    (hβ : ∀ x, ‖(β x : ℂ)‖ = 1) (sα : IsSmoothChar α) (sβ : IsSmoothChar β) (hlt : a' < a)
    {X : Type} [TopologicalSpace X] (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hlin : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁)
    (hin : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ))
    (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) : ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hlin 0 (SB X).zero_mem 0 (SB X).zero_mem 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + (1 : ℂ) • Φ₁, (SB X).add_mem hΦ ((SB X).smul_mem _ hΦ₁), by rw [hlin _ hΦ _ hΦ₁, one_smul]⟩
      zero_mem' := ⟨0, (SB X).zero_mem, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨0 + c • Φ, (SB X).add_mem (SB X).zero_mem ((SB X).smul_mem _ hΦ), by
          rw [hlin _ (SB X).zero_mem _ hΦ, h0, zero_add]⟩ }
  have hle : N ≤ indSp a a' α β := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact hin Φ hΦ
  have hst : ∀ h₁, ∀ F ∈ N, rtr h₁ F ∈ N := by
    rintro h₁ _ ⟨Φ, hΦ, rfl⟩
    exact heq Φ hΦ h₁
  rcases hI k a a' α β hα hβ sα sβ hlt N hle hst with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    have hm : p Φ ∈ N := ⟨Φ, hΦ, rfl⟩
    rw [h] at hm
    exact absurd ((Submodule.mem_bot ℂ).1 hm) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Onto

theorem unrMaps_of_lt (hI : IndIrredLt) : UnrMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν hS hα hβ
  have hν := isUnram_nu hS hα hβ
  have hp1 := p_lin hS hν
  have hp2 := p'_lin hS hν
  have hp3 := p_mem hS hν hβ
  have hp4 := p'_mem hS hν hα
  have hu := p_unit hS hν hβ
  have hu' := p'_unit hS hν hα
  have sα : IsSmoothChar α := isSmoothChar_of_isUnram hα
  have sβ : IsSmoothChar β := isSmoothChar_of_isUnram hβ
  refine ⟨hp1, hp2, hp3, hp4, p_inv hS hν, p'_inv hS hν, fun Φ _ h₁ => p_equiv Φ h₁, fun Ψ _ h₁ => p'_equiv Ψ h₁,
    ?_, ?_, hu, hu'⟩
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp1 hp3
      (fun Φ hΦ h₁ => ⟨_, omA_mem_SB ν β 1 h₁ hΦ, p_equiv Φ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu 1 (one_mem _)] using congrFun h0 1
  · refine onto_of_irredLt hI hS.unitα hS.unitβ sα sβ hS.lt _ hp2 hp4
      (fun Ψ hΨ h₁ => ⟨_, omB_mem_SB ν α 1 h₁ hΨ, p'_equiv Ψ h₁⟩) ⟨_, indicator_int_mem_SB, fun h0 => ?_⟩
    simpa [hu' 1 (one_mem _)] using congrFun h0 1

section Global

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThK PositivityTheory.ThK.SplitAsm

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

local instance measFv {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem finSplit_of_lt (hU : UnrMaps) (hI : IndIrredLt) (hIw : IndIwasawa) (hD : Dict) (hAU : ActsUniq) (hC : ChrFacts)
    (hZ : IntEq) : FinSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, ⟨τ⟩⟩
  obtain ⟨hα, hβ, hν, hcond, -, hunr⟩ := hC F E B X a a' v τ hT.chars
  obtain ⟨hαu, hβu⟩ := hunr hv
  have hS : HidaSetting a a' (unifAt v) (chrW X.α τ) (chrW X.β τ) (chrW X.ν τ) :=
    ⟨GlobalTheory.SplitFlip.exists_isUnif.choose_spec, hα, hβ, hν, hT.geo.lt, hT.geo.even, hcond⟩
  obtain ⟨hlin, hlin', hmem, hmem', hinv, hinv', heq, heq', hon, hon', hsph, hsph'⟩ :=
    hU (Fv F v) a a' _ _ _ _ hS hαu hβu
  obtain ⟨b, b', c, ι, ι', gl, gl', hl, hW, hB, -, hvac, hvac', hRg, hRh, hRg', hRh', hhl⟩ :=
    hD F E σ B a a' G X om om' hT v τ
  have hind : ∀ m n : ℕ, (intInd v : Matrix (Fin m) (Fin n) (Fv F v) → ℂ) =
      Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[Fv F v]} 1 := by
    intro m n
    unfold intInd
    congr 1
    ext Y
    simp only [Set.mem_setOf_eq, hZ F v]
  have h1 : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph h hh
  have h1' : ∀ h ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin (a + a')), pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) h = 1 :=
    fun h hh => by rw [hind]; exact hsph' h hh
  have hiSB : intInd v ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) := by
    rw [← hvac]; exact hW.bij.mapsTo (hT.geo.hM.vac v).1
  have hnz : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) ≠ 0 := fun h0 => by
    have := h1 1 (one_mem _)
    rw [h0] at this
    exact zero_ne_one this
  obtain ⟨p, p', hp, hp', hon1, hon1', hinv1, hinv1', heq1, hnt, hirr1⟩ := core hAU v G om om' _ _ _ (indSp a a' _ _)
    (pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ)) (pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ))
    (fun Φ h Φ₁ h₁ => hlin Φ h Φ₁ h₁) (fun Φ h Φ₁ h₁ => hlin' Φ h Φ₁ h₁)
    (fun Φ h => hmem Φ h) (fun Φ h => hmem' Φ h) (fun Φ h => hinv Φ h)
    (fun Φ h => hinv' Φ h) (fun Φ h => heq Φ h) (fun Φ h => heq' Φ h)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon y hy; exact ⟨Φ, h, r⟩)
    (fun y hy => by obtain ⟨Φ, h, r⟩ := hon' y hy; exact ⟨Φ, h, r⟩) ⟨_, hiSB, hnz⟩
    (fun N hN hst => hI (Fv F v) a a' _ _ hα hβ (isSmoothChar_of_isUnram hαu) (isSmoothChar_of_isUnram hβu)
      hT.geo.lt N hN hst) ι ι' hW.bij hB.bij gl gl' hl hRg hRh hRg' hRh' hhl
  refine ⟨oneMaps v _ p p', ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [oneMaps_p]; exact hon1
  · rw [oneMaps_p']; exact hon1'
  · rw [oneMaps_p]; exact hinv1
  · rw [oneMaps_p']; exact hinv1'
  · rw [oneMaps_p, oneMaps_p']; exact heq1
  · exact hnt
  · rw [oneMaps_p]; exact hirr1
  · intro _
    rw [oneMaps_p, oneMaps_p']
    have e1 := hp _ (hT.geo.hM.vac v).1
    have e2 := hp' _ (hT.geo.hM'.vac v).1
    rw [hvac] at e1
    rw [hvac'] at e2
    have hm1 := hmem _ hiSB
    have hm2 : pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) ∈ indSp a a' (chrW X.α τ) (chrW X.β τ) := by
      rw [← e2]; exact (p' (G.M'.vac v)).2
    have hd : pUnr a a' (unifAt v) (chrW X.ν τ) (chrW X.β τ) (intInd v) -
        pUnr' a a' (unifAt v) (chrW X.ν τ) (chrW X.α τ) (intInd v) = 0 :=
      hIw (Fv F v) a a' _ _ _ (Submodule.sub_mem _ hm1 hm2) fun h hh => by
        simp only [Pi.sub_apply, h1 h hh, h1' h hh, sub_self]
    refine ⟨Subtype.ext ?_, fun h0 => hnz ?_⟩
    · erw [e1, e2]; exact sub_eq_zero.1 hd
    · have := congrArg Subtype.val h0
      erw [e1] at this
      exact this
  · intro _ hvT; exact absurd hvT hv

theorem finSplit_of_narrow : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ →
    (a ≠ b ∨ χ₁ ≠ χ₂) → (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible) → PositivityTheory.ThK.FinSplit :=
  fun NB => finSplit_of_lt (unrMaps_of_lt (indIrredLt_of NB)) (indIrredLt_of NB) induced_vanish_of_vanish_on_integral split_place_dictionary
    PositivityTheory.KCo.action_uniqueness split_character_facts valuation_integers_eq_completion

end Global

end GlobalTheory.CompanionTheory.BernBridge.Split
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBaseChangeSq
section
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MdBase

section

open NumberField IsDedekindDomain MeasureTheory _root_.Topology Filter GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange MeasureTheory.Measure
open scoped ENNReal NNReal NumberField.AdeleRing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem map_smul_pi (n : ℕ) (a : IdeleGroup K) :
    (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      (Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹) ^ n •
        Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
  have hsm : Measurable fun y : 𝔸[K] ↦ a • y := (Homeomorph.smul a).continuous.measurable
  have hmeas : Measurable fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i :=
    Measurable.of_eval fun i ↦ hsm.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ with hcdef
  have hmap : (adeleMeasure K).map (fun y ↦ a • y) = c • adeleMeasure K := by
    rw [map_smul_adeleMeasure]
    rfl
  have h1 : (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      Measure.pi fun _ : Fin n ↦ c • adeleMeasure K := by
    refine (pi_eq fun s hs ↦ ?_).symm
    rw [map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i ↦ (fun y ↦ a • y) ⁻¹' s i := by
      ext x
      simp
    rw [hpre, pi_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← hmap, map_apply hsm (hs i)]
  have h2 : (Measure.pi fun _ : Fin n ↦ c • adeleMeasure K) =
      c ^ n • Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
    refine pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.coe_pow]
  rw [h1, h2]

theorem ideleModule_ideleEmbedding (x : IdeleGroup K) :
    (IdeleGroup.ideleModule L (ideleEmbedding K L x) : ℝ) =
      (IdeleGroup.ideleModule K x : ℝ) ^ Module.finrank K L := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  set n := Module.finrank K L with hn
  let e : 𝔸[L] ≃ₗ[𝔸[K]] (Fin n → 𝔸[K]) := (adeleBasis (Module.finBasis K L)).equivFun
  have hce : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hcs : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : 𝔸[L] ≃ₜ (Fin n → 𝔸[K]) :=
    { toEquiv := e.toEquiv, continuous_toFun := hce, continuous_invFun := hcs }
  set μ : Measure (Fin n → 𝔸[K]) := Measure.pi fun _ ↦ adeleMeasure K with hμ
  set ν : Measure 𝔸[L] := μ.map e.symm with hν
  have hms : Measurable e.symm := hcs.measurable
  haveI : ν.IsAddHaarMeasure :=
    isAddHaarMeasure_map _ e.symm.toLinearMap.toAddMonoidHom hcs e.symm.surjective
      h.symm.isClosedEmbedding.tendsto_cocompact
  set X := ideleEmbedding K L x with hX
  have hcomp : (fun y : 𝔸[L] ↦ X • y) ∘ e.symm = e.symm ∘ (fun v i ↦ x • v i) := by
    funext v
    have hv : (fun i ↦ x • v i) = (x : 𝔸[K]) • v := by
      funext i
      simp [Units.smul_def]
    simp only [Function.comp_apply]
    rw [hv, map_smul, Units.smul_def]
    change (X : 𝔸[L]) * e.symm v = (x : 𝔸[K]) • e.symm v
    rw [Algebra.smul_def (x : 𝔸[K]), algebraMap_adeleRing]
    rfl
  have hsmL : Measurable fun y : 𝔸[L] ↦ X • y := (Homeomorph.smul X).continuous.measurable
  have hsmK : Measurable fun v : Fin n → 𝔸[K] ↦ fun i ↦ x • v i :=
    Measurable.of_eval fun i ↦
      (Homeomorph.smul x).continuous.measurable.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K x : ℝ))⁻¹ with hcdef
  have h1 : ν.map (fun y ↦ X • y) = c ^ n • ν := by
    rw [hν, Measure.map_map hsmL hms, hcomp, ← Measure.map_map hms hsmK, hμ, map_smul_pi,
      Measure.map_smul]
    exact hms.aemeasurable
  have hc := isAddLeftInvariant_eq_smul ν (adeleMeasure L)
  set C := ν.addHaarScalarFactor (adeleMeasure L)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hc, ENNReal.coe_eq_zero.1 h0, zero_smul]
    exact (NeZero.ne ν) this
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : 𝔸[L])
  have hpos : adeleMeasure L S ≠ 0 := (measure_pos_of_mem_nhds _ hS0).ne'
  have htop : adeleMeasure L S ≠ ⊤ := hS.measure_lt_top.ne
  rw [hc, Measure.map_smul, map_smul_adeleMeasure] at h1
  swap
  · exact hsmL.aemeasurable
  have h2 := congrArg (fun m : Measure 𝔸[L] ↦ m S) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  rw [mul_left_comm] at h2
  have hne : (C : ℝ≥0∞) * adeleMeasure L S ≠ 0 := mul_ne_zero hC0 hpos
  have hnt : (C : ℝ≥0∞) * adeleMeasure L S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top htop
  have h3 := (ENNReal.mul_left_inj hne hnt).1 h2
  have hK0 : (0 : ℝ) ≤ (IdeleGroup.ideleModule K x : ℝ)⁻¹ :=
    inv_nonneg.2 (IdeleGroup.ideleModule K x).2.le
  have h4 : ((c ^ n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (((IdeleGroup.ideleModule K x : ℝ))⁻¹ ^ n) := by
    rw [ENNReal.ofReal_pow hK0, ENNReal.coe_pow]
    rfl
  rw [h4] at h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule L X).2.le)
    (pow_nonneg hK0 n)).1 h3
  rw [inv_pow] at h5
  exact inv_inj.1 h5

end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology Filter
  PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem ideleModule_ideleEquiv_ofF : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  intro F E _ _ _ _ _ σ hcm a
  have he : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a) = ideleEmbedding F E a :=
    Units.ext (GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (a : AF F))
  rw [he, ideleModule_ideleEmbedding, hcm.2.2.1]
  rfl

end

end GlobalTheory.CompanionTheory.SW.MdBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBoundedOnCompact
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.IdeleModBdd

theorem ideleModule_bounded_on_compact : ∀ (K : Type) [Field K] [NumberField K] (C : Set (AdeleRing (𝓞 K) K)), IsCompact C → ∃ R : ℝ, ∀ a : IdeleGroup K, (a : AdeleRing (𝓞 K) K) ∈ C → (IdeleGroup.ideleModule K a : ℝ) ≤ R := by
  intro K _ _ C hC
  let U : Finset (HeightOneSpectrum (𝓞 K)) → Set (AdeleRing (𝓞 K) K) := fun S =>
    {x | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers K}
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ S)).preimage continuous_snd
  have hcov : C ⊆ ⋃ S, U S := by
    intro x _
    have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ x.2 v ∈ v.adicCompletionIntegers K}.Finite :=
      Filter.eventually_cofinite.1 x.2.2
    exact Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv => by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)⟩
  have hdir : Directed (· ⊆ ·) U := fun S T =>
    ⟨S ∪ T, fun x hx v hv => hx v fun h => hv (Finset.mem_union_left _ h),
      fun x hx v hv => hx v fun h => hv (Finset.mem_union_right _ h)⟩
  obtain ⟨S, hS⟩ := hC.elim_directed_cover U hUo hcov hdir
  have hfinB : ∀ v : HeightOneSpectrum (𝓞 K), ∃ B : ℝ, ∀ x ∈ C, ‖x.2 v‖ ≤ B := fun v => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.2 v‖ :=
      continuous_norm.comp ((RestrictedProduct.continuous_eval v).comp continuous_snd)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  have hinfB : ∀ w : InfinitePlace K, ∃ B : ℝ, ∀ x ∈ C, ‖x.1 w‖ ≤ B := fun w => by
    have hc : Continuous fun x : AdeleRing (𝓞 K) K => ‖x.1 w‖ :=
      continuous_norm.comp ((continuous_apply w).comp continuous_fst)
    obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose Bf hBf using hfinB
  choose Bi hBi using hinfB
  refine ⟨(∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult) * ∏ v ∈ S, max (Bf v) 1, ?_⟩
  intro a ha
  rw [IdeleGroup.ideleModule_eq]
  have h1 : ∏ w : InfinitePlace K, ‖(a : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult ≤
      ∏ w : InfinitePlace K, max (Bi w) 0 ^ w.mult :=
    Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) ((hBi w _ ha).trans (le_max_left _ _)) _
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(a : AdeleRing (𝓞 K) K).2 v‖ ≤
      ∏ v ∈ S, max (Bf v) 1 := by
    have hfs := IdeleGroup.finite_mulSupport_norm a
    have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        ‖(a : AdeleRing (𝓞 K) K).2 v‖) ⊆ ((hfs.toFinset ∪ S : Finset _) : Set _) := fun v hv => by
      simp only [Finset.coe_union, Set.Finite.coe_toFinset]
      exact Or.inl hv
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    calc ∏ v ∈ hfs.toFinset ∪ S, ‖(a : AdeleRing (𝓞 K) K).2 v‖
        ≤ ∏ v ∈ hfs.toFinset ∪ S, (if v ∈ S then max (Bf v) 1 else 1) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => ?_
          split_ifs with hv
          · exact (hBf v _ ha).trans (le_max_left _ _)
          · exact (Valued.toNormedField.norm_le_one_iff).2
              ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 (hS ha v hv))
      _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
          (Finset.prod_subset Finset.subset_union_right fun v _ hv => if_neg hv).symm
      _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
  exact mul_le_mul h1 h2 (IdeleGroup.finiteModule_pos a).le
    (Finset.prod_nonneg fun _ _ => by positivity)

end GlobalTheory.CompanionTheory.IdeleModBdd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteAdeleHaarScalingTotallyReal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarUnit

theorem norm_inv_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (n : (InfiniteAdeleRing F)ˣ) :
    ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ =
      ((∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ : ℝ≥0) := by
  have hmult : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (hF.isReal w)]
  have hw : ∀ w : InfinitePlace F,
      ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ =
        ‖(n : InfiniteAdeleRing F) w‖⁻¹ := fun w => by
    have h1 : ((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w *
        (n : InfiniteAdeleRing F) w = 1 := congrFun n.inv_mul w
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  rw [InfiniteAdeleRing.norm_def]
  simp only [hmult, pow_one, hw, NNReal.coe_inv, NNReal.coe_prod, coe_nnnorm]
  rw [Finset.prod_inv_distrib]

section Borel

attribute [local instance 100000] GroundTheory.Global.measurableSpace_infiniteAdeleRing

theorem infinite_adele_haar_scaling_by_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    {m : MeasurableSpace (InfiniteAdeleRing F)} (hm : @BorelSpace _ _ m)
    (li : Measure (InfiniteAdeleRing F)) (hli : li.IsAddHaarMeasure)
    (n : (InfiniteAdeleRing F)ˣ) :
    li.map (fun t => (n : InfiniteAdeleRing F) * t) =
      (∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ • li := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul li (infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, map_mul_left_infiniteAdeleMeasure, smul_comm, norm_inv_unit F hF n,
    ENNReal.ofReal_coe_nnreal]
  · rfl
  · letI := hm
    exact (continuous_const_mul (n : InfiniteAdeleRing F)).measurable.aemeasurable

end Borel

theorem map_mul_unit : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ n : (Ainf F)ˣ,
      li.map (fun t => (n : Ainf F) * t) =
        (∏ w : InfinitePlace F, ‖(n : Ainf F) w‖₊)⁻¹ • li := by
  intro F _ _ hF li hli n
  exact infinite_adele_haar_scaling_by_unit F hF (m := measAinf) ⟨rfl⟩ li hli n

end GlobalTheory.CompanionTheory.SW.HaarUnit

end
end

