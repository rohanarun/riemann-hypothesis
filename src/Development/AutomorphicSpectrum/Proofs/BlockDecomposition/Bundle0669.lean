module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0035
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionHaar
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem integrable_map_prod_of_compact_of_lt_top {A B W : Type} [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [T2Space A] [TopologicalSpace B] [MeasurableSpace B]
    [OpensMeasurableSpace B] [T2Space B] [TopologicalSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [IsFiniteMeasureOnCompacts μ]
    (f : A × B → W) (hf : Measurable f) (φ : W → ℝ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (C₁ : Set A) (C₂ : Set B)
    (h₁ : IsCompact C₁) (h₂ : IsCompact C₂) (hν : ν C₂ < ⊤)
    (hs : ∀ᵐ y ∂μ, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ C₁ ∧ X ∈ C₂) (k : ℝ≥0) :
    Integrable φ (k • (μ.prod ν).map f) ∧
      ∫ v, φ v ∂(k • (μ.prod ν).map f) = (k : ℝ) * ∫ y, ∫ X, φ (f (y, X)) ∂ν ∂μ := by
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hc
  have hmeas : Measurable φ := hφ.measurable
  have hg : Measurable (φ ∘ f) := hmeas.comp hf
  have hPm : MeasurableSet (C₁ ×ˢ C₂) := h₁.measurableSet.prod h₂.measurableSet
  have hPfin : (μ.prod ν) (C₁ ×ˢ C₂) < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top h₁.measure_lt_top hν
  have hae : ∀ᵐ p ∂(μ.prod ν), ‖(φ ∘ f) p‖ ≤ (C₁ ×ˢ C₂).indicator (fun _ => |Bd|) p := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs
    filter_upwards [h] with p hp
    by_cases h0 : φ (f p) = 0
    · simp only [Function.comp, h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
    · have hmem : p ∈ C₁ ×ˢ C₂ := hp p.2 h0
      rw [Set.indicator_of_mem hmem]
      exact (hBd _).trans (le_abs_self _)
  have hbound : Integrable ((C₁ ×ˢ C₂).indicator (fun _ => |Bd|)) (μ.prod ν) :=
    (integrable_indicator_iff hPm).2 (integrableOn_const hPfin.ne)
  have hI : Integrable (φ ∘ f) (μ.prod ν) := hbound.mono' hg.aestronglyMeasurable hae
  have hI2 : Integrable φ ((μ.prod ν).map f) :=
    (integrable_map_measure hmeas.aestronglyMeasurable hf.aemeasurable).2 hI
  refine ⟨hI2.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, integral_map hf.aemeasurable hmeas.aestronglyMeasurable,
    integral_prod (fun p => φ (f p)) hI]
  simp [NNReal.smul_def]


set_option maxHeartbeats 1000000 in
theorem integrable_fibSF_and_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm hD φ hφ hcs hfree S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := hD.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨hKr, hKlc, hKsc, hKt2, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hD.hCM R
  have := hKr
  have := hKlc
  have := hKsc
  have := hKt2
  have hB1 : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := hBor 1 (M + 1)
  have hB2 : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hBor n M
  have hB3 : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hBor (n + 1) (M + 1)
  have hJ₁ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J hD.hJ t hD.ht
  obtain ⟨hTG, -, hHsc, hHt2, hHB, hact⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hD.hCM (M + 1) (blockOne (algebraMap F E t) J) hJ₁ R
  have := hTG
  have := hHsc
  have := hHt2
  have := hHB
  obtain ⟨hcont, hone, hmul, -⟩ := hact (n + 1)
  have k1 := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ hD.hCM (M + 1) 1 (blockOne (algebraMap F E t) J) hJ₁ R hD.hR d b lam
    hD.hlam m₁ hD.hm₁
  obtain ⟨-, hlf₁, -, -, -, hgram⟩ := k1
  obtain ⟨hsf₂, -, hbd₂, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ hD.hCM M n J hD.hJ R hD.hR d b lam hD.hlam m' hD.hm'
  set α : Rˣ := a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) with hα
  set c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) with hc
  set S' := schur R σ t a S with hS'
  set μ₁ := m₁ (hermScal R σ (algebraMap F R t)) with hμ₁
  set u : R ⊗[F] E := (α : R) ⊗ₜ[F] (1 : E) with hu
  set u' : R ⊗[F] E := ((α⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) with hu'
  have huu : u * u' = 1 := by
    simp [hu, hu', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
  have := hlf₁ (hermScal R σ (algebraMap F R t))
  have := hsf₂ S'
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec u c p.2)
  have hfm : Measurable f :=
    hcont.measurable.comp ((hD.hs.comp measurable_fst).prodMk
      ((continuous_vec u c).measurable.comp measurable_snd))
  have hfib : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = (κ₁ α * cm α ^ n) • (μ₁.prod (m' S')).map f := by
    unfold fibSF
    rw [Set.indicator_of_mem hS]
  set C := tsupport φ with hC
  have hCc : IsCompact C := hcs
  let e₁ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → Fin 1 → Fin (M + 1) → R ⊗[F] E :=
    fun Z _ i => Z 0 i * u'
  have he₁ : Continuous e₁ := by
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    exact (continuous_apply_apply (0 : Fin (n + 1)) i).mul continuous_const
  have hC₁ : IsCompact (e₁ '' C) := hCc.image he₁
  obtain ⟨C', hC'c, hC'⟩ := hD.hcpt (e₁ '' C) hC₁
  let e₂ : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) →
      Fin (n + 1) → Fin (M + 1) → R ⊗[F] E :=
    fun q => actW R σ (blockOne (algebraMap F E t) J) q.1⁻¹ q.2
  have he₂ : Continuous e₂ := hcont.comp ((continuous_fst.inv).prodMk continuous_snd)
  have hQc : IsCompact (e₂ '' (C' ×ˢ C)) := (hC'c.prod hCc).image he₂
  have hQf : ∀ Y ∈ e₂ '' (C' ×ˢ C), LinearIndependent (R ⊗[F] E) Y := by
    rintro _ ⟨q, ⟨-, hq⟩, rfl⟩
    exact (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff F E R σ (M + 1) (n + 1) (blockOne (algebraMap F E t) J) q.1⁻¹ q.2).2
      (hfree hq)
  obtain ⟨C₂, hC₂c, hC₂f, hC₂⟩ := GlobalTheory.T.compact_free_set_projects_compact (R ⊗[F] E) M n _ hQc hQf
  have hν : m' S' C₂ < ⊤ := by
    obtain ⟨k, hk⟩ := hbd₂ C₂ {S'} hC₂c hC₂f isCompact_singleton
    exact (hk S' rfl).trans_lt ENNReal.coe_lt_top
  have hsupp : ∀ᵐ y ∂μ₁, ∀ X, φ (f (y, X)) ≠ 0 → y ∈ e₁ '' C ∧ X ∈ C₂ := by
    filter_upwards [hgram (hermScal R σ (algebraMap F R t))] with y hy X hne
    have hZ : f (y, X) ∈ C := subset_tsupport _ hne
    have hy0 : e₁ (f (y, X)) = y := by
      have h1 := hD.hsec y hy
      funext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      have h2 : (f (y, X)) 0 = u • y 0 := by
        conv_rhs => rw [← h1]
        simp only [f, actW, actTup, vec_zero, Matrix.mulVec_smul]
      simp only [e₁, h2, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm u, mul_assoc, huu, mul_one]
    have hy1 : y ∈ e₁ '' C := ⟨_, hZ, hy0⟩
    have hsy : s y ∈ C' := hC' y hy1 hy
    have hv : e₂ (s y, f (y, X)) = vec u c X := by
      simp only [e₂, f]
      rw [← hmul, inv_mul_cancel, hone]
    exact ⟨hy1, hC₂ u c X ⟨(s y, f (y, X)), ⟨hsy, hZ⟩, hv⟩⟩
  rw [hfib]
  exact integrable_map_prod_of_compact_of_lt_top μ₁ (m' S') f hfm φ hφ hcs _ _ hC₁ hC₂c hν hsupp _

end GlobalTheory.CompanionTheory.SW.StageF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSigmaFinite
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ContTwoF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory _root_.Topology
open GlobalTheory.CompanionTheory.SW.PiLocalization₂.ContTwo
open scoped TensorProduct ENNReal NNReal Matrix

theorem cont_double_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc hfree
  haveI iTR : IsTopologicalRing R := D.hR.1
  haveI iLC : LocallyCompactSpace R := D.hR.2.1
  haveI iSC : SecondCountableTopology R := D.hR.2.2.1
  haveI iT2 : T2Space R := D.hR.2.2.2.1
  have hval : IsOpenEmbedding (Units.val : Rˣ → R) := D.hR.2.2.2.2.2.2.1
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI := kTR
  haveI := kLC
  haveI := kSC
  haveI := kT2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨eLC, eSC, eT2, eB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R n
  haveI := eLC
  haveI := eSC
  haveI := eT2
  haveI := eB
  obtain ⟨gTG, gLC, gSC, gT2, gB, hactall⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  haveI := gTG
  haveI := gLC
  haveI := gSC
  haveI := gT2
  haveI := gB
  obtain ⟨hact, hact1, hactm, -⟩ := hactall (n + 1)
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ D.hCM R d b lam D.hlam
  haveI := hW n M
  haveI := hH n
  obtain ⟨-, -, hbd', -⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -, -, -, hgram₁⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := kB n M
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := kB 1 (M + 1)
  have hUo : IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ D.hCM R D.hR n M

  have hCt : ∀ L : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact L →
      ∃ C : Set (Fin n → Fin M → R ⊗[F] E), IsCompact C ∧
        C ⊆ {X | LinearIndependent (R ⊗[F] E) X} ∧ ∀ h ∈ L, ∀ A c X,
        φ (actW R σ _ h (vec A c X)) ≠ 0 → X ∈ C := by
    intro L hL
    have hQc : IsCompact ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)) := by
      refine (hL.prod hφc).image ?_
      exact hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    have hQf : ∀ Y ∈ ((fun p : HA R σ (blockOne (algebraMap F E t) J) ×
        (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => actW R σ _ p.1⁻¹ p.2) '' (L ×ˢ tsupport φ)),
        LinearIndependent (R ⊗[F] E) Y := by
      rintro _ ⟨⟨h, z⟩, ⟨-, hz⟩, rfl⟩
      exact (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff F E R σ (M + 1) (n + 1) _ h⁻¹ z).2 (hfree hz)
    obtain ⟨C, hC, hCf, hCv⟩ := GlobalTheory.T.compact_free_set_projects_compact (R ⊗[F] E) M n _ hQc hQf
    refine ⟨C, hC, hCf, fun h hh A c X hne => hCv A c X ?_⟩
    refine ⟨(h, actW R σ _ h (vec A c X)), ⟨hh, subset_tsupport _ hne⟩, ?_⟩
    simp only
    rw [← hactm, inv_mul_cancel, hact1]
  have cT := continuous_tmul_one (F := F) (E := E) R

  let G : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) × HermR R σ n → ℝ :=
    fun q => ∫ X, φ (actW R σ _ q.1.1 (vec (q.1.2.1 ⊗ₜ[F] (1 : E)) q.1.2.2 X)) ∂(m' q.2)
  have hG : ∀ q, ContinuousAt G q := by
    intro q
    obtain ⟨L, hLc, hLn⟩ := exists_compact_mem_nhds q.1.1
    obtain ⟨C, hC, hCf, hCv⟩ := hCt L hLc
    have hWo : IsOpen (interior L ×ˢ (Set.univ : Set (R × (Fin n → R ⊗[F] E)))) :=
      isOpen_interior.prod isOpen_univ
    have hcΦ : Continuous (fun p : (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E)) ×
        (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ _ p.1.1 (vec (p.1.2.1 ⊗ₜ[F] (1 : E)) p.1.2.2 p.2))) := by
      refine hφ.comp (hact.comp ((continuous_fst.comp continuous_fst).prodMk ?_))
      exact continuous_vec.comp ((cT.comp (continuous_fst.comp (continuous_snd.comp continuous_fst))).prodMk
        ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd))
    have hj := _root_.GlobalTheory.CompanionTheory.SW.FibreJointOpen.continuousOn_fibre_integral_of_subset (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) _ (coordW R b lam n M)
      (coordHerm R σ b lam n) (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} hUo
      Set.univ isOpen_univ m' D.hm'
      (HA R σ (blockOne (algebraMap F E t) J) × R × (Fin n → R ⊗[F] E))
      (interior L ×ˢ Set.univ)
      (fun p X => φ (actW R σ _ p.1 (vec (p.2.1 ⊗ₜ[F] (1 : E)) p.2.2 X))) hcΦ.continuousOn hWo C hC hCf
      (by
        intro p hp v hv
        by_contra hne
        exact hv (hCv p.1 (interior_subset hp.1) _ _ _ hne))
    have hmem : ((interior L ×ˢ Set.univ) ×ˢ (Set.univ : Set (HermR R σ n))) ∈ 𝓝 q :=
      (hWo.prod isOpen_univ).mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hLn, trivial⟩, trivial⟩
    exact hj.continuousAt hmem
  rintro ⟨α₀, c₀, S₀⟩ ⟨hα₀, -, -⟩
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨N, hNn, hNs, hNc⟩ := local_compact_nhds (hval.isOpen_range.mem_nhds hα₀)
  have hUc : IsCompact ((Units.val : Rˣ → R) ⁻¹' N) := by
    rw [hval.isInducing.isCompact_iff, Set.image_preimage_eq_of_subset hNs]
    exact hNc
  have hNi : IsCompact ((Units.val : Rˣ → R) '' ((fun u : Rˣ => u⁻¹) '' ((Units.val : Rˣ → R) ⁻¹' N))) :=
    (hUc.image continuous_inv).image Units.continuous_val
  obtain ⟨Dc, hDc, hDn⟩ := exists_compact_mem_nhds S₀
  let C₁ : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E) :=
    (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      scl (p.1 ⊗ₜ[F] (1 : E)) (fun _ : Fin 1 => p.2 0)) ''
        (((Units.val : Rˣ → R) '' ((fun u : Rˣ => u⁻¹) '' ((Units.val : Rˣ → R) ⁻¹' N))) ×ˢ tsupport φ)
  have hC₁c : IsCompact C₁ := by
    refine (hNi.prod hφc).image ?_
    refine continuous_pi fun _ => continuous_pi fun i => ?_
    have h1 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.2 0 i) :=
      (continuous_apply i).comp ((continuous_apply 0).comp continuous_snd)
    have h2 : Continuous (fun p : R × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) => p.1 ⊗ₜ[F] (1 : E)) :=
      cT.comp continuous_fst
    exact h1.mul h2
  obtain ⟨C', hC'c, hC'⟩ := D.hcpt C₁ hC₁c
  obtain ⟨C₂, hC₂c, hC₂f, hC₂⟩ := hCt C' hC'c
  obtain ⟨cD, hcD⟩ := hbd' C₂ Dc hC₂c hC₂f hDc
  obtain ⟨Bd, hBd⟩ := hφ.bounded_above_of_compact_support hφc
  have hBd0 : 0 ≤ Bd := (norm_nonneg _).trans (hBd 0)
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have eD : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.2.2 ∈ Dc :=
    (continuous_snd.comp continuous_snd).continuousAt hDn
  have eN : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀), z.1 ∈ N :=
    continuous_fst.continuousAt hNn
  have hmeas : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      AEStronglyMeasurable (fun y₀ => G ((s y₀, z.1, z.2.1), z.2.2))
        (m₁ (hermScal R σ (algebraMap F R t))) := by
    refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous (fun h : HA R σ (blockOne (algebraMap F E t) J) => G ((h, z.1, z.2.1), z.2.2)) := by
      refine continuous_iff_continuousAt.2 fun h => ?_
      refine ContinuousAt.comp (g := G) (f := fun h => ((h, z.1, z.2.1), z.2.2)) (hG _) ?_
      exact (((continuous_id.prodMk continuous_const)).prodMk continuous_const).continuousAt
    exact (hc.measurable.comp D.hs).aestronglyMeasurable
  have hcont : ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
      ContinuousAt (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => G ((s y₀, z.1, z.2.1), z.2.2))
        (α₀, c₀, S₀) := by
    refine Filter.Eventually.of_forall fun y₀ => ?_
    refine ContinuousAt.comp (g := G)
      (f := fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => ((s y₀, z.1, z.2.1), z.2.2)) (hG _) ?_
    exact ((continuous_const.prodMk (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)).continuousAt
  have hbound : ∀ᶠ z : R × (Fin n → R ⊗[F] E) × HermR R σ n in 𝓝 (α₀, c₀, S₀),
      ∀ᵐ y₀ ∂(m₁ (hermScal R σ (algebraMap F R t))),
        ‖G ((s y₀, z.1, z.2.1), z.2.2)‖ ≤ C₁.indicator (fun _ => Bd * (cD : ℝ)) y₀ := by
    filter_upwards [eN, eD] with z hzN hzD
    filter_upwards [hgram₁ (hermScal R σ (algebraMap F R t))] with y₀ hy₀
    obtain ⟨u, hu⟩ := hNs hzN
    have hsec := D.hsec y₀ hy₀
    have hvan : ∀ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ≠ 0 → y₀ ∈ C₁ := by
      intro X hne
      refine ⟨(((u⁻¹ : Rˣ) : R), actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)),
        ⟨⟨u⁻¹, ?_, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
      · simpa [Set.mem_inv, hu] using hzN
      · funext a i
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        simp only [scl]
        rw [actW_vec_zero, hsec, ← hu, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv,
          mul_one, ← Algebra.TensorProduct.one_def, mul_one]
    by_cases hy : y₀ ∈ C₁
    · have h2 : s y₀ ∈ C' := hC' y₀ hy hy₀
      have hvanX : ∀ X, X ∉ C₂ → φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) = 0 :=
        fun X hX => by_contra fun hne => hX (hC₂ _ h2 _ _ _ hne)
      rw [Set.indicator_of_mem hy]
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvanX]
      have hfin : m' z.2.2 C₂ < ∞ := (hcD _ hzD).trans_lt ENNReal.coe_lt_top
      refine (norm_setIntegral_le_of_norm_le_const hfin (fun X _ => hBd _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hBd0
      have := ENNReal.toReal_mono ENNReal.coe_ne_top (hcD _ hzD)
      simpa [Measure.real] using this
    · rw [Set.indicator_of_notMem hy]
      have h0 : (fun X => φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X))) = 0 :=
        funext fun X => by_contra fun hne => hy (hvan X hne)
      change ‖∫ X, φ (actW R σ _ (s y₀) (vec (z.1 ⊗ₜ[F] (1 : E)) z.2.1 X)) ∂(m' z.2.2)‖ ≤ _
      rw [h0]
      simp
  have hint : Integrable (C₁.indicator (fun _ => Bd * (cD : ℝ)))
      (m₁ (hermScal R σ (algebraMap F R t))) :=
    (integrable_indicator_iff hC₁c.isClosed.measurableSet).2 (integrableOn_const hC₁c.measure_lt_top.ne)
  exact continuousAt_of_dominated hmeas hbound hint hcont

end GlobalTheory.CompanionTheory.SW.StageF.ContTwoF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetric
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem measurable_PintF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, ⟨κ, hκs, hκm⟩, -, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  haveI : IsSFiniteKernel κ := hκs
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  have hfin := Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner
  have hm'κ : m' = fun S => κ S := funext fun S => (hκm S).symm
  rw [hm'κ]
  exact hfin

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_character_integral_vanishes : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ ζ : Matrix (Fin ρ) (Fin p) D.host.E, ζ ≠ 0 → ∫ x in m.𝓕, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ζ) ∂m.μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero | exact GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_chv_rt_eq_zero <;> assumption)
end

