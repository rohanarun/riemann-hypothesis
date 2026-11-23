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
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductUnfold
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF


set_option maxHeartbeats 1000000 in
theorem fibSF_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibSF σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ UsetF σ J t B₀)ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ BsetF R σ B₀
  swap
  · simp [fibSF, hS]
  obtain ⟨m₀, D₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  have hH := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).2
  have hker₁ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨hsf', -, -, hfib'⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hsf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hα : IsUnit α := by
    have hu : α * (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) = 1 := by
      simp [α, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
    exact IsUnit.of_mul_eq_one _ hu
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hopen := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ D.hCM R D.hR (n + 1) (M + 1)
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet.inter
      hopen.measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∧
        LinearIndependent (R ⊗[F] E) (f p) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    refine ⟨?_, ?_⟩
    · change gramR R σ (blockOne (algebraMap F E t) J)
        (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
      rw [hpres]
      exact hcoord S p.2 hS hp.1
    · exact (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff F E R σ (M + 1) (n + 1) _ (s p.1) (vec α c p.2)).2
        ((GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n α hα c p.2).2 hp.2)
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      UsetF σ J t B₀)ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS.1, ⟨⟨S, hS, (Set.mem_singleton_iff.1 hxS.1).symm⟩, hxS.2⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibSF
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionByOneIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_fibSF_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (_root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.StageF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionCompatible
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Unfold1F

open GlobalTheory.CompanionTheory.SW.PiLocalization₂.Unfold1

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {t : F} {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E} {lam : Measure R}
  {m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)}
  {m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)}
  {s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)}
  {B₀ : Set R} {a : R → Rˣ} {κ₁ cm : Rˣ → ℝ≥0}

theorem measurableSet_usetF (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm) :
    MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) := by
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, hsigc, htrc, -, hbw, -, hgramc⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, hbor, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hg (M + 1) _ hJ'
  have hq : Continuous fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
      s0 R (gramR R σ (blockOne (algebraMap F E t) J) v) := by
    unfold s0
    exact continuous_const.mul (htrc.comp ((hgramc (n + 1) (M + 1) _).matrix_elem 0 0))
  have hset : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) =
      (fun v : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E =>
        s0 R (gramR R σ (blockOne (algebraMap F E t) J) v)) ⁻¹' B₀ := by
    ext v
    constructor
    · rintro ⟨S, hS, hSe⟩
      simpa [BsetF, hSe] using hS
    · intro hv
      refine ⟨g v, ?_, (hg v).symm⟩
      simpa [BsetF, ← hg v] using hv
  have hfree := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ D.hCM R D.hR (n + 1) (M + 1)
  unfold UsetF
  rw [hset]
  exact (D.hB₀.preimage hq).measurableSet.inter hfree.measurableSet

theorem chi_eq_zero_F
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞)
    {y : Fin 1 → Fin (M + 1) → R ⊗[F] E}
    (hy : s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀) :
    chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) y = 0 := by
  unfold chi
  have hz : ∀ Z : Fin n → Fin (M + 1) → R ⊗[F] E,
      (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ (Fin.cons (y 0) Z) = 0 := by
    intro Z
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨⟨S, hS, hSe⟩, -⟩
    apply hy
    rw [← corner_half_trace_gram_cons R σ _ y Z, ← hSe]
    exact hS
  simp [hz]

end Main

theorem first_step_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ y₀, chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) ∂(m₁ (hermScal R σ (algebraMap F R t))) ∂lam := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ
  obtain ⟨m₀, D₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hTR := D.hR.1
  have hLC := D.hR.2.1
  have hSC := D.hR.2.2.1
  have hT2 := D.hR.2.2.2.1
  obtain ⟨k1, k2, k3, k4, -, -, -, hbw, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  have hUm : MeasurableSet (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurableSet_usetF D
  have hφ' := hφ.indicator hUm
  have hchi := measurable_chi D₀ hφ'

  obtain ⟨-, -, -, hbor1, hg1⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R 1
  obtain ⟨g₁, hg₁c, hg₁⟩ := hg1 (M + 1) _ hJ'
  obtain ⟨hUo, -, -, -, -, hae⟩ := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  have hU₁ : MeasurableSet {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
      IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} := by
    have : {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det} = g₁ ⁻¹' Unt σ R 1 := by
      ext X
      simp [Unt, hg₁ X]
    rw [this]
    exact (hUo.preimage hg₁c).measurableSet
  obtain ⟨hh, hh2, hh3⟩ := hermScal_main F E σ D.hCM R d b
  have hemb : MeasurableEmbedding (hermScal R σ) := (hh.homeomorph _).measurableEmbedding
  have hs0 : ∀ x : R, s0 R ((hermScal R σ x : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = x :=
    fun x => hh.injective (hh2 (hermScal R σ x))
  set χ := chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) with hχ
  have hzero : ∀ y, s0 R (gramR R σ (blockOne (algebraMap F E t) J) y) ∉ B₀ → χ y = 0 :=
    fun y hy => chi_eq_zero_F φ hy

  have e1 : ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1))
      = ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hUm]
    exact _root_.GlobalTheory.CompanionTheory.SW.lintegral_tuple_moving_frame F E σ D.hCM M _ hJ' R D.hR d b lam D.hlam n (sTil σ J t s a) (measurable_sTil D₀) _ hφ'
  have e2 : ∫⁻ y, χ y ∂(coordW R b lam 1 (M + 1)) =
      ∫⁻ y in {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}, χ y ∂(coordW R b lam 1 (M + 1)) := by
    rw [← lintegral_indicator hU₁]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ {X : Fin 1 → Fin (M + 1) → R ⊗[F] E |
        IsUnit (gramR R σ (blockOne (algebraMap F E t) J) X).det}
    · exact (Set.indicator_of_mem hy χ).symm
    · rw [Set.indicator_of_notMem hy, hzero y fun h => hy (isUnit_gram D₀ h)]
  have e3 := D.hm₁.2.1 χ hchi
  rw [← hh3 lam D.hlam, hemb.lintegral_map] at e3
  have e4 : ∫⁻ x, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam = ∫⁻ x in B₀, ∫⁻ v, χ v ∂(m₁ (hermScal R σ x)) ∂lam := by
    rw [← lintegral_indicator D.hB₀.measurableSet]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ B₀
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hae (hermScal R σ x)] with y hy
      refine hzero y ?_
      rw [hy, hs0]
      exact hx
  rw [e1, e2, e3, e4]
  refine setLIntegral_congr_fun D.hB₀.measurableSet fun x hx => ?_
  have hm : m₁ (hermScal R σ x) =
      κ₁ (a x) • (m₁ (hermScal R σ (algebraMap F R t))).map (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) := by
    have := D.hscale (a x)
    rwa [← D.hsq x hx] at this
  have hsm : Measurable (scl (N := M + 1) (n := 1) (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E))) :=
    measurable_scl.comp (measurable_const.prodMk measurable_id)
  simp only [hm]
  rw [lintegral_smul_measure, lintegral_map hchi hsm]
  rfl

end GlobalTheory.CompanionTheory.SW.StageF.Unfold1F
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionMeasurable
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.Fibre

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem chi_at_fibreF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ x ∈ B₀, ∀ y₀ : Fin 1 → Fin (M + 1) → R ⊗[F] E, gramR R σ (blockOne (algebraMap F E t) J) y₀ = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → chi σ J t s a b lam ((UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)).indicator φ) (scl (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) y₀) = ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S', ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (((a x : Rˣ) : R) ⊗ₜ[F] (1 : E)) c X)) ∂(m' S') ∂(coordHerm R σ b lam n) ∂(Measure.pi fun _ => coordK R b lam) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ x hx y₀ hy₀
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id D.hR
  obtain ⟨m₀, D₀⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  have hJt := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨-, -, -, -, -, -, -, hBor, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  obtain ⟨-, -, -, -, -, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJt R
  obtain ⟨-, -, -, -, hlift⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R (n + 1)
  obtain ⟨g, -, hg⟩ := hlift (M + 1) _ hJt
  have hcoord := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.GramCoord.coords F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).1 x hx
  have hd : Module.finrank F E = 2 := D.hCM.2.2.1
  set u : R := ((a x : Rˣ) : R) with hu
  have huE : IsUnit (u ⊗ₜ[F] (1 : E)) :=
    (Units.isUnit (a x)).map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hy00 : gramR R σ (blockOne (algebraMap F E t) J) y₀ 0 0 = algebraMap F R t ⊗ₜ[F] (1 : E) := by
    rw [hy₀]; rfl
  have hG : gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀) 0 0 =
      x ⊗ₜ[F] (1 : E) := by
    rw [gramR_scl_tmul, hy00, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    have hq : u ^ 2 * algebraMap F R t = x := (D.hsq x hx).symm
    rw [mul_one, mul_one, ← pow_two, hq]
  have hs0 : s0 R (gramR R σ (blockOne (algebraMap F E t) J) (scl (u ⊗ₜ[F] (1 : E)) y₀)) = x :=
    corner_half_trace_of_pure_tensor R b hd x _ hG
  have hsT : sTil σ J t s a (scl (u ⊗ₜ[F] (1 : E)) y₀) = s y₀ := by
    unfold sTil
    rw [hs0]
    congr 1
    funext i j
    simp only [scl, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [hu, Units.mul_inv]
    exact mul_one _
  have hsec := congrFun (D.hsec y₀ hy₀) 0
  have hcons : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      (Fin.cons (scl (u ⊗ₜ[F] (1 : E)) y₀ 0)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (fun j => Fin.cons (c j) (X j))) :
          Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) := by
    intro c X
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have e : (Fin.cons (u ⊗ₜ[F] (1 : E)) (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) =
          (u ⊗ₜ[F] (1 : E)) • (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E) := by
        funext k
        refine Fin.cases ?_ (fun l => ?_) k <;> simp
      simp only [Fin.cons_zero, vec, actW, actTup]
      rw [e, Matrix.mulVec_smul]
      simp only [actW, actTup] at hsec
      rw [hsec]
      funext k
      simp [scl, mul_comm]
    · simp [vec, actW, actTup]
  have hfree : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      LinearIndependent (R ⊗[F] E)
        (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) ↔
      LinearIndependent (R ⊗[F] E) X := fun c X =>
    (_root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff F E R σ (M + 1) (n + 1) _ (s y₀) _).trans
      (GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n _ huE c X)
  have hmem : ∀ (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E),
      actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) ∈
        (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) ↔
      X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
    intro c X
    have hinv := (hact (n + 1)).2.2.2 (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)
    constructor
    · rintro ⟨-, h⟩
      exact (hfree c X).1 h
    · intro hX
      refine ⟨?_, (hfree c X).2 hX⟩
      have h3 := hcoord c X (g (vec (u ⊗ₜ[F] (1 : E)) c X)) (hg _).symm
      simp only [Set.mem_preimage, hinv]
      refine ⟨g (vec (u ⊗ₜ[F] (1 : E)) c X), ?_, (hg _).symm⟩
      change s0 R _ ∈ B₀
      rw [h3.1]; exact hx
  haveI := hBor n M
  haveI := hBor (n + 1) (M + 1)
  have hUd : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    (_root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ D.hCM R D.hR n M).measurableSet
  have hψ : ∀ c : Fin n → R ⊗[F] E, Measurable fun X : Fin n → Fin M → R ⊗[F] E =>
      φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X)) := by
    intro c
    have hv : Continuous fun X : Fin n → Fin M → R ⊗[F] E => vec (u ⊗ₜ[F] (1 : E)) c X := by
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_const
      · refine continuous_pi fun k => ?_
        refine Fin.cases ?_ (fun l => ?_) k
        · exact continuous_const
        · exact (continuous_apply l).comp (continuous_apply j)
    have hc : Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
        actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X) :=
      (hact (n + 1)).1.comp (continuous_const.prodMk hv)
    exact hφ.comp hc.measurable
  unfold chi
  rw [hsT]
  refine lintegral_congr fun c => ?_
  calc _ = ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
        {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}.indicator (fun X =>
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))) X
        ∂(coordW R b lam n M) := by
        refine lintegral_congr fun X => ?_
        rw [hcons c X]
        by_cases h : X ∈ {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem c X).2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmem c X).1 h'))]
    _ = ∫⁻ X in {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X},
          φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (u ⊗ₜ[F] (1 : E)) c X))
        ∂(coordW R b lam n M) := lintegral_indicator hUd _
    _ = _ := D.hm'.2.1 _ (hψ c)

end GlobalTheory.CompanionTheory.SW.StageF.Fibre
end
end

