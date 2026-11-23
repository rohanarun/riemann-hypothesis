module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
section
noncomputable section

open GlobalTheory.CompanionTheory.ThTot

namespace GlobalTheory.CompanionTheory.ThTot.SchwT

section Analysis

variable {E E₁ E₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

theorem norm_iter_comp_le (A : E →L[ℝ] E₁) (hA : ‖A‖ ≤ 1) (f : SchwartzMap E₁ ℂ) (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun w => f (A w)) z‖ ≤ ‖iteratedFDeriv ℝ n f (A z)‖ := by
  have h : iteratedFDeriv ℝ n (fun w => f (A w)) z =
      (iteratedFDeriv ℝ n f (A z)).compContinuousLinearMap fun _ => A :=
    A.iteratedFDeriv_comp_right (f := f) (f.smooth n) z le_rfl
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _i : Fin n, ‖A‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hA
  exact mul_le_of_le_one_right (norm_nonneg _) this

def tens (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) : SchwartzMap E ℂ where
  toFun z := f (A z) * g (B z)
  smooth' := ((f.smooth ⊤).comp A.contDiff).mul ((g.smooth ⊤).comp B.contDiff)
  decay' := by
    intro k n
    choose Cf hCf using fun (a : ℕ × ℕ) => f.decay' a.1 a.2
    choose Cg hCg using fun (a : ℕ × ℕ) => g.decay' a.1 a.2
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (Cf (k, i) * Cg (0, n - i) + Cf (0, i) * Cg (k, n - i)), fun z => ?_⟩
    have hf1 : ContDiff ℝ n (fun w => f (A w)) := (f.smooth n).comp A.contDiff
    have hg1 : ContDiff ℝ n (fun w => g (B w)) := (g.smooth n).comp B.contDiff
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := n) (N := n) hf1 hg1 z le_rfl
    have hz : ‖z‖ ^ k ≤ ‖A z‖ ^ k + ‖B z‖ ^ k := by
      rcases le_total ‖A z‖ ‖B z‖ with h | h
      · have : ‖z‖ ≤ ‖B z‖ := (hAB z).trans (max_le h le_rfl)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_left (by positivity))
      · have : ‖z‖ ≤ ‖A z‖ := (hAB z).trans (max_le le_rfl h)
        exact (pow_le_pow_left₀ (norm_nonneg _) this k).trans (le_add_of_nonneg_right (by positivity))
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun z => f (A z) * g (B z)) z‖
        ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖ :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ∑ i ∈ Finset.range (n + 1), ‖z‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ * ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖) :=
          Finset.mul_sum _ _ _
      _ ≤ _ := by
          refine Finset.sum_le_sum fun i _ => ?_
          set a := ‖iteratedFDeriv ℝ i f (A z)‖
          set b := ‖iteratedFDeriv ℝ (n - i) g (B z)‖
          have ha0 : 0 ≤ a := norm_nonneg _
          have hb0 : 0 ≤ b := norm_nonneg _
          have h1 : ‖A z‖ ^ k * a ≤ Cf (k, i) := hCf (k, i) (A z)
          have h2 : b ≤ Cg (0, n - i) := by
            have := hCg (0, n - i) (B z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h3 : a ≤ Cf (0, i) := by
            have := hCf (0, i) (A z)
            simp only [pow_zero, one_mul] at this
            exact this
          have h4 : ‖B z‖ ^ k * b ≤ Cg (k, n - i) := hCg (k, n - i) (B z)
          have hn0 : (0 : ℝ) ≤ n.choose i := by positivity
          have hA' := norm_iter_comp_le A hA f i z
          have hB' := norm_iter_comp_le B hB g (n - i) z
          have hAk : 0 ≤ ‖A z‖ ^ k := by positivity
          have hBk : 0 ≤ ‖B z‖ ^ k := by positivity
          have e1 : ‖A z‖ ^ k * a * b ≤ Cf (k, i) * Cg (0, n - i) :=
            mul_le_mul h1 h2 hb0 ((mul_nonneg hAk ha0).trans h1)
          have e2 : a * (‖B z‖ ^ k * b) ≤ Cf (0, i) * Cg (k, n - i) :=
            mul_le_mul h3 h4 (mul_nonneg hBk hb0) (ha0.trans h3)
          calc ‖z‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w => f (A w)) z‖ *
                ‖iteratedFDeriv ℝ (n - i) (fun w => g (B w)) z‖)
              ≤ (‖A z‖ ^ k + ‖B z‖ ^ k) * ((n.choose i : ℝ) * a * b) := by
                refine mul_le_mul hz ?_ (by positivity) (by positivity)
                exact mul_le_mul (mul_le_mul_of_nonneg_left hA' hn0) hB' (norm_nonneg _) (by positivity)
            _ = (n.choose i : ℝ) * (‖A z‖ ^ k * a * b + a * (‖B z‖ ^ k * b)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hn0

@[simp] theorem tens_apply (A : E →L[ℝ] E₁) (B : E →L[ℝ] E₂) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (hAB : ∀ z, ‖z‖ ≤ max ‖A z‖ ‖B z‖) (f : SchwartzMap E₁ ℂ) (g : SchwartzMap E₂ ℂ) (z : E) :
    tens A B hA hB hAB f g z = f (A z) * g (B z) := rfl

end Analysis

section Coord

variable {T : Type*} [Fintype T] {r s p : ℕ}

def topL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin r → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.castAdd s i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def botL (T : Type*) [Fintype T] (r s p : ℕ) : (T → Fin (r + s) → Fin p → ℂ) →L[ℝ] (T → Fin s → Fin p → ℂ) where
  toFun t := fun τ i j => t τ (Fin.natAdd r i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

theorem norm_coord_le (t : T → Fin r → Fin p → ℂ) (τ : T) (i : Fin r) (j : Fin p) : ‖t τ i j‖ ≤ ‖t‖ :=
  (norm_le_pi_norm (t τ i) j).trans ((norm_le_pi_norm (t τ) i).trans (norm_le_pi_norm t τ))

theorem norm_le_of_coord {t : T → Fin r → Fin p → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ τ i j, ‖t τ i j‖ ≤ C) : ‖t‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun τ => (pi_norm_le_iff_of_nonneg hC).2 fun i =>
    (pi_norm_le_iff_of_nonneg hC).2 fun j => h τ i j

theorem norm_topL_le : ‖topL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_botL_le : ‖botL T r s p‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => by
    rw [one_mul]
    exact norm_le_of_coord (norm_nonneg _) fun τ i j => norm_coord_le t τ _ j

theorem norm_le_max (t : T → Fin (r + s) → Fin p → ℂ) : ‖t‖ ≤ max ‖topL T r s p t‖ ‖botL T r s p t‖ := by
  refine norm_le_of_coord (le_max_of_le_left (norm_nonneg _)) fun τ i j => ?_
  induction i using Fin.addCases with
  | left a => exact le_max_of_le_left (norm_coord_le (topL T r s p t) τ a j)
  | right b => exact le_max_of_le_right (norm_coord_le (botL T r s p t) τ b j)

end Coord

section Finite

variable {R : Type} {tR : TopologicalSpace R} {r s p : ℕ}

def joinR (a : Fin r → Fin p → R) (b : Fin s → Fin p → R) : Fin (r + s) → Fin p → R :=
  fun i j => Fin.addCases (motive := fun _ => R) (fun u => a u j) (fun v => b v j) i

theorem continuous_joinR :
    Continuous fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.addCases with
  | left a => simp only [joinR, Fin.addCases_left]; fun_prop
  | right b => simp only [joinR, Fin.addCases_right]; fun_prop

theorem sb_tensor {g : (Fin r → Fin p → R) → ℂ} {g' : (Fin s → Fin p → R) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin r → Fin p → R)) (hg' : g' ∈ GlobalTheory.WeilM.SB (Fin s → Fin p → R)) :
    (fun u : Fin (r + s) → Fin p → R =>
      g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j)) ∈
      GlobalTheory.WeilM.SB (Fin (r + s) → Fin p → R) := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨hl', hc'⟩ := hg'
  have hT : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin r) (j : Fin p) => u (Fin.castAdd s i) j := by
    fun_prop
  have hB : Continuous fun u : Fin (r + s) → Fin p → R => fun (i : Fin s) (j : Fin p) => u (Fin.natAdd r i) j := by
    fun_prop
  have hlc := (hl.comp_continuous hT).mul (hl'.comp_continuous hB)
  refine ⟨hlc, ?_⟩
  set G : (Fin (r + s) → Fin p → R) → ℂ := fun u =>
    g (fun i j => u (Fin.castAdd s i) j) * g' (fun i j => u (Fin.natAdd r i) j) with hG
  have hlG : IsLocallyConstant G := hlc
  have hclosed : IsClosed (Function.support G) := by
    have : Function.support G = (G ⁻¹' {0})ᶜ := by ext u; simp [Function.mem_support]
    rw [this]
    exact (hlG.isOpen_fiber 0).isClosed_compl
  have hK : IsCompact ((fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g')) := (IsCompact.prod hc hc').image continuous_joinR
  have hsub : Function.support G ⊆ (fun q : (Fin r → Fin p → R) × (Fin s → Fin p → R) => joinR q.1 q.2) ''
      (tsupport g ×ˢ tsupport g') := by
    intro u hu
    have hu' : G u ≠ 0 := hu
    refine ⟨(fun i j => u (Fin.castAdd s i) j, fun i j => u (Fin.natAdd r i) j), ⟨?_, ?_⟩, ?_⟩
    · exact subset_tsupport _ (left_ne_zero_of_mul hu')
    · exact subset_tsupport _ (right_ne_zero_of_mul hu')
    · funext i j
      induction i using Fin.addCases with
      | left a => simp [joinR]
      | right b => simp [joinR]
  have : HasCompactSupport G := by
    unfold HasCompactSupport tsupport
    rw [hclosed.closure_eq]
    exact hK.of_isClosed_subset hclosed hsub
  exact this

end Finite

theorem schwTensor : SchwTensor := by
  intro D θ _ r s p φ hφ φ' hφ'
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
  | add a b _ _ ha hb =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
    convert this using 1
    funext y; simp [add_mul]
  | smul c a _ ha =>
    have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
    convert this using 1
    funext y; simp [mul_assoc]
  | mem a ha =>
    obtain ⟨f, g, hg, rfl⟩ := ha
    induction hφ' using Submodule.span_induction with
    | zero =>
    convert (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).zero_mem using 1
    funext y; simp
    | add a b _ _ ha hb =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).add_mem ha hb
      convert this using 1
      funext y; simp [mul_add]
    | smul c a _ ha =>
      have := (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ (r + s) p).smul_mem c ha
      convert this using 1
      funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
    | mem b hb =>
      obtain ⟨f', g', hg', rfl⟩ := hb
      refine Submodule.subset_span ⟨tens (topL _ r s p) (botL _ r s p) norm_topL_le norm_botL_le norm_le_max f f',
        _, sb_tensor hg hg', ?_⟩
      funext y
      simp only [tens_apply]
      exact mul_mul_mul_comm _ _ _ _

end GlobalTheory.CompanionTheory.ThTot.SchwT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesArchimedeanHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem pi_map_update_add {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {n : ℕ}
    (ν : Measure V) [SigmaFinite ν] [ν.IsAddRightInvariant] (a : Fin n) (T : (Fin n → V) → V)
    (hT : Measurable T) (hTa : ∀ x y, T (Function.update x a y) = T x) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => Function.update x a (x a + T x)) =
      Measure.pi fun _ : Fin n => ν := by
  have hf : Measurable (fun x : Fin n → V => Function.update x a (x a + T x)) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j = a
    · subst h
      simp only [Function.update_self]
      exact (measurable_pi_apply j).add hT
    · simpa [Function.update_of_ne h] using measurable_pi_apply j
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [← Measure.pi_pi, ← lintegral_indicator_one h2s, ← lintegral_indicator_one h2s,
    lintegral_map (measurable_one.indicator h2s) hf]
  refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp hf)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have key : ∀ y : V, Function.update (Function.update x a y) a (Function.update x a y a + T (Function.update x a y))
      = Function.update x a (y + T x) := by
    intro y
    simp [hTa]
  simp only [Function.comp_def, key]
  exact lintegral_add_right_eq_self
    (fun y => (Set.univ.pi s).indicator (1 : (Fin n → V) → ℝ≥0∞) (Function.update x a y)) (T x)

theorem coordW_map_shearK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam a s hs
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) := inferInstance
  haveI hν : (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).IsAddHaarMeasure := inferInstance
  have hmul : ∀ c : Ainf F ⊗[F] E, Measurable (fun y : Ainf F ⊗[F] E => c * y) := fun c =>
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun (x : Fin n → Fin M → Ainf F ⊗[F] E) (i : Fin M) => ∑ c, s c * x c i) := by
    refine Measurable.of_eval fun i => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (hmul (s c)).comp ((measurable_pi_apply i).comp (measurable_pi_apply c))
  have hTa : ∀ (x : Fin n → Fin M → Ainf F ⊗[F] E) (y : Fin M → Ainf F ⊗[F] E),
      (fun i => ∑ c, s c * Function.update x a y c i) = fun i => ∑ c, s c * x c i := by
    intro x y
    funext i
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = a
    · subst h; simp [hs]
    · simp [Function.update_of_ne h]
  exact pi_map_update_add (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) a _ hT hTa

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (GlobalTheory.SmGL.jac e π) = jhMult σ (GlobalTheory.SmGL.jac e π₁) + jhMult σ (GlobalTheory.SmGL.jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e T.toRepresentation))
    (hjm : jhMult ρ (GlobalTheory.SmGL.jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (GlobalTheory.SmGL.jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (GlobalTheory.SmGL.jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
end

