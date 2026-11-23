module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolic
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_tuple_vH {T : Type} [MeasurableSpace T] (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 2) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 2) => m) =
      ∫⁻ a : Fin 1 → Fin n → T, ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
        ψ (fun j => vH (a 0 j) (s 0 j) (Y j))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) := by
  have hu : ∀ f : (Fin n → T) → ℝ≥0∞,
      ∫⁻ a : Fin 1 → Fin n → T, f (a 0) ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) =
        ∫⁻ c, f c ∂(Measure.pi fun _ : Fin n => m) := fun f =>
    (measurePreserving_funUnique (Measure.pi fun _ : Fin n => m) (Fin 1)).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) f
  have hc : ∀ c : Fin n → T, Measurable fun X : Fin n → Fin (M + 1) → T =>
      ψ (fun a => Fin.cons (c a) (X a)) := by
    intro c
    refine hψ.comp (measurable_pi_iff.2 fun a => ?_)
    exact (TupFubini.measurable_cons_tail (c a)).comp (measurable_pi_apply a)
  rw [TupFubini.lintegral_tuple_first_coord m n (M + 1) ψ hψ]
  refine Eq.trans ?_ (hu fun c => ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
    ψ (fun j => vH (c j) (s 0 j) (Y j)) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
    ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)).symm
  refine lintegral_congr fun c => ?_
  rw [TupFubini.lintegral_tuple_first_coord m n M _ (hc c)]
  exact (hu fun c' => ∫⁻ Y : Fin n → Fin M → T, ψ (fun j => vH (c j) (c' j) (Y j))
    ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)).symm

theorem lintegral_chartS_of_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ X, ¬ IsUnit (X 0 0) → g X = 0)
    (hc : ∀ x : Fin (M + 2) → R ⊗[F] E, IsUnit (x 0) → ∃ c : HA R σ (hypOne J), ∀ v,
      ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v) :
    ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
        ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨hK, hW, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have hJ' := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ).1
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hBK : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hBt := hBorel 1 n
  have hHaar := hW 1 n
  have step : ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y)
        ∂(coordW R b lam n (M + 2)) ∂(coordW R b lam 1 (M + 2)) :=
    TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 2) g hg
  rw [step]
  refine lintegral_congr fun x => ?_
  by_cases hu : IsUnit (x 0 0)
  · obtain ⟨c, hcv⟩ := hc (x 0) hu
    have hact : Measurable (actW R σ (hypOne J) c :
        (Fin n → Fin (M + 2) → R ⊗[F] E) → Fin n → Fin (M + 2) → R ⊗[F] E) := by
      have := hBorel n (M + 2)
      have hcont := ((_root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 2) (hypOne J) hJ' R).2.2.2.2.2 n).1
      exact (hcont.comp (Continuous.prodMk_right c)).measurable
    have hinv := _root_.GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq F E σ hCM (M + 2) (hypOne J) hJ' R hR n (coordW R b lam n (M + 2)) (hW n (M + 2)) c
    have hf : Measurable fun Y : Fin n → Fin (M + 2) → R ⊗[F] E => g (Fin.cons (x 0) Y) :=
      hg.comp (TupFubini.measurable_cons_tail (x 0))
    have hψ := hf.comp hact
    calc ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) ∂(coordW R b lam n (M + 2))
        = ∫⁻ Y, g (Fin.cons (x 0) Y) ∂((coordW R b lam n (M + 2)).map (actW R σ (hypOne J) c)) := by
          rw [hinv]
      _ = ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c Y)) ∂(coordW R b lam n (M + 2)) :=
          lintegral_map hf hact
      _ = ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
            (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
            ∂(coordW R b lam 1 n) :=
          lintegral_tuple_vH (coordK R b lam) n M _ hψ
      _ = _ := by
          refine lintegral_congr fun a => ?_
          have ht := lintegral_add_right_eq_self (μ := coordW R b lam 1 n)
            (fun s : Fin 1 → Fin n → R ⊗[F] E => ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
              (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M))
            (fun _ j => - (tHalf R σ J (x 0) * a 0 j))
          rw [← ht]
          refine lintegral_congr fun s => lintegral_congr fun Y => ?_
          congr 1
          unfold chartS
          congr 1
          funext j
          simpa [actW, actTup, sub_eq_add_neg] using hcv (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))
  · have h0 : ∀ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) = 0 := fun Y => hg0 _ (by simpa using hu)
    have h1 : ∀ a s Y, g (chartS R σ J x a s Y) = 0 := fun a s Y => hg0 _ (by simpa [chartS] using hu)
    simp [h0, h1]

theorem chartS_lintegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam g hg hg0
  exact lintegral_chartS_of_unitary F E σ hCM M J hJ R hR n d b lam hlam g hg hg0
    fun x hx => GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary F E σ hCM M J hJ R x hx

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernPartNullSetZero
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ

theorem chernPart_null_of_chart_null : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB X} (φ : GlobalTheory.Weight q σ B)
    (ε : ℤˣ) (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) → φ.chernPart D ε Z = 0 := by
  intro k _ X q σ D B φ ε Z hZ hc
  have hchart : ∀ (c : GlobalTheory.AlgChart q σ D) (ρ : GlobalTheory.CxPts q σ → ENNReal),
      GlobalTheory.ChartGlue.chartMeas c.e ρ Z = 0 := by
    intro c ρ
    unfold GlobalTheory.ChartGlue.chartMeas
    have hf : AEMeasurable c.e.symm ((volume.restrict c.e.target).withDensity (ρ ∘ c.e.symm)) :=
      (c.e.continuousOn_symm.aemeasurable c.e.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [Measure.map_apply_of_aemeasurable hf hZ]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' c.e.open_target.measurableSet, Set.inter_comm]
    exact hc c
  have hle : ∀ ρ : GlobalTheory.AlgChart q σ D → GlobalTheory.CxPts q σ → ENNReal,
      GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ ≤
        (GlobalTheory.ChartGlue.glueMeas (fun c : GlobalTheory.AlgChart q σ D => c.e) ρ).restrict Zᶜ := by
    intro ρ
    unfold GlobalTheory.ChartGlue.glueMeas
    refine iSup_le fun c => ?_
    have hae : ∀ᵐ y ∂(GlobalTheory.ChartGlue.chartMeas c.e (ρ c)), y ∈ Zᶜ := by
      rw [ae_iff]
      simpa using hchart c (ρ c)
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact Measure.restrict_mono subset_rfl
      (le_iSup (fun c : GlobalTheory.AlgChart q σ D => GlobalTheory.ChartGlue.chartMeas c.e (ρ c)) c)
  have h3 : φ.chernPart D ε Z ≤ (φ.chernPart D ε).restrict Zᶜ Z :=
    Measure.le_iff'.mp (hle fun c y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Z
  rw [Measure.restrict_apply hZ, Set.inter_compl_self, measure_empty] at h3
  exact nonpos_iff_eq_zero.mp h3

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.Scheme.Hom.finiteType_appLE (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨_root_.GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := _root_.GlobalTheory.CompanionTheory.MPDict.DimVar.isArithVar_ptIdeal m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonicStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_of_capelli_monic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), J ⊆ Zalg E n → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) → Cofin J := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | exact GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | (intros; apply GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicDenominator
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.AdelicDenom

theorem isOpen_integral (F : Type) [Field F] [NumberField F] :
    IsOpen {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} := by
  have h := RestrictedProduct.isOpen_forall_mem (ι := HeightOneSpectrum (𝓞 F))
    (R := fun v => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem natCast_integral (F : Type) [Field F] [NumberField F] (M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (M : Af F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v :=
  GlobalTheory.IntegralFinAdele.natCast_apply F M v ▸
    HeightOneSpectrum.coe_mem_adicCompletionIntegers v (M : 𝓞 F)

theorem exists_common_denominator (F : Type) [Field F] [NumberField F] (K : Set (Af F))
    (hK : IsCompact K) :
    ∃ M : ℕ, 0 < M ∧ ∀ a ∈ K, ∀ v,
      ((M : Af F) * a) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  let U : {M : ℕ // 0 < M} → Set (Af F) := fun M =>
    (fun a => (M.1 : Af F) * a) ⁻¹'
      {a : Af F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  have hU : ∀ M, IsOpen (U M) := fun M =>
    (isOpen_integral F).preimage (continuous_const_mul _)
  have hcov : K ⊆ ⋃ M, U M := fun a _ => by
    obtain ⟨M, hM, h⟩ := GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F a
    exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcov
  refine ⟨∏ m ∈ t, m.1, Finset.prod_pos fun m _ => m.2, fun a ha v => ?_⟩
  obtain ⟨m, hm, ham⟩ := Set.mem_iUnion₂.1 (ht ha)
  obtain ⟨c, hc⟩ : m.1 ∣ ∏ m ∈ t, m.1 := Finset.dvd_prod_of_mem (fun m => m.1) hm
  have h : ((∏ m ∈ t, m.1 : ℕ) : Af F) * a = (c : Af F) * ((m.1 : Af F) * a) := by
    rw [hc, Nat.cast_mul]; ring
  rw [h, GlobalTheory.IntegralFinAdele.mul_apply']
  exact mul_mem (natCast_integral F c v) (ham v)

theorem exists_denominator_of_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (C : Set (Af F ⊗[F] E)), IsCompact C →
    ∃ d : ℕ, 0 < d ∧ ∀ x : E, (1 : Af F) ⊗ₜ[F] x ∈ C → ∃ y : 𝓞 E, (d : E) * x = y := by
  intro F E _ _ _ _ _ C hC
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let ε := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (Af F) ε
  have hcont : ∀ k, Continuous (b.coord k) := fun k =>
    IsModuleTopology.continuous_of_linearMap (b.coord k)
  have hK : IsCompact (⋃ k, (b.coord k) '' C) :=
    isCompact_iUnion fun k => hC.image (hcont k)
  obtain ⟨M, hM, hMK⟩ := exists_common_denominator F _ hK

  have : Algebra.IsAlgebraic ℤ E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).2 inferInstance
  have hm : ∀ k, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * ε k) := fun k => by
    obtain ⟨m, y, hm, hmy⟩ := IsAlgebraic.exists_nsmul_eq (𝓞 E)
      (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) (ε k))
    refine ⟨m, Nat.pos_of_ne_zero hm, ?_⟩
    rw [← nsmul_eq_mul, hmy]
    exact RingOfIntegers.isIntegral_coe y
  choose m hm0 hmi using hm
  refine ⟨M * ∏ k, m k, Nat.mul_pos hM (Finset.prod_pos fun k _ => hm0 k), fun x hx => ?_⟩

  have hcoord : ∀ k, IsIntegral ℤ ((M : F) * ε.repr x k) := fun k => by
    have hmem : b.coord k ((1 : Af F) ⊗ₜ[F] x) ∈ ⋃ k, (b.coord k) '' C :=
      Set.mem_iUnion.2 ⟨k, Set.mem_image_of_mem _ hx⟩
    have hrepr : b.coord k ((1 : Af F) ⊗ₜ[F] x) = algebraMap F (Af F) (ε.repr x k) := by
      simp [b, Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul]
    have h := hMK _ hmem
    rw [hrepr, ← map_natCast (algebraMap F (Af F)) M, ← map_mul] at h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 _ h
    rw [hy]
    exact RingOfIntegers.isIntegral_coe y

  have hP : ∀ k, IsIntegral ℤ (((∏ j, m j : ℕ) : E) * ε k) := fun k => by
    obtain ⟨c, hc⟩ : m k ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ k)
    have : ((∏ j, m j : ℕ) : E) * ε k = (c : E) * ((m k : E) * ε k) := by
      rw [hc, Nat.cast_mul]; ring
    rw [this]
    exact (isIntegral_natCast c : IsIntegral ℤ (c : E)).mul (hmi k)
  have hdx : ((M * ∏ k, m k : ℕ) : E) * x =
      ∑ k, algebraMap F E ((M : F) * ε.repr x k) * (((∏ j, m j : ℕ) : E) * ε k) := by
    conv_lhs => rw [← ε.sum_repr x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  have hint : IsIntegral ℤ (((M * ∏ k, m k : ℕ) : E) * x) := by
    rw [hdx]
    exact IsIntegral.sum _ fun k _ => (hcoord k).algebraMap.mul (hP k)
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 hint
  exact ⟨y, hy.symm⟩

end GlobalTheory.CompanionTheory.AdelicDenom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorization
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.JacStages

namespace GlobalTheory.CompanionTheory.CoarseOcc

theorem nontrivial_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : Nontrivial V := by
  obtain ⟨S, f, hf⟩ := h
  haveI : Nontrivial W := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  refine ⟨(v : V), 0, fun h0 => hu ?_⟩
  have hv0 : v = 0 := Subtype.ext h0
  rw [hv0, map_zero]

theorem sum_concat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s : ℕ}
    (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ i, (x a i).1 := by
  calc ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
        Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
    _ = ∑ a, ∑ i, (x a i).1 := Fintype.sum_sigma _

theorem exists_one_le_jm_coarse : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  intro k _ _ _ _ hA s N c x _ hcat V _ _ π hs _ h1
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := (sum_concat c x).symm.trans hcat
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φS⟩ := _root_.GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s N d e c (fun a b => (x a b).1) e' V π
  have hsub : IsSubquotient (piTensor fun l => (concat c x l).rep) (jac (refinePlace e e') π) := by
    rw [hE]
    exact jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)
  have hnt := nontrivial_of_isSubquotient (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (concat c x)) hsub
  have hnt2 := @Function.Surjective.nontrivial _ _ hnt _ φS.symm.surjective
  have hnt3 := @Function.Surjective.nontrivial _ _ hnt2 _
    (Submodule.Quotient.mk_surjective (twKer (jac e π) (relUnipD k e') 1))
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hnt3
  let T : IrrRep (Levi k fun a => Fin (d a)) := ⟨Y, τ, hτs.isSmooth (isSmooth_jac e hs), hτ⟩
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d T
  refine ⟨fun a => ⟨d a, σ a⟩, hd, fun _ => rfl, ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 ?_)⟩
  exact (isSubquotient_of_equiv φ.symm).trans hτs

end GlobalTheory.CompanionTheory.CoarseOcc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometryStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_L2_norm_one_isometry : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a))) [ν.IsHaarMeasure], ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧ ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) ℂ, Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.transfer | exact GlobalTheory.CompanionTheory.CuspTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.transfer <;> assumption)
end

