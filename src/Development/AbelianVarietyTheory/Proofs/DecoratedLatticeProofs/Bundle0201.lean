module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.StdUnn


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_realPar_of_isCharAF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ θ : InfFam D, IsInfFam θ → ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l := by
  intro D ψ hψ θ hθ
  obtain ⟨ψ₀, h₀, a, -, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨fun τ => -(tauE D τ y).re, ?_⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
    intro ρ
    apply Complex.ext <;> simp [hreal ρ]
  simp only [e4, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  ring

end GlobalTheory.StdUnn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdeles
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem realIdem_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem realIdem_gen (σ : E →ₐ[F] E) : ∃ e : AF F ⊗[F] E, e * e = e ∧ sigR (AF F) σ e = e ∧
    (∀ v, compFin F E v e = 0) ∧ (∀ w, compInf F E w e = 1) ∧
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom e = 0 ∧
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom e = 1 := by
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have h0 : sndA F (pairA F 1 0) = 0 := rfl
  have h1 : fstA F (pairA F 1 0) = 1 := rfl
  refine ⟨pairA F 1 0 ⊗ₜ[F] (1 : E), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  · exact realIdem_map F E (AlgHom.id F (AF F)) σ _
  · intro v
    refine (realIdem_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, h0, map_zero, TensorProduct.zero_tmul]
  · intro w
    refine (realIdem_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, h1, map_one, Algebra.TensorProduct.one_def]
  · rw [realIdem_map, h0, TensorProduct.zero_tmul]
  · rw [realIdem_map, h1, Algebra.TensorProduct.one_def]

end

theorem realIdem_exists : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 :=
  fun D => realIdem_gen D.host.F D.host.E _

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCore
section
namespace I195MixedCoordinates_b25480cef10b1759a6cbdced

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_b25480cef10b1759a6cbdced

public noncomputable abbrev _root_.I195MixedCoordinates_6fe4275e00e1b6fee4b47128.source :=
  @_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitPlaceForm


set_option maxHeartbeats 1000000 in
theorem exists_form_of_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f') x) = k * ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 hne
  letI : MeasurableSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.measHalf _ _ _
  haveI : BorelSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.borelHalf _ _ _
  have hH : ∀ x, x ∈ GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ ↔ ∀ i j, cA D e * x i j = x i j := fun x => Iff.rfl
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.HalfLinForm.halfAvg_linear D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun h a => ?_⟩
  · rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u), hℓ f hf]
    exact GlobalTheory.HalfInvariance.half_avg_heis_inv D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 _ hH _ u hu f hf
  · obtain ⟨f, hf, hn⟩ := GlobalTheory.HalfNonvan.avg_mixS_ne_zero D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hne _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
    exact ⟨f, hf, by rw [hℓ f hf]; exact hn⟩
  · obtain ⟨r, hr, hm⟩ := GlobalTheory.HalfTwist.integral_twist_fix_eq_smul D T.rank ρ (cA D e) _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ) h a
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    have e1 := hm fun x => ℓ₀ ((_root_.I195MixedCoordinates_b25480cef10b1759a6cbdced.source d) T ψ μ 𝓕 f x)
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← e1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitPlaceForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnit
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SkewNorm

theorem exists_norm_eq {R : Type} [CommRing R] (c : R →+* R) (a : R) (ha : c a = -a) (B B' : Ideal R)
    (hsup : B ⊔ B' = ⊤) (h1 : ∀ x ∈ B, c x ∈ B') (h2 : ∀ y ∈ B', c y ∈ B)
    (hP : ∀ P : Ideal R, P.IsPrime → a ∈ P → B ≤ P ∨ B' ≤ P) (hcc : ∀ x, c (c x) = x) :
    ∃ α η : R, α * c α = a * η ∧ IsCoprime η a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  have hrad : x * c x ∈ (Ideal.span {a}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hp⟩
    rcases hP P hp (hle (Ideal.mem_span_singleton_self a)) with h | h
    · exact P.mul_mem_right _ (h hx)
    · exact P.mul_mem_left _ (h (h1 x hx))
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hn
  have hN : x ^ (2 * n + 1) * c x ^ (2 * n + 1) = a ^ 2 * (k ^ 2 * (x * c x)) := by
    rw [← mul_pow, pow_succ, mul_comm 2 n, pow_mul, ← hk]; ring
  refine ⟨x ^ (2 * n + 1) + a, c x ^ (2 * n + 1) - x ^ (2 * n + 1) + a * (k ^ 2 * (x * c x) - 1), ?_, ?_⟩
  · rw [map_add (f := _), map_pow, ha]; linear_combination hN
  · rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨P, hPm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hp := hPm.isPrime
    have haP : a ∈ P := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
    have hη := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hd : c x ^ (2 * n + 1) - x ^ (2 * n + 1) ∈ P := by
      have := P.sub_mem hη (P.mul_mem_right (k ^ 2 * (x * c x) - 1) haP)
      rwa [add_sub_cancel_right] at this
    refine hp.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rcases hP P hp haP with h | h
    · have : c x ∈ P := hp.mem_of_pow_mem (2 * n + 1)
        (by simpa using P.add_mem hd (P.pow_mem_of_mem (h hx) (2 * n + 1) (by omega)))
      rw [← map_one c, ← hxy, map_add (f := _)]
      exact P.add_mem this (h (h2 y hy))
    · have : x ∈ P := hp.mem_of_pow_mem (2 * n + 1)
        (by simpa using P.sub_mem (P.pow_mem_of_mem (h (h1 x hx)) (2 * n + 1) (by omega)) hd)
      rw [← hxy]
      exact P.add_mem this (h hy)

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_natCast_mem (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : (n : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (Fv F v) (n : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F n) = 1 := by
    refine le_antisymm (v.valuation_le_one _) (not_lt.1 fun h' => hn ?_)
    exact (v.valuation_lt_one_iff_mem _).1 h'
  rw [map_natCast] at h1
  have h2 := v.valuedAdicCompletion_eq_valuation' (n : F)⁻¹
  exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))


omit [NumberField E] in
theorem inv_mem_intLoc (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (hn : (n : 𝓞 F) ∉ v.asIdeal) [CharZero E] (x y : 𝓞 E)
    (h : x * y = n) : (1 : Fv F v) ⊗ₜ[F] (x : E)⁻¹ ∈ intLoc F E v := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have h' : (x : E) * y = n := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) h
  have hx : (x : E) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h'; exact hn0 (by exact_mod_cast h'.symm)
  have : (x : E)⁻¹ = (n : F)⁻¹ • (y : E) := by
    rw [Algebra.smul_def, map_inv₀, map_natCast, ← h']
    have hy : (y : E) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h'; exact hn0 (by exact_mod_cast h'.symm)
    field_simp
  rw [this, ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  exact tmul_mem_intLoc (inv_natCast_mem v n hn) y


open Classical in
noncomputable def idemAt (F : Type) [Field F] [NumberField F] (q : ℕ) : AF F :=
  (0, ⟨fun v => if (q : 𝓞 F) ∈ v.asIdeal then 1 else 0, Filter.Eventually.of_forall fun v => by
    dsimp only
    split_ifs
    · exact (v.adicCompletionIntegers F).one_mem
    · exact (v.adicCompletionIntegers F).zero_mem⟩)

open Classical in
theorem evFin_idemAt (q : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    evFin F v (idemAt F q) = if (q : 𝓞 F) ∈ v.asIdeal then 1 else 0 := rfl

theorem idemAt_mul (q : ℕ) : idemAt F q * idemAt F q = idemAt F q := by
  refine Prod.ext (mul_zero _) (DFunLike.ext _ _ fun v => ?_)
  change evFin F v (idemAt F q) * evFin F v (idemAt F q) = evFin F v (idemAt F q)
  rw [evFin_idemAt]
  split_ifs <;> simp

omit [NumberField E] in
theorem glue_mul (q : ℕ) (x y x' y' : E) :
    (idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y) * (idemAt F q ⊗ₜ[F] x' + (1 - idemAt F q) ⊗ₜ[F] y') =
      idemAt F q ⊗ₜ[F] (x * x') + (1 - idemAt F q) ⊗ₜ[F] (y * y') := by
  have h := idemAt_mul (F := F) q
  have h1 : idemAt F q * (1 - idemAt F q) = 0 := by linear_combination -h
  have h2 : (1 - idemAt F q) * idemAt F q = 0 := by linear_combination -h
  have h3 : (1 - idemAt F q) * (1 - idemAt F q) = 1 - idemAt F q := by linear_combination h
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, h, h1, h2, h3, TensorProduct.zero_tmul,
    add_zero, zero_add]

omit [NumberField E] in
theorem glue_self (q : ℕ) (x : E) :
    idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] x = (1 : AF F) ⊗ₜ[F] x := by
  rw [← TensorProduct.add_tmul, add_sub_cancel]

noncomputable def glue (q : ℕ) (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) : (AF F ⊗[F] E)ˣ where
  val := idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y
  inv := idemAt F q ⊗ₜ[F] x⁻¹ + (1 - idemAt F q) ⊗ₜ[F] y⁻¹
  val_inv := by rw [glue_mul, mul_inv_cancel₀ hx, mul_inv_cancel₀ hy, glue_self]; rfl
  inv_val := by rw [glue_mul, inv_mul_cancel₀ hx, inv_mul_cancel₀ hy, glue_self]; rfl

omit [NumberField E] in
theorem glue_mem (q : ℕ) (x y : E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (q : 𝓞 F) ∈ v.asIdeal → (1 : Fv F v) ⊗ₜ[F] x ∈ intLoc F E v)
    (h2 : (q : 𝓞 F) ∉ v.asIdeal → (1 : Fv F v) ⊗ₜ[F] y ∈ intLoc F E v) :
    compFin F E v (idemAt F q ⊗ₜ[F] x + (1 - idemAt F q) ⊗ₜ[F] y) ∈ intLoc F E v := by
  have e : ∀ (a : AF F) (z : E), compFin F E v (a ⊗ₜ[F] z) = evFin F v a ⊗ₜ[F] z := fun _ _ => rfl
  rw [map_add (f := _), e, e, map_sub, map_one, evFin_idemAt]
  split_ifs with h
  · simpa using h1 h
  · simpa using h2 h

theorem exists_idele (σ : E →ₐ[F] E) (q : ℕ) (hq : 1 < q) (a α η : 𝓞 E) (ha : a ^ 2 = -(q : 𝓞 E))
    (hα : (α : E) * σ α = a * η) (hcop : IsCoprime η a) (hu : ¬ IsUnit a) :
    ∃ u ε : (AF F ⊗[F] E)ˣ, (ε : AF F ⊗[F] E) * u * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ u = (1 : AF F) ⊗ₜ[F] (a : E) ∧
      (∀ v, compFin F E v ε ∈ intLoc F E v) ∧ ∀ v, compFin F E v (ε⁻¹ : (AF F ⊗[F] E)ˣ) ∈ intLoc F E v := by
  have hη : η ≠ 0 := by rintro rfl; exact hu (isCoprime_zero_left.1 hcop)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : (q : 𝓞 E) = 0 := by simpa using ha
    exact absurd (by exact_mod_cast this : q = 0) (by omega)
  have hηE : (η : E) ≠ 0 := by simpa using hη
  have haE : (a : E) ≠ 0 := by simpa using ha0
  have hαE : (α : E) ≠ 0 := by
    intro h; rw [h, zero_mul] at hα; exact mul_ne_zero haE hηE hα.symm
  obtain ⟨k, hk, d, hd⟩ : ∃ k : ℕ, 0 < k ∧ η ∣ (q : 𝓞 E) ^ k - 1 := by
    haveI : Finite (𝓞 E ⧸ Ideal.span {η}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hη)
    have hcq : IsCoprime η (q : 𝓞 E) := by
      have := (hcop.pow_right (n := 2)).neg_right
      rwa [ha, neg_neg] at this
    have hu' : IsUnit (Ideal.Quotient.mk (Ideal.span {η}) (q : 𝓞 E)) := by
      obtain ⟨s, t, e⟩ := hcq
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ t) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact ⟨-s, by linear_combination e⟩
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu'.unit)
    refine ⟨k, hk, ?_⟩
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
  refine ⟨glue q (α : E) 1 hαE one_ne_zero, glue q (η : E)⁻¹ a (inv_ne_zero hηE) haE, ?_, fun v => ?_, fun v => ?_⟩
  · have e : ∀ (b : AF F) (z : E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (b ⊗ₜ[F] z) = b ⊗ₜ[F] σ z := fun _ _ => rfl
    simp only [glue]
    rw [map_add (f := _), e, e, glue_mul, glue_mul, map_one, mul_one, mul_one, mul_assoc, hα,
      show (η : E)⁻¹ * (a * η) = a by field_simp, glue_self]
  · refine glue_mem q _ _ v (fun h => inv_mem_intLoc v (q ^ k - 1) (fun h' => ?_) η d ?_)
      fun _ => tmul_mem_intLoc (one_mem _) a
    · rw [Nat.cast_sub h1] at h'
      push_cast at h'
      refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      simpa using v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem h k hk) h'
    · rw [Nat.cast_sub h1, ← hd]; push_cast; rfl
  · refine glue_mem q _ _ v (fun _ => ?_) fun h => inv_mem_intLoc v q h a (-a) (by linear_combination -ha)
    rw [inv_inv]
    exact tmul_mem_intLoc (one_mem _) η

end Adelic

theorem different_le (D : D7) (a : 𝓞 D.host.E) (ha : a ^ 2 = -(D.host.q : 𝓞 D.host.E)) (P : Ideal (𝓞 D.host.E))
    (hp : P.IsPrime) (haP : a ∈ P) : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) ≤ P := by
  have hq := D.host.hyp.1
  have hqP : (D.host.q : 𝓞 D.host.E) ∈ P ^ 2 := by
    rw [← neg_mem_iff, ← ha]; exact Ideal.pow_mem_pow haP 2
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_pow (by norm_num), Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  haveI := hp.isMaximal hP0
  haveI : Fact D.host.q.Prime := ⟨hq⟩
  haveI : (Ideal.span {(D.host.q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  have h2 := pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(D.host.q : ℤ)}) P 2 (by simpa using hq.ne_zero)
    (by rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
        exact hqP)
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E), Ideal.dvd_iff_le] at h2
  norm_num at h2
  refine (hp.mul_le.1 h2).resolve_right fun h => ?_
  have hd := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 D.host.K))
  rw [absNorm_differentIdeal D.host.K, GlobalTheory.CurveLattice.discr_hostK] at hd
  have hd' := h (Ideal.mem_map_of_mem _ hd)
  rw [map_natCast, Int.natAbs_neg, Int.natAbs_natCast] at hd'
  have hne : D.host.q ≠ D.host.d := by
    have := D.host.hyp.2.2.1; have := D.host.hyp.2.2.2.1; omega
  obtain ⟨s, t, e⟩ : IsCoprime (D.host.q : 𝓞 D.host.E) (D.host.d : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hq D.host.hyp.2.1).2 hne)
  exact hp.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ add_mem (P.mul_mem_left s (Ideal.pow_le_self two_ne_zero hqP)) (P.mul_mem_left t hd')))

theorem exists_skew_norm_mul_unit : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, (ε : AE D) * u * cA D u = incA D μ ∧ IntA (ε : AE D) ∧ IntA ((ε⁻¹ : (AE D)ˣ) : AE D) := by
  intro D
  have hs : ∀ x : D.host.E, star x = D.host.conj x := Formalism.BasicNotions.Examples₂.star_eq_conj D.host
  have hsq := Formalism.BasicNotions.Examples₂.aE_sq D.host
  have hc := Formalism.BasicNotions.Examples₂.conj_aE D.host
  set a₀ := D.host.sqq
  have hq := D.host.hyp.1
  have hint : IsIntegral ℤ a₀ := IsIntegral.of_pow two_pos (by rw [hsq]; exact (isIntegral_natCast _).neg)
  set a : 𝓞 D.host.E := ⟨a₀, hint⟩
  have ha : a ^ 2 = -(D.host.q : 𝓞 D.host.E) := RingOfIntegers.ext (by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]; exact hsq)
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ _ D.host.conj
  have hcv : ∀ x, ((c x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := fun x => (hs x).symm
  have hcc : ∀ x, c (c x) = x := fun x => RingOfIntegers.ext (by rw [hcv, hcv, star_star])
  obtain ⟨α, η, e, hcop⟩ := exists_norm_eq c a (RingOfIntegers.ext hc) D.host.𝔟 _ D.host.𝔟_spec.2
    (fun x hx => Ideal.smul_mem_pointwise_smul _ _ _ hx)
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective c (fun z => ⟨c z, hcc z⟩)).1 hy
      rwa [hcc])
    (fun P hp haP => hp.mul_le.1 (D.host.𝔟_spec.1 ▸ different_le D a ha P hp haP)) hcc
  have hu : ¬ IsUnit a := fun h => by
    have h2 : IsUnit (D.host.q : 𝓞 D.host.E) := by
      have := (h.pow 2).neg
      rwa [ha, neg_neg] at this
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 h2)
    rw [Ideal.absNorm_span_natCast] at h1
    exact Module.finrank_pos.ne' ((Nat.pow_eq_one.1 h1).resolve_left hq.one_lt.ne')
  refine ⟨a₀, ⟨fun h => hq.ne_zero ?_, (hs _).trans hc⟩, exists_idele D.sp.cm.sig _ hq.one_lt a α η ha ?_ hcop hu⟩
  · rw [h] at hsq
    exact_mod_cast (by simpa using hsq : (D.host.q : D.host.E) = 0)
  · have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at this
    exact (congrArg _ (hcv α).symm).trans this

end GlobalTheory.StdUnn.SkewNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugateStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_type_places_pairwise_not_conjugate : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.Core.Mi.typePlaces_noConj | exact GlobalTheory.Core.Mi.typePlaces_noConj | (intros; apply GlobalTheory.Core.Mi.typePlaces_noConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  first | exact @GlobalTheory.ChainTw.quot_unrAt_twist | exact GlobalTheory.ChainTw.quot_unrAt_twist | (intros; apply GlobalTheory.ChainTw.quot_unrAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parOfVal_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  intro hP D hM hL c hc j hj s hs x w B hv hf
  obtain ⟨e, he⟩ := _root_.GlobalTheory.ChainOnto.ValPart.valPart_mem hP D hM hL c hc j hj s hs x w B hv hf
  exact (_root_.GlobalTheory.ChainOnto.partPar hP D c hc j hj s hs x e he).2 w B hv hf
end

