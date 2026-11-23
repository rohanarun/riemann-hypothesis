module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem integrable_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  intro D V W a b P Q hP hQ _hiso ψ hψ μ hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨U, hU, hvan⟩ := _root_.GlobalTheory.CoeffVanish.matrixCoeff_eq_zero D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨K, hK, hKmem⟩ := _root_.GlobalTheory.IsoMeanAnnih.finPart_mem_compact D V W a b P Q hP hQ ψ hψ U hU
  refine _root_.GlobalTheory.AdelicIntegrable.integrable_of_rapid_decay D a b μ hμ θ hθ _ (_root_.GlobalTheory.ThetaCoefCont.continuous_coef D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG') K hK ?_ ?_
  · intro y hy
    by_contra hne
    apply hy
    refine hKmem y fun u hu hu0 => ?_
    by_contra h1
    exact hne (hvan _ u hu hu0 h1)
  · refine _root_.GlobalTheory.DecayCoord.decay_real_coords D V W a b P Q hP hQ θ hθ _ fun τ z m => ?_
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.ThetaDecay.coef_decay D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
    exact ⟨C, fun y => hC _⟩

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteIndicatorSmulArchFunction
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrProdInt

theorem integral_indicator_smul_of_measurePreserving {X Y Z E : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X} {m : Measure Y} {ν : Measure Z}
    [SigmaFinite m] [SigmaFinite ν] (e : X ≃ᵐ Y × Z) (he : MeasurePreserving e μ (m.prod ν)) {B : Set Z}
    (hB : MeasurableSet B) (hBf : ν B ≠ ⊤) {a : Y → E} (ha : Integrable a m) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) μ ∧
      ∫ x, B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1 ∂μ = (ν B).toReal • ∫ y, a y ∂m := by
  set Φ : Y × Z → E := (univ ×ˢ B).indicator (fun p => a p.1) with hΦdef
  have hΦ : (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) = Φ ∘ e := by
    funext x
    rw [Function.comp_apply, hΦdef]
    by_cases h : (e x).2 ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, h⟩), one_smul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm => h (Set.mem_prod.1 hm).2), zero_smul]
  have hmeasS : MeasurableSet (univ ×ˢ B : Set (Y × Z)) := MeasurableSet.univ.prod hB
  have hres : (m.prod ν).restrict (univ ×ˢ B) = m.prod (ν.restrict B) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hBf.lt_top⟩
  have hint : Integrable Φ (m.prod ν) := by
    rw [hΦdef, integrable_indicator_iff hmeasS, IntegrableOn, hres]
    exact ha.comp_fst _
  have hval : ∫ p, Φ p ∂(m.prod ν) = (ν B).toReal • ∫ y, a y ∂m := by
    rw [hΦdef, integral_indicator hmeasS, hres, integral_fun_fst]
    simp [Measure.real]
  rw [hΦ]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).2 hint, ?_⟩
  rw [show (∫ x, (Φ ∘ e) x ∂μ) = ∫ x, Φ (e x) ∂μ from rfl, he.integral_comp' Φ]
  exact hval

theorem integral_indicatorFin_smul_arch : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  intro D V μa μf μ hμ νF hF E _ _ _ B hB hBf a ha
  haveI := SelfDual.isLattice_frameLat V
  have hmap := hμ.map_archFin hF
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.1
  haveI : νF.IsHaarMeasure := hF.2.2.1
  haveI : ∀ w, SigmaFinite (μa w) := fun w => inferInstance
  haveI : SigmaFinite (Measure.pi μa) := Measure.pi.sigmaFinite _
  haveI : SigmaFinite νF := inferInstance
  exact integral_indicator_smul_of_measurePreserving
    (archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv
    ⟨(archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv.measurable, hmap⟩ hB hBf ha

end GlobalTheory.TrProdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.UnderConj
open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem isConjPl_of_under_eq_of_ne : ∀ (D : D7) (PP PP' : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') →
    PP ≠ PP' → Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro D PP PP' hu hne
  have key : PP' = conjSpec PP := by
    by_contra hc
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (Q := PP') (P := PP) (P' := conjSpec PP) (Ne.symm hne) hc
    have hfix : star ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ha]
      exact (x * Formalism.L2.Col.cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext ha
    have h1 : (⟨a, hint⟩ : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP'.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hu] at h1
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal at h1
    rw [e] at h1
    rcases PP.isPrime.mem_or_mem h1 with h | h
    · exact hx1 h
    · exact hx2 h
  rw [key]
  exact GlobalTheory.LevelPlaces.isConjPl_conjSpec PP

end GlobalTheory.UnderConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsParabolicIsotropicFlagStabilizerSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SplitFlag.isParabRad_parAt : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  intro D V v s 𝔉
  obtain ⟨d, hd, g₀, hg₀⟩ := _root_.GlobalTheory.Flag.exists_gl_adapted_chain (GlobalTheory.SplitFlag.flagChain 𝔉 s.emb) (GlobalTheory.SplitFlag.flagChain_mono _ _)
    (GlobalTheory.SplitFlag.flagChain_zero _ _) (GlobalTheory.SplitFlag.flagChain_last _ _ s.cm)
  obtain ⟨hP, hN⟩ := _root_.GlobalTheory.StdChainStab.stdChain_stab_rad _ d hd g₀ hg₀
  have key : ∀ x : GL (Fin V.rank) (Fv D.host.F v),
      splitHom D.sp.cm.sig V.gram s.emb (s.equiv.symm x) = s.basis * x * s.basis⁻¹ := fun x =>
    splitHom_splitEquivIn_symm s.cm s.herm s.emb s.basis x
  have hmap : ∀ (H : Subgroup (GLoc D.sp.cm.sig V.gram v)) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ H.map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v)) ↔ s.equiv.symm x ∈ H :=
    fun H x => ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hx => ⟨_, hx, s.equiv.apply_symm_apply x⟩⟩
  have hconj : ∀ (H : Subgroup (GL (Fin V.rank) (Fv D.host.F v))) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy (s.basis⁻¹ * g₀) H ↔ s.basis * x * s.basis⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g₀ H := by
    intro H x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨2 * 𝔉.k + 1, d, hd, s.basis⁻¹ * g₀, ?_, ?_⟩
  · ext x
    rw [parAt, hmap, _root_.GlobalTheory.SplitFlag.mem_par_iff_flagChain D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hP]
  · ext x
    rw [hmap, _root_.GlobalTheory.SplitFlag.mem_unip_iff_flagChain D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hN]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZero
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer

open GlobalTheory.Orb

namespace GlobalTheory.RegSupp

theorem mem_iwahori_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    {g : GL (Fin n) (Fv F v)} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n) → g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.iwahori (Fv F v) n := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  intro hg
  haveI hc : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he : (ValuativeRel.valuation (Fv F v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hle : (ValuativeRel.valuation (Fv F v)).integer ≤ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.Int (Fv F v) :=
    fun x hx => he.le_one_iff_le_one.1 hx
  refine Subgroup.mem_map.2 ⟨Matrix.GeneralLinearGroup.map (Subring.inclusion hle) h, ?_, ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff]
    intro i j hij
    have hb := (Subgroup.mem_comap.1 hh) (i := i) (j := j) (by
      rw [show i = (GlobalTheory.SmGL.points (Fin n)) ⟨i, ()⟩ from rfl, show j = (GlobalTheory.SmGL.points (Fin n)) ⟨j, ()⟩ from rfl,
        GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
      exact hij)
    change IsLocalRing.residue _ (h.1 i j) = 0 at hb
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers _).isUnit_iff_valuation_eq_one] at hb
    have h1 : ValuativeRel.valuation (Fv F v) ((h.1 i j : _) : Fv F v) < 1 :=
      lt_of_le_of_ne (h.1 i j).2 hb
    exact he.lt_one_iff_lt_one.1 h1
  · ext i j
    rfl

end GlobalTheory.RegSupp

namespace GlobalTheory.RegSupp

theorem isRegSS_of_tensor_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  intro hI D V T U μf ff hT fa δ x h
  obtain ⟨-, -, ⟨t, ht, hfu⟩, -, hcof⟩ := hT
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  have hfin : (Function.mulSupport fun v =>
      ff v (proj D.sp.cm.sig V.gram v (x⁻¹ * rat V δ * x))).Finite :=
    Filter.eventually_cofinite.1 ((hcof.and (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V)
      (x⁻¹ * rat V δ * x))).mono fun v hv => by
        show ff v _ = 1
        rw [hv.1, unitLoc, Set.indicator_of_mem hv.2, Pi.one_apply])
  have hne : ff U.u (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) ≠ 0 := by
    intro h0
    apply h
    show (∏ w, fa w (projArch D.sp.cm.sig V.gram w _)) * ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v _) = 0
    rw [finprod_eq_zero _ U.u h0 hfin, mul_zero]
  rw [hfu] at hne
  have hmem := Set.mem_of_indicator_ne_zero hne
  obtain ⟨A, hA, rfl⟩ := ht
  obtain ⟨a, ha, b, hb, e⟩ := U.frame.mem_iwahoriCoset.1 hmem
  have key := (hI _ (U.ϖ : Fv _ U.u) U.unif _ A hA
    (U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x))).1
    ⟨a, mem_iwahori_valued U.u ha, b, mem_iwahori_valued U.u hb, by
      rw [e, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT]
      congr 2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.diagPow
      congr 1
      funext i
      exact Units.val_zpow_eq_zpow_val _ _⟩).2
  have e1 : U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) =
      (U.frame.equiv (proj D.sp.cm.sig V.gram U.u x))⁻¹ * U.frame.equiv (proj D.sp.cm.sig V.gram U.u (rat V δ)) *
        U.frame.equiv (proj D.sp.cm.sig V.gram U.u x) := by
    simp only [map_mul, map_inv]
  rw [e1, charpoly_conj_GL] at key
  change (splitEquivIn _ _ U.frame.emb U.frame.basis _).1.charpoly.Separable at key
  rw [splitEquivIn_apply, charpoly_conj_GL, splitHom_val, rat, proj_ratEmb,
    show (matHom _ D.sp.cm.sig V.gram (ratLoc D.sp.cm.sig V.gram U.u δ)).1 = δ.1.1.map (inclR _) from rfl,
    Matrix.map_map, show (splitProj U.frame.emb) ∘ (inclR (Fv _ U.u)) = (U.frame.emb : _ →+* Fv _ U.u) from
      funext (splitProj_inclR _), Matrix.charpoly_map] at key
  exact (Polynomial.separable_map _).1 key

end GlobalTheory.RegSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicFormMultMapValue
section
noncomputable section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S GlobalTheory.SmVec GlobalTheory.MultGelf Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivValues

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def IsEquivMap (θ : InfFam D) (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)

def IsSobValued (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ : InfFam D} {M : DSModel V S} {T : MMap M}

theorem rder_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hC τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := _root_.GlobalTheory.SmVec.sobCont_repr _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (_root_.GlobalTheory.SmVecDeriv.hasDerivAt_word _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hE hC τ v Z w _ rfl

theorem gelf_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ)) :
    gelf θ V τ k (T v) = T (Function.update v τ w) := by
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem gelf_eigen (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) :
    ∃ c : ℂ, gelf θ V τ k (T v) = c • T v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ)
    (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k
  refine ⟨c, ?_⟩
  have hv := hc _ ((mem_sm M τ).1 (v τ).2)
  rw [gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]
  have := T.map_update_smul v τ c (v τ)
  rw [Function.update_eq_self] at this
  exact this

theorem zfin (hθ : IsInfFam θ) (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (v : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T v ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_eigen hE hC τ k v
  rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem isAutFunSm : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  intro _ D θ hθ V S M T U N hU hT hE hC v
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT v
  exact GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩)
    ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)

end GlobalTheory.EquivValues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedFnConjLocFinEqOne
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
end

