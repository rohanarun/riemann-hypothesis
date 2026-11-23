module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0402
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegel
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbeddingOfExponent
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.GlFrob


set_option maxHeartbeats 1000000 in
theorem embedding_of_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (hd1 : ∑ _a : Fin n, 1 = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsAdmissible π → π.IsIrreducible → ∀ (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ a, IsSmoothChar (ξ a)) (hd : ∑ a, (IrrGL.ofChar (ξ a) (hξ a)).1 = n), (∃ v : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), v ≠ 0 ∧ ∀ t : Levi k (fun _ : Fin n => Fin 1), v ∈ Module.End.maxGenEigenspace (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π t) (PositivityTheory.Lbc.torusChar ξ t)) → ∃ f : π.IntertwiningMap (prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd), Function.Injective f := by
  intro k _ _ _ _ _ n hd1 V _ _ π hs ha hirr ξ hξ hd hv
  obtain ⟨v, hv0, hv⟩ := hv
  have h0 := GlobalTheory.CompanionTheory.KmIwahori.c0 k
  have h3 := GlobalTheory.CompanionTheory.Lbc.c3 k
  have hcomm : ∀ l l' : Levi k (fun _ : Fin n => Fin 1),
      GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l * GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' =
        GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l' * GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π l := by
    intro l l'
    rw [← map_mul, ← map_mul]
    congr 1
    funext a
    exact GlobalTheory.CompanionTheory.PinLift.gl_one_comm _ _
  obtain ⟨hanti, hpow⟩ := _root_.GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow (k := k) n hd1
  have hsm : ∀ w : Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)), ∃ m,
      ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
        GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π u w = w := by
    intro w
    obtain ⟨m, hm, h⟩ := _root_.GlobalTheory.CompanionTheory.JacSmooth.jac_fixed_of_smooth (k := k) n hd1 π hs w
    refine ⟨m - 1, ?_⟩
    rw [Nat.sub_add_cancel hm]
    exact h
  have hfd : ∀ m, FiniteDimensional ℂ ↥(⨅ u : PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1,
      LinearMap.ker (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1)) := by
    intro m
    haveI := _root_.GlobalTheory.CompanionTheory.Jacquet.finiteDimensional_fixed_jac (k := k) n hd1 π ha h0 h3 (m + 1) (by omega)
    refine Submodule.finiteDimensional_of_le (S₂ := fixed (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1)) ?_
    intro w hw u
    have h1 := (Submodule.mem_iInf _).1 hw u
    have h2 : (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) - 1) w = 0 := h1
    have h3' : GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π (u : Levi k (fun _ : Fin n => Fin 1)) w = w := by
      simpa [sub_eq_zero] using h2
    simpa using h3'
  obtain ⟨f, hf0, hf⟩ := _root_.GlobalTheory.CompanionTheory.TorusQuot.exists_quotient_character (Levi k (fun _ : Fin n => Fin 1))
    (Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd1)))
    (GlobalTheory.SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd1) π) hcomm
    (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd1) hanti hpow hsm hfd
    (GlobalTheory.CompanionTheory.PinLift.torusCharHom ξ) v hv0 hv
  obtain ⟨g, w, hg⟩ := _root_.GlobalTheory.CompanionTheory.CharTensor.chartotensor n π ξ hξ hd f hf0 hf
  obtain ⟨G, x, hx⟩ := GlobalTheory.CompanionTheory.FrobInv.exists_map_prodIrr (fun a => IrrGL.ofChar (ξ a) (hξ a)) hd π hs g ⟨w, hg⟩
  refine ⟨G, ?_⟩
  have hso : IsSimpleOrder (Subrepresentation π) := hirr
  have hk : ∀ y, y ∈ G.ker.toSubmodule ↔ G y = 0 := fun y => Iff.rfl
  rcases eq_bot_or_eq_top G.ker with h0' | h0'
  · refine (injective_iff_map_eq_zero G.toLinearMap).2 fun y hy => ?_
    have hy' : y ∈ G.ker.toSubmodule := (hk y).2 hy
    rw [h0'] at hy'
    exact (Submodule.mem_bot ℂ).1 hy'
  · refine absurd ((hk x).1 ?_) hx
    rw [h0']
    trivial

end GlobalTheory.CompanionTheory.GlFrob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductMeasureEventuallyStandard
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Euler

theorem pureN_eq_indicator {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n M : ℕ}
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureN φ A X = {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v}.indicator
        (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) X := by
  change φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) *
    (boxFN A).indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) = _
  by_cases hX : ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∈ boxFN A := hX
    rw [Set.indicator_of_mem (show X ∈ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_mem h1, mul_one]
  · have h1 : HeckeCharacterZeroLocus.SiegelWeilU.projFin X ∉ boxFN A := hX
    rw [Set.indicator_of_notMem (show X ∉ {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} from hX),
      Set.indicator_of_notMem h1, mul_zero]

theorem integrable_integral_pureN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ M n d b I c minf m hE
  obtain ⟨-, -, S₀, hS₀⟩ := hE
  refine ⟨S₀, fun S hS φ hφ hφi A hA hfin hoff => ?_⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hB := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurableSet_box b n M S A hA hoff
  have hp := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler.measurable_projInf (E := E) b n M
  set B : Set (Fin n → Fin M → AF F ⊗[F] E) :=
    {X | ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} with hBdef
  set P : ℝ := ∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal with hP
  have hP0 : 0 ≤ P := tprod_nonneg fun _ => ENNReal.toReal_nonneg
  set K : ℝ≥0∞ := (c : ℝ≥0∞) * (∏ v ∈ S, m v (A v)) * ENNReal.ofReal P with hK
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.prod_ne_top fun v _ => hfin v)) ENNReal.ofReal_ne_top
  have hmap : (I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf = K • minf := by
    ext T hT
    rw [Measure.map_apply hp hT, Measure.restrict_apply (hp hT), Measure.smul_apply, smul_eq_mul]
    have hform := hS₀ S hS (T.indicator 1) (fun v => (A v).indicator 1)
      (measurable_one.indicator hT) (fun v => measurable_one.indicator (hA v))
    simp_rw [GlobalTheory.CompanionTheory.SW.EulerBox.pureL_indicator_eq b S _ A hoff] at hform
    rw [lintegral_indicator hB, lintegral_indicator_one hT] at hform
    have hl : ∫⁻ X in B, T.indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) ∂I =
        I (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T ∩ B) := by
      have : (fun X => T.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) =
          (HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T).indicator 1 := by
        funext X
        by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projInf X ∈ T
        · rw [Set.indicator_of_mem h,
            Set.indicator_of_mem (show X ∈ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
          rfl
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (show X ∉ HeckeCharacterZeroLocus.SiegelWeilU.projInf ⁻¹' T from h)]
      rw [this, lintegral_indicator_one (hp hT), Measure.restrict_apply (hp hT)]
    rw [hl] at hform
    change _ = _ * _ * ENNReal.ofReal P at hform
    rw [hform]
    simp_rw [lintegral_indicator_one (hA _)]
    rw [hK]; ring
  have hfun : pureN φ A = B.indicator (fun X => φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf X)) :=
    funext fun X => pureN_eq_indicator φ A X
  refine ⟨?_, ?_⟩
  · have h1 : Integrable φ ((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [hmap]; exact hφi.smul_measure hKtop
    have h2 := (integrable_map_measure hφ.aestronglyMeasurable hp.aemeasurable).1 h1
    rw [hfun]
    exact IntegrableOn.integrable_indicator h2 hB
  · have h1 : ∫ X, pureN φ A X ∂I = ∫ Y, φ Y ∂((I.restrict B).map HeckeCharacterZeroLocus.SiegelWeilU.projInf) := by
      rw [integral_map hp.aemeasurable hφ.aestronglyMeasurable, hfun]
      exact integral_indicator hB
    rw [h1, hmap, integral_smul_measure]
    have hKr : K.toReal = (c : ℝ) * (∏ v ∈ S, (m v (A v)).toReal) * P := by
      rw [hK, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hP0]
      simp
    rw [hKr, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SiegelND.Coef.Euler
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

theorem latS_isOpen_isCompact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  intro E _ _ _ S B hO hI
  have hc : ∀ w : Pl E, Continuous (pLoc E w) := fun w => RestrictedProduct.continuous_eval w
  have heq : (latS S B : Set (Af E)) =
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∩
        ⋂ w ∈ S, (pLoc E w) ⁻¹' (B w : Set (w.adicCompletion E)) := by
    ext a
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨GroundTheory.Global.mem_integralFiniteAdeles.2 fun w => ?_, ?_⟩
      · by_cases hw : w ∈ S
        · exact hI w hw (h2 w hw)
        · exact h1 w hw
      · exact Set.mem_iInter₂.2 fun w hw => h2 w hw
    · rintro ⟨h1, h2⟩
      exact ⟨fun w _ => GroundTheory.Global.mem_integralFiniteAdeles.1 h1 w,
        fun w hw => Set.mem_iInter₂.1 h2 w hw⟩
  rw [heq]
  constructor
  · exact GroundTheory.Global.isOpen_integralFiniteAdeles.inter
      (isOpen_biInter_finset fun w hw => (hO w hw).preimage (hc w))
  · refine (GroundTheory.Global.isCompact_integralFiniteAdeles E).inter_right ?_
    refine isClosed_biInter fun w hw => IsClosed.preimage (hc w) ?_
    exact AddSubgroup.isClosed_of_isOpen (B w) (hO w hw)

end GlobalTheory.CompanionTheory.CutOff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimStableSubspace
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.IrredMod

theorem exists_finiteDimensional_zalg_lie_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a),
      FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧
      ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  intro E _ _ _ a W hW hA φ hφ

  let S₀ : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have hS₀fd : FiniteDimensional ℂ S₀ := (hA φ hφ).kfin
  have hS₀W : S₀ ≤ W := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hW (.cpt k) φ hφ)
  have hS₀K : ∀ k, ∀ ψ ∈ S₀, cptRep E a k ψ ∈ S₀ := by
    intro k ψ hψ
    have hle : S₀ ≤ S₀.comap (cptRep E a k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    exact hle hψ
  have hS₀L : ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ ψ ∈ S₀, lie E a X ψ ∈ S₀ :=
    fun X hX ψ hψ => _root_.GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable E a S₀ hS₀fd hS₀K X hX ψ hψ
  have hφS₀ : φ ∈ S₀ := Submodule.subset_span ⟨1, by simp⟩

  let Y : Submodule ℂ (Sm E a) := Submodule.span ℂ
    (Set.image2 (fun (z : Module.End ℂ (Sm E a)) (s : Sm E a) => z s) (Zalg E a : Set (Module.End ℂ (Sm E a))) S₀)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S₀).2 hS₀fd
  let Zs : Sm E a → Submodule ℂ (Sm E a) := fun s =>
    Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z s) '' Zalg E a)
  have hts : ∀ s ∈ t, s ∈ S₀ := fun s hs => ht ▸ Submodule.subset_span hs
  have hZfd : ∀ s : t, FiniteDimensional ℂ (Zs s.1) := fun s => (hA s.1 (hS₀W (hts s.1 s.2))).zfin
  let T : Submodule ℂ (Sm E a) := ⨆ s : t, Zs s.1
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_iSup _
  have hYT : Y ≤ T := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, s, hs, rfl⟩
    have hle : S₀ ≤ T.comap z := by
      rw [← ht]
      refine Submodule.span_le.2 fun u hu => ?_
      exact Submodule.mem_iSup_of_mem (⟨u, hu⟩ : t) (Submodule.subset_span ⟨z, hz, rfl⟩)
    exact hle hs)
  have hWlie : ∀ X, ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ hψ => hW (.lie X) ψ hψ
  refine ⟨Y, Submodule.finiteDimensional_of_le hYT, Submodule.span_le.2 ?_, Submodule.subset_span
    ⟨1, (Zalg E a).one_mem, φ, hφS₀, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, s, hs, rfl⟩
    exact Zalg_stable hWlie hz s (hS₀W hs)
  · intro z hz y hy
    have hle : Y ≤ Y.comap z := Submodule.span_le.2 (by
      rintro _ ⟨z', hz', s, hs, rfl⟩
      exact Submodule.subset_span ⟨z * z', (Zalg E a).mul_mem hz hz', s, hs, rfl⟩)
    exact hle hy
  · intro X hX y hy
    have hle : Y ≤ Y.comap (lie E a X) := Submodule.span_le.2 (by
      rintro _ ⟨z, hz, s, hs, rfl⟩
      have e : lie E a X (z s) = z (lie E a X s) :=
        (LinearMap.congr_fun (GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a z hz X) s).symm
      change lie E a X (z s) ∈ Y
      rw [e]
      exact Submodule.subset_span ⟨z, hz, _, hS₀L X hX s hs, rfl⟩)
    exact hle hy

end GlobalTheory.CompanionTheory.IrredMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsSiegelStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_points_siegel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q' : Set (GA E N)) (ω : Set (GA E N)) (t₀ : ℝ)
  (Q : Set (GA E N)), IsCompact Q' → IsCompact ω → ω ⊆ (adelicBorel (K := E) (n := N) : Set _) → IsCompact Q → ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin N → ℝ,
    (∀ r, -t₀ ≤ An.sr x r) → ∀ q ∈ Q,
    {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ Q', ∃ a' ∈ Q', γ = (b * An.tor E x * q) * a * a'⁻¹ * (b * An.tor E x * q)⁻¹}.encard ≤
      (⌈C * Real.exp (M * ∑ r ∈ Finset.range N, An.sr x r)⌉₊ : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | exact GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel | (intros; apply GlobalTheory.CompanionTheory.ConcCount.count_conj_siegel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitQuot

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem twKer_subQuot {ρ : Representation ℂ G V} (A B : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ) :
    twKer (subQuot A B) U χ =
      (twKer A.toRepresentation U χ).map (B.toSubmodule.comap A.toSubmodule.subtype).mkQ := by
  have key : ∀ (g : G) (v : A.toSubmodule),
      (subQuot A B) g ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ (A.toRepresentation g v) := fun _ _ => rfl
  unfold twKer
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := (B.toSubmodule.comap A.toSubmodule.subtype).mkQ_surjective w
    have h : (subQuot A B) n ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) -
          ((χ n : ℂˣ) : ℂ) • (B.toSubmodule.comap A.toSubmodule.subtype).mkQ v =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ
          (A.toRepresentation n v - ((χ n : ℂˣ) : ℂ) • v) := by
      rw [key, map_sub, map_smul]
    rw [h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, v, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← key]
    exact Submodule.subset_span ⟨n, _, rfl⟩

theorem coe_mem_twKer {ρ : Representation ℂ G V} (A : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ)
    {x : A.toSubmodule} (hx : x ∈ twKer A.toRepresentation U χ) : (x : V) ∈ twKer ρ U χ := by
  have h : twKer A.toRepresentation U χ ≤ (twKer ρ U χ).comap A.toSubmodule.subtype := by
    unfold twKer
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨n, v, rfl⟩
  exact h hx

end General

theorem isGenericFor_subQuot_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ A B hBA
  have hsm : IsSmooth A.toRepresentation := by
    intro v
    have h : {g : GL (Fin N) k | A.toRepresentation g v = v} = {g | ρ g (v : V) = v} :=
      Set.ext fun g => Subtype.ext_iff
    rw [h]
    exact hρ v
  show Nontrivial (_ ⧸ twKer (subQuot A B) (unipB k (Fin N)) (whitChar ψ N)) ↔ _
  rw [Submodule.Quotient.nontrivial_iff, twKer_subQuot, Ne, Submodule.map_mkQ_eq_top]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · intro v hv
    have hmem : (⟨v, hv⟩ : A.toSubmodule) ∈ B.toSubmodule.comap A.toSubmodule.subtype ⊔
        twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hv' : v = (y : V) + (z : V) := by rw [← Submodule.coe_add, hyz]
    rw [hv']
    exact Submodule.add_mem_sup hy (coe_mem_twKer A _ _ hz)
  · rw [eq_top_iff]
    rintro a -
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h a.2)
    have hyA : y ∈ A.toSubmodule := hBA hy
    have hzA : z ∈ A.toSubmodule := by
      have hz2 : z = (a : V) - y := by rw [← hyz]; abel
      rw [hz2]
      exact A.toSubmodule.sub_mem a.2 hyA
    have hz' : (⟨z, hzA⟩ : A.toSubmodule) ∈ twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) :=
      GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N A.toRepresentation ρ hsm hρ
        A.toSubmodule.subtype A.toSubmodule.injective_subtype (fun _ _ => rfl) _ hz
    have ha : a = ⟨y, hyA⟩ + ⟨z, hzA⟩ := Subtype.ext hyz.symm
    rw [ha]
    exact Submodule.add_mem_sup hy hz'

end GlobalTheory.CompanionTheory.PRep.WhitQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct ENNReal Matrix

section Loc

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def gramNear (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (U : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ u ∈ U, (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X = (u : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def gramTest (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (c : HermR R σ n) (ρ : HermR R σ n → ℝ)
    (X : Fin n → Fin M → R ⊗[F] E) : ℝ := by
  classical
  exact if h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n then ρ ⟨_, h⟩ else 0

end Loc

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {B | ∀ v, v ∉ S → projV v (projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ latV (M := n) (n := n) b v}

def coefS (σ : E →ₐ[F] E) {d M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ B, (intH σ b S).indicator (fun _ => (1 : ℂ)) B *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ B * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))) ∂db

end Adelic

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_function_continuous_pos' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x := by
  first | exact @GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | exact GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos | (intros; apply GlobalTheory.CompanionTheory.Iwasawa.height_continuous_pos <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)

noncomputable def rowInfEquiv : (Fin k → InfiniteAdeleRing E) ≃+ (Fin k → Cinf E) :=
  AddEquiv.piCongrRight fun _ => (infEq E).symm.toAddEquiv

theorem nuInf_isAddHaarMeasure : (nuInf E k).IsAddHaarMeasure := by
  have hc : Continuous (rowInfEquiv E k) :=
    continuous_pi fun i => (GASplit.continuous_infEq_symm E).comp (continuous_apply i)
  have hc' : Continuous (rowInfEquiv E k).symm :=
    continuous_pi fun i => (continuous_infEq E).comp (continuous_apply i)
  have hp : (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact AddEquiv.isAddHaarMeasure_map _ (rowInfEquiv E k) hc hc'

end GlobalTheory.CompanionTheory.CutOff
end

