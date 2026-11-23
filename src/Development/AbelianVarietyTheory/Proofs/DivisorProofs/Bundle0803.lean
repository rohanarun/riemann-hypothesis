module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0795

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolume
section
open MeasureTheory

namespace GlobalTheory.HaarFundDom

open scoped Pointwise

theorem exists_haar_fundDom_mass_one : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K →
    (∀ g : G, ∃ γ : Γ, γ • g ∈ K) →
    ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ _ _ Γ _ _ K hK hcov
  let μ₀ : Measure G := Measure.haar
  obtain ⟨𝓕, h𝓕m, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have hD : IsFundamentalDomain Γ 𝓕 μ₀ := IsFundamentalDomain.mk' h𝓕m.nullMeasurableSet h𝓕
  haveI : MeasurableMul G :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul Γ G :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : G => (γ : G) * x).measurable⟩
  haveI : SMulInvariantMeasure Γ G μ₀ := ⟨fun γ A _ => measure_preimage_mul μ₀ (γ : G) A⟩
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : 𝓕 ⊆ ⋃ γ : Γ, γ • K ∩ 𝓕 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set.2 ⟨γ • x, hγ, ?_⟩, hx⟩
    simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hfin : μ₀ 𝓕 < ⊤ :=
    calc μ₀ 𝓕 ≤ μ₀ (⋃ γ : Γ, γ • K ∩ 𝓕) := measure_mono hsub
      _ ≤ ∑' γ : Γ, μ₀ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ₀ K := (hD.measure_eq_tsum _).symm
      _ < ⊤ := hK.measure_lt_top
  have hne : μ₀ 𝓕 ≠ 0 := by
    intro h0
    have h1 := hD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter, measure_smul, h0, tsum_zero] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne μ₀)).ne' h1
  refine ⟨(μ₀ 𝓕)⁻¹ • μ₀, 𝓕, ?_, hD.mono Measure.smul_absolutelyContinuous, ?_⟩
  · exact Measure.IsHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hne)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hne hfin.ne]

end GlobalTheory.HaarFundDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
section
namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateVacuumEntireGaussianGrowth
section
namespace GlobalTheory.ConjTranslate

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem mem_Th (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _
    (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hg cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  obtain ⟨hg, hperm⟩ := GlobalTheory.InducedType.induced_type D
  have hGT := mem_Th D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1
    hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hperm Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hg cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y
    (2 * m) hy (by omega)
  have hgal := (GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1)
    (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
    (by rw [comb_one]; exact hAU y hy)).1
  rw [comb_one] at hgal
  rw [hgal]
  refine ⟨U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1, U_ne_zero D _ _ _ hne, fun z => ?_⟩
  have := sup_perm D hg cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
    hTh y' z
  rw [Hf_re, ← mul_div_assoc] at this
  exact this

theorem conj_any (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata
  · exact conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy ρ hfix
  · obtain ⟨hd, hne, hle⟩ := conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy
      (rhoBar Qbar ρ) hfix
    obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ
      hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [(hbar a d L L' G).1, htor, hn2, hL, area_conj] at hle
    rw [(hbar a d L L' _).1] at hd hne hle
    refine ⟨?_, fun h => hne ?_, fun z => ?_⟩
    · have := GlobalTheory.ThetaConj.differentiable_cBar hd
      rwa [GlobalTheory.ThetaConj.cBar_cBar] at this
    · rw [h]
      funext z
      simp [cBar]
    · have := hle (vBar D z)
      rw [cBar, GlobalTheory.ThetaConj.vBar_invol] at this
      simpa only [vBar, Complex.norm_conj] using this

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem conj_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  intro D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  obtain ⟨-, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨hd, hne, hle⟩ := conj_any D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  exact ⟨GlobalTheory.ConjJet.U_diff D _ y F (mem_Th D cc dl t0 hc ht a b L L' h1 h2 F hF).1, hAU y hy,
    _, hd, (GlobalTheory.ConjSeries.taylor_fnConj D a b _ ρ _ hd hne).1, hle⟩

end GlobalTheory.ConjTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_thV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Continuous (thV ψ Φ) := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  have hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N =>
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    intro ξ
    refine Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))
    refine Continuous.add ?_ (continuous_const.mul ?_)
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    funext w
    simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
    rfl
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
  obtain ⟨c, hcs, hc0, hcb⟩ := hk (Prod.fst '' ω) (hωc.image continuous_fst)
  have hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_
    rw [norm_mul, hψn, one_mul]
    by_cases hmem : fin (rat ξ + w.1) ∈ K
    · have h1 := hcb ξ w.1 ⟨w, hw, rfl⟩ hmem
      have h2 := hC (rat ξ + w.1)
      calc ‖Φ (rat ξ + w.1)‖ = ‖Φ (rat ξ + w.1)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + w.1)‖ * (c ξ * (1 + sz (rat ξ + w.1)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + w.1)‖ * (1 + sz (rat ξ + w.1)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  exact hon.continuousAt hωn

end GlobalTheory.ThetaTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendPointValuationRingOfDominatingLocalDomain
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

theorem descend_point_to_valuationRing_of_dominating_local_domain : ∀ (V K W L : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [CommRing W] [IsDomain W] [IsLocalRing W] [Field L] [Algebra W L] [IsFractionRing W L] [Algebra V W] [Algebra K L], (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) → IsLocalHom (algebraMap V W) → ∀ (X : Scheme.{0}) (x : Sp K ⟶ X) (f : Sp W ⟶ X), spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x := by
  intro V K W L _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcomm hloc X x f hxf
  classical

  let c : Sp W := IsLocalRing.closedPoint W
  obtain ⟨U, hU, hcU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show f c ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hfU : ∀ a : Sp W, f a ∈ U := fun a =>
    ((IsLocalRing.specializes_closedPoint (R := W) a).map f.continuous).mem_open U.isOpen hcU
  have hrf : Set.range f ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    exact hfU a
  let pL : Sp L := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum L)
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have e := congrArg (fun h : Sp L ⟶ X => h pL) hxf
    simp only [Scheme.Hom.comp_apply] at e
    have ha : a = (spMap (algebraMap K L)) pL := by
      have h : ∀ c : PrimeSpectrum K, c.asIdeal = ⊥ := fun c => Ideal.eq_bot_of_prime c.asIdeal
      exact PrimeSpectrum.ext ((h a).trans (h _).symm)
    rw [ha, e]
    exact hfU _
  have hf₁ := IsOpenImmersion.lift_fac hU'.fromSpec f hrf
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec f hrf)] at hf₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set β := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec f hrf) with hβ
  set α := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hα
  have key : α ≫ CommRingCat.ofHom (algebraMap K L) = β ≫ CommRingCat.ofHom (algebraMap W L) := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc, hx₁, hf₁]
    exact hxf
  have key' : ∀ r, algebraMap K L (α.hom r) = algebraMap W L (β.hom r) := fun r => by
    have e := congrArg (fun h => h.hom r) key
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using e

  have hmem : ∀ r, α.hom r ∈ (algebraMap V K).range := by
    intro r
    by_cases h0 : α.hom r = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger V (α.hom r) with ⟨v, hv⟩ | ⟨b, hb⟩
    · exact ⟨v, hv⟩
    · by_cases hb0 : IsUnit b
      · obtain ⟨u, rfl⟩ := hb0
        refine ⟨((u⁻¹ : Vˣ) : V), ?_⟩
        rw [← inv_inv (α.hom r), ← hb]
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      · exfalso
        apply hb0
        apply (isUnit_map_iff (algebraMap V W) b).1
        refine isUnit_iff_exists_inv.2 ⟨β.hom r, ?_⟩
        apply IsFractionRing.injective W L
        rw [map_mul, map_one, ← key', ← RingHom.comp_apply, hcomm, RingHom.comp_apply, hb, ← map_mul,
          inv_mul_cancel₀ h0, map_one]
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h),
      (algebraMap V K).rangeRestrict_surjective⟩
  let χ : Γ(X, U) →+* V := e.symm.toRingHom.comp (α.hom.codRestrict _ hmem)
  have hχ : (algebraMap V K).comp χ = α.hom := by
    ext r
    change algebraMap V K (e.symm ⟨α.hom r, hmem r⟩) = α.hom r
    have := congrArg Subtype.val (e.apply_symm_apply ⟨α.hom r, hmem r⟩)
    exact this
  refine ⟨Spec.map (CommRingCat.ofHom χ : Γ(X, U) ⟶ CommRingCat.of V) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact congrArg (fun h => h r) hχ

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  first | (exact @GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (exact GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (intros; apply GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDim
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.OnMatGram

theorem norm_evalAt_intVec_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) (g : UN n) :
    ‖evalAt g.1 (map (Int.castRingHom ℂ) (intVec la j))‖ ≤ 1 := by
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j
  have hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
  rw [hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) =
      g.1.submatrix (I k) (Fin.castLE (hsz k)) := by
    ext p q
    simp
  rw [h]
  exact _root_.GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard.1 n (sz k) g (I k) (Fin.castLE (hsz k))

theorem normSq_basis_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    normSq la (basis la ℂ j).1 ≤ dim la := by
  refine normSq_le_dim fun g => ?_
  rw [coe_basis]
  exact norm_evalAt_intVec_le la j g

theorem sum_norm_sq_onMat {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    ∑ i, ‖onMat la i j‖ ^ 2 = normSq la (basis la ℂ j).1 := by
  rw [← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]
  rfl

theorem det_onMat_ne_zero {n : ℕ} (la : Fin n → ℕ) : (onMat la).det ≠ 0 := by
  let c : Module.Basis (Idx la) ℂ (Space la) := (basis la ℂ).map (toSpace la)
  have hc : onMat la = (onBasis la).toBasis.toMatrix c := by
    ext i j
    simp [onMat, c, Module.Basis.toMatrix_apply]
  rw [hc]
  exact (Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero

end GlobalTheory.OnMatGram

namespace GlobalTheory.OnMatGram

theorem norm_det_onMat_sq_le : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  intro n la _
  refine ⟨det_onMat_ne_zero la, ?_⟩
  refine (_root_.GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard.2 (Idx la) (onMat la)).trans ?_
  calc ∏ j, ∑ i, ‖onMat la i j‖ ^ 2 ≤ ∏ _j : Idx la, (dim la : ℝ) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (sum_norm_sq_onMat la j).trans_le (normSq_basis_le la j)
    _ = (dim la : ℝ) ^ dim la := by rw [Finset.prod_const, Finset.card_univ, ← dim_eq_card]

end GlobalTheory.OnMatGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamilyStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K), IsAdelic A → Submodule.IsFullLattice K (locLat A) := by
  first | exact @GlobalTheory.LocMatLat.isLattice_locLat | exact GlobalTheory.LocMatLat.isLattice_locLat | (intros; apply GlobalTheory.LocMatLat.isLattice_locLat <;> assumption)
end

