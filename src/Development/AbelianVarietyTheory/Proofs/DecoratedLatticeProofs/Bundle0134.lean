module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnitaryOrbitActionTransitiveWithStabilizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergTranslateThetaFunctionRealCoor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTranslate

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem hasDerivAt_expLine {H : ℝ → ℂ} {h' : ℂ} (hH : HasDerivAt H h' 0) (a k : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((a + s * k : ℝ) : ℂ)) * H s)
      (Complex.exp (-(Real.pi * Complex.I) * (a : ℂ)) * (-(Real.pi * Complex.I) * (k : ℂ) * H 0 + h')) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => a + s * k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : HasDerivAt (fun s : ℝ => ((a + s * k : ℝ) : ℂ)) (k : ℂ) 0 := h1.ofReal_comp
  have h3 := ((h2.const_mul (-(Real.pi * Complex.I))).cexp).mul hH
  exact h3.congr_deriv (by simp only [zero_mul, add_zero]; ring)

theorem contDiff_heisO_iota_fderiv : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ v : WO S T, ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) ∧ ∀ z u : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) z u = (Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T z u : ℝ) : ℂ) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v + heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) (fun y => deriv (fun s : ℝ => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (s • u)) F y) 0) v := by
  intro D θ σ h ψ hψ S T F hF v
  have hG : ContDiff ℝ ∞ fun x : RW T S => F (v + iotaW σ T S x) := theta_sm h hF v
  have eg : (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) = fun z =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (omO S T (piW θ T S v) z))) *
        F (v + iotaW σ T S z) := by
    funext z; rw [heisO_iota h hψ]; rfl
  have hsm : ContDiff ℝ ∞ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) := by
    rw [eg]
    exact (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (LinearMap.toContinuousLinearMap (omO S T (piW θ T S v))).contDiff))).mul hG
  refine ⟨hsm, fun z u => ?_⟩
  have hHc : ContDiff ℝ ∞ fun x : RW T S => F ((v + iotaW σ T S z) + iotaW σ T S x) := theta_sm h hF _
  have hH : HasDerivAt (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u)))
      (deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0) 0 :=
    ((hHc.comp (contDiff_id.smul contDiff_const)).differentiable (by simp) 0).hasDerivAt
  have hline : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eline : (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z + s * omO S T (piW θ T S v) u : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (omO S T (piW θ T S v)).map_add, LinearMap.map_smul, smul_eq_mul, (iotaW σ T S).map_add,
        add_assoc]
    rw [eline]
    exact hasDerivAt_expLine hH _ _
  have hf : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z u) 0 := by
    have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v)
        (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z) (z + (0 : ℝ) • u) := by
      rw [zero_smul, add_zero]; exact (hsm.differentiable (by simp) z).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    exact hd.comp_hasDerivAt (0 : ℝ) hl
  have hF' : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z))
      (Complex.exp (-(Real.pi * Complex.I) * ((0 : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u + omO S T z u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eF : (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z)) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) *
          ((0 + s * (omO S T (piW θ T S v) u + omO S T z u) : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (piW θ T S).map_add, h.pi_iota, LinearMap.map_smul, smul_eq_mul, (omO S T).map_add,
        LinearMap.add_apply, zero_add]
    rw [eF]
    exact hasDerivAt_expLine hH _ _
  rw [hf.unique hline, heisO_iota h hψ z F v, heisO_iota h hψ z _ v]
  beta_reduce
  rw [hF'.deriv]
  simp only [zero_smul, map_zero, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_add]
  ring

end GlobalTheory.ThetaTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralValueNeOneOfGramNe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem gramSkew_rat {D : D7} (W : HSp D) {ρ : ℕ} (y : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y) = rat ((-D.host.xi0) • (gramQ W y)ᵀ) := by
  have e : adj (rat y) ⬝ (gA W ⬝ rat y) = rat (gramQ W y) := by
    rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, e, rat_smul, map_neg]
  rfl

theorem gramQ_eq_of_gramSkew {D : D7} (W : HSp D) {ρ : ℕ} {x y : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y)) : gramQ W x = gramQ W y := by
  rw [gramSkew_rat, gramSkew_rat] at h
  have h' := rat_injective h
  have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D))
  exact Matrix.transpose_injective (smul_right_injective _ hξ h')

theorem exists_central_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  intro D ψ hψ V V₀ W ρ d x₀ x hne
  by_contra hcon
  push_neg at hcon
  have hall : ∀ c : skewA D ρ, ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) := by
    intro c
    have hn : ‖ψ (d.qS W c (rat x₀))‖ = 1 := hψ.1.2.1 _
    have hs : ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    calc ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) := by
          rw [hs, one_mul]
      _ = ψ (d.qS W c (rat x₀)) := by rw [mul_assoc, hcon c, mul_one]
  have h := (((_root_.GlobalTheory.CentralGram.central D).1 V V₀ W ρ d).2.2 ψ hψ).2.2 (rat x) (rat_mem x) (rat x₀) (rat_mem x₀)
  exact hne (gramQ_eq_of_gramSkew W (h.1 hall))

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX * b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := GlobalTheory.IwaFlag.exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2)
      (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol (z : Fin S.rank → D.host.E) (hz : ∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) :
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := by
    have hscale : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [hscale]
    exact hmul _ fun l => GlobalTheory.IwaFlag.mul_incA_mem hεI (hz l)
  have hflag := GlobalTheory.IwaFlag.exists_flag_dual_matrix
    (c := cA D) (O := GlobalTheory.IwaFlag.intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1)
    (fun _ ha _ hb => GlobalTheory.IwaFlag.mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]),
      (FrameLat.cA_int_iff a).2 ha.2⟩)
    (GlobalTheory.IwaFlag.princ_intGrpAt hεε hεc hεI hε ht)
    (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := hflag
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentFundamentalDomainLayersIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf


set_option maxHeartbeats 1000000 in
theorem layers_integral : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ), ∃ 𝓐 : Set (flagN d), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν ∧ ∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν := by
  intro D V V₀ ρ d vN vb vU
  obtain ⟨e, he⟩ := _root_.GlobalTheory.Unf.flagCoord_measEquiv D V V₀ ρ d
  obtain ⟨lC, 𝓒, hH, hS, hF, h1⟩ := GlobalTheory.T.exists_haar_covolume_one_skewHermitian_adelic D ρ
  obtain ⟨sb, su⟩ := _root_.GlobalTheory.Unf.sFinite_vol D ρ V₀.rank vb vU
  have hν := _root_.GlobalTheory.HaarCoordsUnit.volN_eq_map_coords D V V₀ ρ d vN vb vU e he lC 𝓒 hH hS hF h1
  refine ⟨e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), ?_, ?_⟩
  · rw [hν]; exact GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers D V V₀ ρ d e he lC 𝓒 hH hS hF vb vU.ν sb su
  · intro f hf hinv
    have hg : Measurable fun p => f (e p : GA D V) := hf.comp (measurable_subtype_coe.comp e.measurable)
    let g : Mx D ρ V₀.rank × UX D ρ → ENNReal := fun q => f (e (0, q) : GA D V)
    have hgm : Measurable g := hg.comp (measurable_const.prodMk measurable_id)
    have hge : ∀ q, g q = f (d.nB q.1 * d.levi q.2.1) := fun q => by
      show f (e (0, q) : GA D V) = _
      rw [he, d.nC_zero, one_mul]
    have hpt : ∀ p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ), f (e p : GA D V) = g p.2 := fun p => by
      have hm : (e (0, p.2) : GA D V) ∈ flagN d := (e (0, p.2)).2
      rw [he, d.nC_zero, one_mul] at hm
      rw [hge, he, hinv _ _ hm]
    have s1 : ∫⁻ n in e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), f n.1 ∂((lC.prod (vb.μ.prod vU.ν)).map e) =
        ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) := by
      rw [e.restrict_map, lintegral_map_equiv, e.preimage_image]
    have s2 : (lC.prod (vb.μ.prod vU.ν)).restrict (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)) = (lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) :=
      (Measure.prod_restrict 𝓒 (vb.𝓕 ×ˢ Set.univ)).symm
    have s3 : (vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ) = (vb.μ.restrict vb.𝓕).prod vU.ν := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have s4 : ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) =
        ∫⁻ q, g q ∂((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) := by
      rw [lintegral_prod (fun p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) => g p.2) (hgm.comp measurable_snd).aemeasurable]
      show ∫⁻ _ in 𝓒, (∫⁻ y in vb.𝓕 ×ˢ Set.univ, g y ∂(vb.μ.prod vU.ν)) ∂lC = _
      rw [lintegral_const, Measure.restrict_apply_univ, h1, mul_one]
    have s5 : ∫⁻ q, g q ∂((vb.μ.restrict vb.𝓕).prod vU.ν) = ∫⁻ u, ∫⁻ b in vb.𝓕, g (b, u) ∂vb.μ ∂vU.ν := by
      rw [lintegral_prod _ hgm.aemeasurable]
      exact lintegral_lintegral_swap (f := fun b u => g (b, u)) hgm.aemeasurable
    have s6 : ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) =
        ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) := by
      rw [s2]; exact lintegral_congr fun p => hpt p
    rw [hν]
    refine s1.trans (s6.trans (s4.trans ?_))
    rw [s3]
    refine s5.trans ?_
    exact lintegral_congr fun u => lintegral_congr fun b => hge (b, u)

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnitaryOrbitActionTransitiveWithStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer : ∀ (D : D7) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : IsBase W x₀), ∃ (_ : MulAction ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀)) (y₀ : Orb W x₀), y₀.1 = x₀ ∧ (∀ (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀), (rat (γ • x).1 : Mx D W.rank ρ) * blockX d γ.1.1.1 = mt W γ.1.2 * rat x.1) ∧ (∀ x : Orb W x₀, ∃ γ : (NFlagQ V d.e).prod (GQ W), γ • y₀ = x) ∧ ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).comap (MonoidHom.inl _ _) = (GQ V ⊓ radX d).subgroupOf (flagN d) ∧ ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).map (MonoidHom.snd _ _) = GQ W ⊓ Rgrp W (rat x₀) := by
  first | exact @GlobalTheory.OrbAct.action_transitive_stabiliser | exact GlobalTheory.OrbAct.action_transitive_stabiliser | (intros; apply GlobalTheory.OrbAct.action_transitive_stabiliser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

def eLast (D : D7) (ρ : ℕ) : Fin ρ → D.host.E := fun i => if i.1 + 1 = ρ then 1 else 0

theorem ratV_eLast (ρ : ℕ) : ratV (eLast D ρ) = ell D ρ := by
  funext i
  simp only [ratV, eLast, ell]
  split_ifs <;> simp

def zlQ (B : BesLev D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (eLast D (σ + 1))

theorem rat_zlQ (B : BesLev D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zl B := by
  rw [zl, zEll, ← ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem rat_gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    (rat (gramQ W x) : Mx D ρ ρ) = adj (rat x) ⬝ (gA W ⬝ rat x) := by
  rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem gramQ_eq_of_gramSkew {W W' : HSp D} {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E)
    (x' : Matrix (Fin W'.rank) (Fin ρ) D.host.E)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x : Mx D W.rank ρ) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W' (rat x')) :
    gramQ W x = gramQ W' x' := by
  have hu : IsUnit (-incA D D.host.xi0) :=
    ((isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map (incA D)).neg
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew at h
  rw [hu.smul_left_cancel, Matrix.transpose_inj] at h
  apply rat_injective
  rw [rat_gramQ, rat_gramQ, h]

theorem pairS_mul (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (c : Mx D ρ ρ) :
    pairS T x (x ⬝ c) = (adj c ⬝ (adj x ⬝ (gA T ⬝ x))).trace := by
  rw [pairS, adj_mul, Matrix.mul_assoc]

theorem gramQ_zlQ_mulVec_last (B : BesLev D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply, eLast,
    Pi.star_apply, Fin.val_last]
  simp only [if_true, mul_one, star_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, if_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E,
    (rat x₀ : Mx D B.V.rank (σ + 1)) = x0 B ∧ IsBase B.V x₀ ∧
    Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧
    (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧
    ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (x0 B) = d.qS B.L c (zl B) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := _root_.GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (x0 B) ⬝ (gA B.V ⬝ x0 B) = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by
    rw [← hx, ← rat_zlQ, ← rat_gramQ, ← rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [rat_gramQ, hx, hA, ]
    have hz : zl B ⬝ u.1 = zl B := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zl B) ⬝ (gA B.L ⬝ zl B) ⬝ u.1) = adj (zl B ⬝ u.1) ⬝ (gA B.L ⬝ (zl B ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zl B) ⬝ (gA B.L ⬝ zl B) := by rw [hz]
  · ext g
    rw [hx]
    exact ((_root_.GlobalTheory.Unf.FB.besselGroup_action_fourierBesselBasePoint D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, pairS_mul, pairS_mul, hA]

end GlobalTheory.Unf.FB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCover
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_hasParam_of_group : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q : ℕ), 1 ≤ p + q → ∀ (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ),
      IsParam lam → HasParam R lam → HasTypes R lam := by
  intro hL hK hD p q hpq T R lam hlam hR
  have hn : 0 < p + q := hpq
  obtain ⟨P, e, -, hB, hcase⟩ := isParam_cases hlam
  rcases hcase with rfl | rfl
  · obtain ⟨σ, hf, hds⟩ := (hasParam_iff_factors R hn P hB).1 hR
    exact _root_.GlobalTheory.CoverDS.hasTypes_of_factors hL hK hD p q (p + q) e P T R σ hB hf hds
  · obtain ⟨σ, hπ, hds⟩ := (hasParam_half_iff R hn P hB).1 hR
    have hf : Factors (Cover.twist R).U e σ := (factors_twist_iff R σ).2 hπ
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_sqrtDetTwist p q T R (blockPar P e)
      (_root_.GlobalTheory.CoverDS.hasTypes_of_factors hL hK hD p q (p + q) e P T (Cover.twist R) σ hB hf hds)

end GlobalTheory.CoverDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLaws
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf.SupFin

theorem supSob_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D), (∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k f ≠ ⊤) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), (∀ U : AddSubgroup (WO S T), ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, dRho (heisO ψ S T) θ τ z f ∈ GlobalTheory.Size.thetaLevel ψ S T U) ∧ ∃ C : ℝ≥0, ∀ k (f : WO S T → ℂ), IsThetaFunO ψ S T f → supSob ψ θ k (dRho (heisO ψ S T) θ τ z f) ≤ C * supSob ψ θ (k + 1) f) ∧ ∀ k (f g : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → supSob ψ θ k (f + g) ≤ supSob ψ θ k f + supSob ψ θ k g ∧ supSob ψ θ k (c • f) = ‖c‖ₑ * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T
  have ha : ∀ g g' : WO S T → ℂ, (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (g + g') ≤
      (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g + (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g' :=
    GlobalTheory.Size.SupWord.supN_add_le
  have hs : ∀ (c : ℂ) (g : WO S T → ℂ), (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (c • g) =
      ‖c‖ₑ * (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) g := GlobalTheory.Size.SupWord.supN_smul
  refine ⟨fun k f hf => ?_, fun τ z => ⟨fun U f hf => GlobalTheory.Size.dRho_mem_thetaLevel hψ hθ hf τ z, ?_⟩,
    fun k f g c hf hg => ⟨GlobalTheory.Size.SupWord.ws_add_le hψ hθ ha hf hg k, GlobalTheory.Size.SupWord.ws_smul hs k c f⟩⟩
  · refine GlobalTheory.Size.wordSum_ne_top_iff.2 fun l _ => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ (GlobalTheory.Size.theta_word hψ hθ l hf)
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (hC w)
  · refine ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf => ?_⟩
    exact GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ ha hs hf τ z k

end GlobalTheory.Unf.SupFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
section
noncomputable section

namespace GlobalTheory.KerDia

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

def ent (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β}
    (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') :
    (Fr B.fields.emb B.embLL (B.R.N i) → ℂ) →ₗ[ℂ] (Fr B.fields.emb B.embLL (B.R.N (i + 1)) → ℂ) :=
  (I.rho u a i b p * I.rho' u a i b' p') • (((I.chain l u a).divDe i).comp
    ((fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ∘ₗ jetMap (jetC I.J.cD (I.th u a i b b' p p')) 0 ∘ₗ
      polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))).comp ((I.chain l u a).sharp i)))

theorem Kmap_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.chain l u a).Kmap i c c' = ent I l u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := rfl

end GlobalTheory.KerDia
end
end

