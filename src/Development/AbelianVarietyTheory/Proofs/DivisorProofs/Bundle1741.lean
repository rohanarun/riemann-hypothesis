module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelIntegrableOnFundamentalDomain
section
namespace I195MixedCoordinates_a146dcd1584a90330aa1ce04

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

end I195MixedCoordinates_a146dcd1584a90330aa1ce04

public noncomputable abbrev _root_.I195MixedCoordinates_74ccb184947b854a25a0cacd.source :=
  @_root_.I195MixedCoordinates_a146dcd1584a90330aa1ce04.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaCuspInteg

theorem theta_le_height {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ)
    (hΦ : IsThetaFunO ψ (sgn ε M) X Φ) (τ₀ : D.what₂.Tau)
    (hvan : ∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r)
      (μ' : Measure (Mx D X.rank r)) (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → (_root_.I195MixedCoordinates_a146dcd1584a90330aa1ce04.source d) X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0)
    (r : ℕ) (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (Ω C₀ : Set (GA D M)) (K : Subgroup (GA D M)) (c : ℝ) (hC₀ : IsCompact C₀) (hK : IsCompact (K : Set (GA D M)))
    (hc : 0 < c)
    (hsub : ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
      a⁻¹ * p * a ∈ C₀) (h : GA D X) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
      ∀ k ∈ K, ‖thetaKO ω (p * a * k) h Φ‖ₑ ≤ ENNReal.ofReal B := by
  have hC₁ : IsCompact (C₀ * (K : Set (GA D M))) := hC₀.mul hK
  obtain ⟨K₀, hK₀n, hK₀c, m, e, hlev⟩ := _root_.GlobalTheory.LevelGrowth.level_poly ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (sgn ε M) X
  obtain ⟨S₀, d, hA1⟩ := _root_.GlobalTheory.WittLevi.witt_levi θ hθ ε M r Xf Yf hW
  obtain ⟨μ', 𝓕', hcov, hA2⟩ := _root_.GlobalTheory.LeviThetaSum.levi_sum ψ (sgn ε M) S₀ X r d χ χ' (ω.toSgn ε) hω
  obtain ⟨k, A, C, hC, hB⟩ := GlobalTheory.T.torus_mixedCoordinate_sum_rapid_decay ψ (IsWeilDatumO.std hω) θ hθ (sgn ε M) X S₀ r d μ' 𝓕' hcov c hc K₀ hK₀n hK₀c
    μ 𝓕 hμ τ₀ (Module.finrank ℚ D.host.F * X.rank)
  obtain ⟨N₂, C₂, hC₂, hU⟩ := GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁ μ 𝓕 hμ k
  set H : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) with hHdef
  refine ⟨C * (m * H ^ e) ^ A * (C₂ * H ^ N₂), fun p hp t ht a ha k' hk' => ?_⟩
  have hy : a⁻¹ * p * a * k' ∈ C₀ * (K : Set (GA D M)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk'
  have hΨ : IsThetaFunO ψ (sgn ε M) X (ω (a⁻¹ * p * a * k', h) Φ) := by
    have := hω.om_pres ((GlobalTheory.Grid.ofSgn ε M).symm (a⁻¹ * p * a * k'), h) Φ hΦ
    simpa [GlobalTheory.Grid.WRep.toSgn] using this
  obtain ⟨n, hn, hnle, hnlev⟩ := hlev _ hy h
  have hs := hU _ hy h
  have hsplit : thetaKO ω (p * a * k') h Φ = ω (a, 1) (ω (a⁻¹ * p * a * k', h) Φ) 0 := by
    have e1 : ((p * a * k', h) : GA D M × GA D X) = (a, 1) * (a⁻¹ * p * a * k', h) := by
      ext <;> simp [mul_assoc]
    unfold thetaKO
    rw [e1, map_mul]
    rfl
  rw [hsplit]
  obtain ⟨α, hα1, hα2, hlevi⟩ := hA1 t ht.1 a ha
  have h2 := hB n hn _ hΨ hnlev (hvan _ h S₀ r d μ' 𝓕' hcov) t ht α.1 hα1 hα2
  have hle := hA2 _ hΨ α
  generalize ω (a⁻¹ * p * a * k', h) Φ = Ψ at *
  have e' : ω (a, 1) Ψ 0 = ω.toSgn ε (d.levi α, 1) Ψ 0 := by
    rw [← hlevi]
    show ω (a, 1) Ψ 0 = ω ((ofSgn ε M) ((ofSgn ε M).symm a), 1) Ψ 0
    rw [MulEquiv.apply_symm_apply]
  rw [← e', _root_.GlobalTheory.HalfModTorus.halfMod_torus θ hθ r X.rank t ht.1 α hα1 hα2] at hle
  refine hle.trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : 0 ≤ m * H ^ e := hn0.trans hnle
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hnle A) hC) hs ENNReal.toReal_nonneg
    (mul_nonneg hC (pow_nonneg hm0 A))

theorem integrableOn_thetaKO : GlobalTheory.Published.SiegelSetUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → p < M.rank →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ∀ τ₀ : D.what₂.Tau,
    (∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r) (μ' : Measure (Mx D X.rank r))
      (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → (_root_.I195MixedCoordinates_a146dcd1584a90330aa1ce04.source d) X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0) →
    ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  intro hRT D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ τ₀ hvan h
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨B, hB⟩ := theta_le_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ τ₀ hvan r Xf Yf hW Ω C₀ K c hC₀ hK hc hconj h
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : Continuous fun g => thetaKO ω g h Φ :=
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := _root_.GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top D.host.F M.rank r 0 hc (by omega)
  simp only [mul_zero, pow_zero, Finset.prod_const_one, ENNReal.ofReal_one, one_mul] at hI
  have key : ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal B * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹)) := by
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov hcont.enorm.measurable
            (fun γ hγ g => by rw [hinv γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal B *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) :=
          hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) (fun _ => ENNReal.ofReal B) measurable_const
            fun q hq t ht a ha k hk => hB q hq t ht a ha k hk
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ⟨hcont.aestronglyMeasurable, key.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI))⟩

end GlobalTheory.ThetaCuspInteg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblRestrict


set_option maxHeartbeats 2000000 in
theorem omp_diag_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  let h : GA D T := ⟨g.1, GlobalTheory.ThetaTransform.mem_GA_target hA g⟩
  let hd : GA D (GlobalTheory.Doubling.dblSp T) := ⟨gd.1, GlobalTheory.ThetaTransform.mem_GA_target rfl gd⟩
  have hh : Formalism.L2.Theta.mt T h = g.1.1 := rfl
  have hhd : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd = gd.1.1 := rfl
  have h1S : Formalism.L2.Theta.mt S 1 = ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))⁻¹).1.1ᵀ := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨hB1, hΘ1⟩ := hom g 1 1 h hh h1S φ₁ hφ₁
  have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hA1, hΘA⟩ := homp gd 1 1 hd hhd h1S _ hbox
  have hφ₂' := GlobalTheory.ConjSch.star_mem_schA κ φ₂ hφ₂
  have bij := GlobalTheory.ThetaTransform.thetaTr_bij co hψ hA hB hrat
  have bijd := GlobalTheory.ThetaTransform.thetaTr_bij (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) hψ rfl hB
    (GlobalTheory.WeilSchrodinger.DblTarget.coDbl_rat hA co hrat)
  refine bijd.2.1 _ hA1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ hB1 φ₂ hφ₂) ?_
  have e1 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun D ψ hψ S T JA JB ξ hA κ co _ hφ₁ _ hφ₂
  have e2 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.thetaTr_coDbl_boxFun D ψ hψ S T JA JB ξ hA κ co _ hB1 _ hφ₂
  have hgd' : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) := hgd
  have key := _root_.GlobalTheory.DblRestrictChar.dbl_diag_box D ψ hψ S T χS χT ω hω ωd hωd (_root_.GlobalTheory.DblThetaRestrict.scalar D ψ hψ S T χS χT ω hω ωd hωd) h hd hgd' _ _
    ((bij.2.2 _).2 ⟨φ₁, hφ₁, rfl⟩) ((bij.2.2 _).2 ⟨_, hφ₂', rfl⟩)
  refine hΘA.trans ?_
  refine ((congrArg (ωd (1, hd)) e1).trans key).trans ?_
  refine Eq.trans ?_ e2.symm
  rw [hΘ1]

end GlobalTheory.WeilSchrodinger.DblRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransposeMapConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.TripleCplxAt

variable {m n : Type} [Fintype m] [Fintype n]

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map conj).map conj = M := by
  ext; simp

theorem smul_map_conj {m n : Type} (c : ℂ) (M : Matrix m n ℂ) : (c • M).map conj = conj c • M.map conj := by
  ext; simp

theorem transpose_map_conj {k : Type} (M : Matrix k k ℂ) : (M.map conj)ᵀ = Mᴴ := by
  ext; simp [Matrix.conjTranspose_apply]

theorem cartan_comm {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  obtain ⟨h1, h2, -⟩ := h
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h2]

theorem mul_cols {a b d k : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (X : Matrix (Fin b) (Fin d) ℂ) (f : Fin k → Fin d) :
    (A * X).submatrix id f = A * X.submatrix id f := by
  ext; simp [Matrix.mul_apply]

theorem smul_cols {a d k : ℕ} (c : ℂ) (X : Matrix (Fin a) (Fin d) ℂ) (f : Fin k → Fin d) :
    (c • X).submatrix id f = c • X.submatrix id f := by
  ext; simp

theorem conj_hyp {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ)) :
    X' = (-Complex.I) • (sW.map conj * X * (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁)ᵀ) := by
  have h := congrArg (fun M => M.map (starRingEnd ℂ)) hX
  simp only [map_conj_conj, smul_map_conj, Matrix.map_mul, Complex.conj_I] at h
  rw [h, ← Matrix.transpose_map, map_conj_conj]

theorem algV {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW G : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : sWᴴ * G = G * sW) :
    (X'.submatrix id fun k => e (.inl k))ᵀ * (-G) =
      Complex.I • (cV * ((X.submatrix id fun k => e (.inl k))ᵀ * (-G)) * (-sW)) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inl, mul_cols, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, transpose_map_conj]
  simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_smul, neg_neg, hs]

theorem algW {a p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (X X' : Matrix (Fin a) (Fin d) ℂ)
    (sW : Matrix (Fin a) (Fin a) ℂ) (cV : Matrix (Fin p) (Fin p) ℂ) (cV₁ G₁ : Matrix (Fin q) (Fin q) ℂ)
    (hX : X'.map conj = Complex.I • (sW * X.map conj * ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e cV cV₁).map conj)ᵀ))
    (hs : cV₁ᴴ * G₁ = G₁ * cV₁) :
    -((X'.submatrix id fun k => e (.inr k)).map conj * G₁) =
      Complex.I • (sW * (-((X.submatrix id fun k => e (.inr k)).map conj * G₁)) * cV₁) := by
  rw [conj_hyp e X X' sW cV cV₁ hX, smul_cols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose,
    GlobalTheory.RouteCoords.submatrix_mul_blk_inr, mul_cols, smul_map_conj, Matrix.map_mul, Matrix.map_mul, map_conj_conj,
    Matrix.transpose_map, transpose_map_conj]
  simp only [map_neg, Complex.conj_I, neg_neg, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul,
    Matrix.mul_neg, smul_neg, neg_smul, hs]

end GlobalTheory.TripleCplxAt

namespace GlobalTheory.TripleCplxAt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

section Adelic

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {a b c : ℕ} (A : Mx D a b) (B : Mx D b c) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B :=
  Matrix.map_mul (f := (θ τ).comp (infPart D))

theorem compAt_neg' (θ : InfFam D) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (-A) = -compAt θ τ A :=
  Matrix.map_neg _ (fun a => map_neg ((θ τ).comp (infPart D)) a) A

theorem compAt_inc (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) :
    compAt θ τ (A.map (incA D)) = A.map (tauE D τ) := by
  ext x y; exact (hθ τ).1 (A x y)

theorem compAt_conj (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (A : Mx D a b) :
    compAt θ τ (A.map (cA D)) = (compAt θ τ A).map conj := by
  ext x y; exact (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 _ _

theorem compAt_mapV (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapV e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * (-gramAt D (spW G i j) τ) := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((negSp (spW G i j)).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ, negSp_gram, Matrix.map_neg _ (map_neg _)]
  rfl

theorem compAt_mapW (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : Pt G i j) :
    compAt θ τ (mapW e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl

end Adelic

theorem cplx_pair : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ u u' : Pt G i j, (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) → ∀ τ,
      compAt W.θ τ (mapV e u') = cplxO (-W.cart (.grid (i + 1) (j + 1)) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapV e u)) ∧
      compAt W.θ τ (mapW e u') = cplxO (W.cart (.grid (i + 1) j) τ) (W.cart (.grid (i + 1) (j + 1)) τ) (compAt W.θ τ (mapW e u)) := by
  intro D T L sc G W M t i j e Bs Γ X h u u' hu τ
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V.θ w = W.cart (.grid (i + 1) (j + 1)) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, hV, -, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : Pt G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW := W.cart_is (.grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · rw [compAt_mapV W.θ W.θ_is, compAt_mapV W.θ W.θ_is]
    exact algV e _ _ _ _ _ _ hX (cartan_comm cW)
  · rw [compAt_mapW W.θ W.θ_is, compAt_mapW W.θ W.θ_is]
    exact algW e _ _ _ _ _ _ hX (cartan_comm cV₁)

end GlobalTheory.TripleCplxAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzLocal
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.VacLine

theorem eigen_line : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (g : (Fin a' × Fin (a + a') → Fv F w) → ℂ), g ∈ SB (Fin a' × Fin (a + a') → Fv F w) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) g (c • g)) →
    ∃ r : ℂ, g = r • G.M'.vac w := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v φ hφ hfix
  have hat : ∀ γ ∈ latAtV G.V' G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  obtain ⟨hvSB, hv0, θ, -, hvac⟩ := hTr.geo.hM'.vac v
  let cf : latAtV G.V' G.W v → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  have hloc : ∀ f ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ γ : latAtV G.V' G.W v,
      Acts (evFin F v) (G.M'.co.rho B.ψ γ) f (cf γ • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) f = cf γ • f := by
    intro f hf γ h
    exact GlobalTheory.TensUniq.eq_of_tens_eq v f _ _ hf fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ γ.2) f r hr).symm.trans (h r hr)
  have hsd : ∀ z, z ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) ↔
      ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), GlobalTheory.LatVac.psiAt B.ψ v (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1 :=
    GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ (latAtV G.V' G.W v) hat
      (fun z hz => GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B a' (a + a') G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW
        v z hz)
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v),
      t • l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v) := by
    rintro t ht _ ⟨γ, hγ, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • γ, (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).2 t ht γ hγ, ?_⟩
    rw [GlobalTheory.LatOpenCpt.locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hbd : ∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo G.M'.co v), ∀ i,
      c * l.1 i ∈ v.adicCompletionIntegers F := by
    obtain ⟨c, hc0, hc⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
    exact ⟨c, hc0, by rintro _ ⟨γ, hγ, rfl⟩ i; exact (hc γ hγ i).1⟩
  have hD := _root_.GlobalTheory.selfDual_exists_snd_of_orth v (GlobalTheory.LatVac.psiAt B.ψ v) _ hsd hst hbd
  refine GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun γ : latAtV G.V' G.W v => GlobalTheory.LatVac.locCo G.M'.co v γ) cf (fun u hu => ?_) φ (G.M'.vac v)
    (fun γ => hloc φ hφ γ (hfix γ γ.2 _ (hvac γ γ.2))) (fun γ => hloc _ hvSB γ (hvac γ γ.2)) hv0
  obtain ⟨y', γ, hγ, he⟩ := hD u (by
    rintro y ⟨γ, hγ, he⟩
    have h1 := hu ⟨γ, hγ⟩ (congrArg Prod.fst he)
    have h2 : (GlobalTheory.LatVac.locCo G.M'.co v γ).2 = y := congrArg Prod.snd he
    simp only at h1
    rw [h2] at h1
    exact h1)
  exact ⟨⟨γ, hγ⟩, congrArg Prod.fst he⟩

end GlobalTheory.VacLine
end
end

