module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankSelfDualUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0441
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistLiftModerateGrowth
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftGrowthDef
theorem lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'
end GlobalTheory.LiftGrowthDef
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_lift_moderate_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  first | exact @_root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | exact _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth | (intros; apply _root_.GlobalTheory.LiftGrowthDef.lift_moderate_growth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistPairingRationalPullbackEq
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets
noncomputable section
namespace GlobalTheory.RatMoveIop
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison GlobalTheory.ThLoc.AllPlaces
section Arith
variable {F : Type} [NormedField F] {lam : Qbar →+* F}
end Arith
variable {D : D7} {N N' : ℕ}
variable (A : Matrix.unitaryGroup (Fin N) D.host.E) (A' : Matrix.unitaryGroup (Fin N') D.host.E)
variable (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
theorem twist_pairing_pullback_of_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  intro _ hI D δ t0 hC ht N N' e0 he _ M M' hM hM' A A'
  obtain ⟨ε, h1, h2⟩ := iop_move A A' D.host.ccK δ (hI D) hC ht he.2.2.2.1 hM hM'
  have hc : ∀ σ : Qbar →+* ℂ, NormOne σ ε := fun σ =>
    h1 ℂ σ fun τ => ⟨(norm_det_complex _ A').1, (norm_det_complex _ A).2⟩
  refine ⟨ε, ⟨(hc (algebraMap Qbar ℂ)).1, fun σ => (hc σ).2⟩, fun q _ a1 a2 a3 a4 lam => ?_, h2⟩
  obtain ⟨h3, h4⟩ := h1 ℂ_[q] lam fun τ => ⟨(norm_det_padic _ A' a2 a4).1, (norm_det_padic _ A a1 a3).2⟩
  rw [lamC, dite_eq_left h3]
  exact h4
end GlobalTheory.RatMoveIop
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_pairing_rational_pullback_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {δ t0 : ℂ}, Crv D D.host.ccK δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 → ∀ {N N' : ℕ} {e0 : VC D N N' → ℂ}, oddE0 D D.host.ccK δ t0 N N' e0 → Even (N * N') →
    ∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SD D M → SD D M' →
    ∀ (U : Matrix.unitaryGroup (Fin N) D.host.E) (U' : Matrix.unitaryGroup (Fin N') D.host.E),
    ∃ ε : ℂ, Mod1All ε ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q M (stdL D N) → EqAt D q M' (stdL D N') →
        EqAt D q (SDLat.smulLat U.1 M) (stdL D N) → EqAt D q (SDLat.smulLat U'.1 M') (stdL D N') → GlobalTheory.MovedKappaEx.UnitAt q ε) ∧
      ∀ z, Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) M M') e0
          (Formalism.L2.KerInert.tPull D (tor0 D D.host.ccK δ) U.1 U'.1 z) =
        ε * Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) N N')
          (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK δ) (SDLat.smulLat U.1 M) (SDLat.smulLat U'.1 M')) e0 z := by
  first | exact @_root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | exact _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational | (intros; apply _root_.GlobalTheory.RatMoveIop.twist_pairing_pullback_of_rational <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftApproxFockSpace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaArrowApprox
theorem thetaLift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨a, ha⟩ := GlobalTheory.KernelApprox.exists_kernel_approx hRB.inf hω
    (fun X => ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank),
      (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧
        X = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) hΦ
    (fun U hU hΦU μ 𝓕 hμ d ε hε => by
      obtain ⟨n, fs, ps, h1, h2, h3⟩ := _root_.GlobalTheory.ArrowFockDense.dense_level D G₀ Pl0 T A Ks R G hRB hG t i j hi hj U hU Φ hΦU μ 𝓕 hμ d ε hε
      exact ⟨_, ⟨n, fs, ps, h1, rfl⟩, h2, h3⟩)
  refine ⟨a, a, fun ε hε => ?_⟩
  obtain ⟨X, ⟨n, fs, ps, hfs, rfl⟩, hX⟩ := ha ε hε
  exact ⟨n, fs, ps, hfs, fun h g => hX h g⟩
end GlobalTheory.ThetaArrowApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_thetaLift_approx_fockSpace : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @_root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace | exact _root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace | (intros; apply _root_.GlobalTheory.ThetaArrowApprox.thetaLift_approx_fockSpace <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistUpperArrowApprox
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped ComplexConjugate
namespace GlobalTheory.UpArrowApprox
end GlobalTheory.UpArrowApprox
namespace GlobalTheory.UpArrowApprox
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  intro hLC hP D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ F hF v hint C hC ε hε
  have hθ : IsInfFam R.θ := hR.inf
  have hω := (hG.arrows.dn i hi).weil
  have hψ : IsStdChar D R.ψ (-1) := IsWeilDatumO.std hω
  have hm := (hG.meas.P i hi.le).2 (by omega)
  have hCA := hLC D hSz G₀ Pl0 T A Ks R G hR hG
  obtain ⟨-, -, hFr⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP.cuspRapidDecay D _ _ _ R.θ hθ _ _ F hF v
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _
    (GlobalTheory.PairLift.frSgn true (GlobalTheory.ChainFr.Fr.ofModel (G.P (i + 1)).M)) (GlobalTheory.ChainFr.Fr.ofModel (G.P i).M) R.θ R.ψ hψ hθ
    μ 𝓕 hμ Φ hΦ
  obtain ⟨a, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (GlobalTheory.Grid.neg (G.P (i + 1)).V).rank (G.P i).V.rank
  obtain ⟨K, hK0, hK⟩ := (H (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V rfl rfl).real R.ψ hθ hU
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ h ∈ C,
      GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) ((GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h) ≤ M := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image
      ((GlobalTheory.Grow.continuous_height _).comp (GlobalTheory.Grid.continuous_ofSgn_symm true _)).continuousOn
    exact ⟨M, fun h hh => hM ⟨h, hh, rfl⟩⟩
  obtain ⟨B, hB⟩ := hFr.decay a
  have hfin : (G.mP i).ν (G.mP i).fd < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hm.1.1 hm.2
  set L : ℝ := K * max M 1 ^ a * 2 ^ a * max B 0 * ((G.mP i).ν (G.mP i).fd).toReal with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ max M 1 := le_trans zero_le_one (le_max_right _ _)
    have : 0 ≤ max B 0 := le_max_right _ _
    positivity
  have hδ : 0 < ε / (2 * (L + 1)) := div_pos hε (by linarith)
  obtain ⟨g₀, hg₀, hg₀U, hg₀d⟩ := hdense d (ENNReal.ofReal (ε / (2 * (L + 1)))) (ENNReal.ofReal_pos.2 hδ)
  obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.1 hg₀
  choose f₀ P hvac hlev hgeq using fun l => (w l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => isFinVec_of_isVacF (hvac l), fun h hh => ?_⟩
  have hsum : g₀ = ∑ l, GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l) := by
    rw [← hw]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hgeq l, ← ptF_eq_fock]
    simp only [GlobalTheory.ChainFr.ptF, map_smul]
  have he : Φ - g₀ ∈ GlobalTheory.Size.thetaLevel R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V U := sub_mem hΦU hg₀U
  have hint' : ∀ l, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) (G.mP i).fd (G.mP i).ν :=
    fun l => ((hCA.up i hi (f₀ l) (isFinVec_of_isVacF (hvac l)) F hF).choose_spec.2 (c l • P l) v h).1
  have hlin : ∀ g, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g =
      starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g := by
    intro g
    rw [hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul]
  rw [← integral_finsetSum _ fun l _ => hint' l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hint' l)]
  have e0 : (∫ g in (G.mP i).fd, (starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g -
      ∑ l, starRingEnd ℂ (thetaKO (G.dn i).ω h g
        (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f₀ l) (c l • P l))) * F v g) ∂(G.mP i).ν) =
      ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g ∂(G.mP i).ν := by
    congr 1
    funext g
    exact hlin g
  rw [e0]
  set s : ℝ := (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (Φ - g₀)).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set h' := (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V).symm h with hh'
  have hpt : ∀ g, ‖starRingEnd ℂ (thetaKO (G.dn i).ω h g (Φ - g₀)) * F v g‖ ≤ K * max M 1 ^ a * 2 ^ a * max B 0 * s := by
    intro g
    have e1 : thetaKO (G.dn i).ω h g (Φ - g₀) = thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀) :=
      GlobalTheory.UpArrowConv.thetaKO_toSgn _ _ _ _
    have hbd : ∀ g, ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ ≤
        (K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a) * GlobalTheory.Grow.height (G.P i).V g ^ a := fun g => by
      have := (hK _ _ _ hω μ 𝓕 hμ _ he).2 h' g
      rw [mul_pow, ← mul_assoc] at this
      exact this
    have hq := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀))
      (GlobalTheory.UpArrowConv.thetaKO_left_snd hω he.1 h') hbd g
    rw [norm_mul, RCLike.norm_conj, e1]
    have hh1 : GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a ≤ max M 1 ^ a :=
      pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le ((hM h hh).trans (le_max_left _ _)) a
    have hFB : ‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a ≤ max B 0 := (hB g).trans (le_max_left _ _)
    have a0 : 0 ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a :=
      mul_nonneg (mul_nonneg (mul_nonneg hK0 hs0) (pow_nonneg (GlobalTheory.Grow.height_pos _ _).le _)) (by positivity)
    have a1 : K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a ≤ K * s * max M 1 ^ a * 2 ^ a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 (mul_nonneg hK0 hs0)) (by positivity)
    calc ‖thetaKO ((G.dn i).ω.toSgn true) h' g (Φ - g₀)‖ * ‖F v g‖
        ≤ K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            GlobalTheory.Grow.quotHeight (G.P i).V g ^ a * ‖F v g‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
      _ = K * s * GlobalTheory.Grow.height (GlobalTheory.Grid.neg (G.P (i + 1)).V) h' ^ a * 2 ^ a *
            (‖F v g‖ * GlobalTheory.Grow.quotHeight (G.P i).V g ^ a) := by ring
      _ ≤ K * s * max M 1 ^ a * 2 ^ a * max B 0 :=
          mul_le_mul a1 hFB (mul_nonneg (norm_nonneg _) (pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ _).le _))
            (a0.trans a1)
      _ = K * max M 1 ^ a * 2 ^ a * max B 0 * s := by ring
  refine (norm_setIntegral_le_of_norm_le_const hfin fun g _ => hpt g).trans_lt ?_
  have hslt : s < ε / (2 * (L + 1)) := ENNReal.toReal_lt_of_lt_ofReal hg₀d
  calc K * max M 1 ^ a * 2 ^ a * max B 0 * s * ((G.mP i).ν (G.mP i).fd).toReal = L * s := by rw [hL]; ring
    _ ≤ (L + 1) * s := by nlinarith
    _ < (L + 1) * (ε / (2 * (L + 1))) := mul_lt_mul_of_pos_left hslt (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end GlobalTheory.UpArrowApprox
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P i).Maps, F ∈ (G.P i).Cusp R.θ → ∀ v : SmT (G.P i).M, (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g) (G.mP i).fd (G.mP i).ν) → ∀ C : Set (GA D (G.P (i + 1)).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * F v g ∂(G.mP i).ν) - ∑ l, ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l))) * F v g ∂(G.mP i).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.UpArrowApprox.upperArrow_approx | exact _root_.GlobalTheory.UpArrowApprox.upperArrow_approx | (intros; apply _root_.GlobalTheory.UpArrowApprox.upperArrow_approx <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaIntegralIntegrableOn
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownConv
theorem downward_theta_integral_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hB hG i hi Φ hΦ φ hφ h
  obtain ⟨hν, h𝓕⟩ := MeasDat.haar_fd (hG.meas.P (i + 1) hi)
  exact integrableOn_thetaKO_mul_cusp hP.cuspRapidDecay hB.inf true ((hG.arrows.dn i hi).weil) hΦ hν h𝓕 hφ.1 hφ.2.1 h
end GlobalTheory.DownConv
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn | exact _root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn | (intros; apply _root_.GlobalTheory.DownConv.downward_theta_integral_integrableOn <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DnLiftAut
theorem downward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have hθ : IsInfFam R.θ := hR.inf
  have hW := (hG.arrows.dn i hi).weil
  have hκ := GlobalTheory.Mem.Lift.isKerSys_thKer hθ hW.std (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont
  have hm := hG.meas.P (i + 1) hi
  have hq0 : (G.mP (i + 1)).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(hm.1 hd).1.1, (hm.1 hd).2⟩
    · exact ⟨(hm.2 hd).1.1, (hm.2 hd).2⟩
  obtain ⟨ν₁, hH, hF, hI⟩ := (GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V).meas _ _ hq0.1 hq0.2
  have hL' := GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V
  have hc : GlobalTheory.Mem.Th.IsCuspForm R.θ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (fun g => φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g)) :=
    ⟨(GlobalTheory.SgnFun.isAutFunSm_sgn_true hL' φ).2 hφ.1, (GlobalTheory.SgnFun.isCuspFun_sgn_true hL' φ).2 hφ.2.1⟩
  have key := hκ.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ hc ⟨Φ, hΦ⟩
  have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V ⁻¹' (G.mP (i + 1)).fd,
        GlobalTheory.Mem.Lift.thKer R.ψ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V ((G.dn i).ω.toSgn true) ⟨Φ, hΦ⟩ g h *
          φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g) ∂ν₁ :=
    funext fun h => ((hI fun g => thetaKO (G.dn i).ω g h Φ * φ g).2).symm
  rw [e]
  exact key.2
end GlobalTheory.DnLiftAut
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  first | exact @_root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic | exact _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic | (intros; apply _root_.GlobalTheory.DnLiftAut.downward_theta_lift_isSmoothAutomorphic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorAwayFromLevel
section
section
namespace TwistAwayFromPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)
open GlobalTheory.SumSize
namespace GlobalTheory.CompanionTheory.Twist
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Host in
theorem twist_trivial_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩
  have hr : ¬ (R.xiH (R.mu w)).UnrAt PP := (s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)
  by_cases hw : w ∈ R.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := s.mu_on w hw
    have e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    by_cases hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP
    · refine Or.inr fun l hl h1 h2 => hr fun x hx => ?_
      have hp : Formalism.EigenvalueLevelCeiling.plc w = l := by
        exact ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1
          ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))
      have a1 := hd x hx
      have a2 := hψ.atl PP (hp ▸ h1) x
      rw [e']
      change (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
      rw [a1, a2, mul_one]
    · refine Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
      have key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := fun p hp => by
        change algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal
        rwa [map_natCast]
      unfold CharFrame.delAt at hd
      split_ifs at hd
      · exact Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))
      · exact Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))
  · have e : R.mu w = A.μ0 := s.mu_off w hw
    refine absurd (fun x _ => ?_) hr
    rw [e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]
    rfl
end GlobalTheory.CompanionTheory.Twist
end
end
end TwistAwayFromPlace
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  first | exact @_root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | exact _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | (intros; apply _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level <;> assumption)
end
end
end

