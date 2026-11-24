module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSubspaceStableMaximalCompact
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
noncomputable section
namespace GlobalTheory.CompactStable
variable {D : D7}
theorem maximal_compact_stable_theta_subspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  intro _ D ψ θ _ hθ ε M X A B χS χT ω eS eT hω hE Xs Ws Mo ψ' χX χW om τ hH hR Φ hΦ _ hF N hN k hk f hf f₁ hact
  obtain ⟨-, hstd, -, hdX, -, hdW, -, -, -, -, hW, -, -⟩ := hH
  obtain ⟨f₀, r, hv, hv0, hP⟩ := hF
  obtain rfl := hR.psi
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨T, hT, hTi⟩ := _root_.GlobalTheory.ThetaTransformInj.linear_injective D Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) hR.good hstd hdX hdW
    (gram_det_ne (sgn ε M))
  have hinj : ∀ a ∈ schA D.host.F (Fin M.rank × Fin X.rank), ∀ b ∈ schA D.host.F (Fin M.rank × Fin X.rank),
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) a =
        GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank)) b → a = b := by
    intro a ha b hb e
    rw [← hT a ha, ← hT b hb, ← sub_eq_zero, ← map_sub] at e
    exact sub_eq_zero.1 (hTi _ (Submodule.sub_mem _ ha hb) e)
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hv0
    have e1 : ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ 1 = f₀ := by
      have : (1 : PolF D X.rank M.rank) = MvPolynomial.basisMonomials _ ℂ 0 := by simp
      rw [this]
      exact (Module.Basis.constr_basis _ _ _ _).trans (by simp [opPow])
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ 1) 0 = 0 := by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
    rw [← e1, ← (hP 1).2, e2, ← hT 0 (Submodule.zero_mem _), map_zero]
  have hcan : ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) (Q : PolF D X.rank M.rank),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r ∈ schA D.host.F (Fin M.rank × Fin X.rank) →
      GlobalTheory.TripleRead.thO Mo ψ' (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) g r) = ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀ Q → g = Φ Q := by
    intro g Q hg e
    exact DFunLike.coe_injective (tens_inj (hP Q).1.1 hr0 (hinj _ hg _ (hP Q).1.2 (e.trans (hP Q).2.symm)))
  have hi : Function.Injective (ptF ψ' (Eqv.thetaC D) (frSgn ε A) B f₀) := fun P Q e =>
    hΦ (hcan _ Q (hP P).1.2 ((hP P).2.trans e))
  obtain ⟨h, hh, rfl⟩ := exists_of_mem_KInf B hR.JW (fun w => (hR.cart w).imp fun t ht => ⟨ht.1, ht.2.2⟩) hk
  have key := closure_stable (frSgn ε A) B hθ hω hE hv hv0 hi N (fun t Y hY P hP => hN ⟨(t, Y), hY⟩ P hP) hh
  obtain ⟨P, hPN, rfl⟩ := hf
  obtain ⟨Q, hQ, e⟩ := key P hPN
  refine ⟨Q, hQ, (hcan f₁ Q ?_ ?_).symm⟩
  · rw [← hact r (hP P).1]
    letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.invTwo (F := D.host.F)
    exact hW.1.1.pres _ _ (hP P).1.2
  · have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (GlobalTheory.RealDict.sgE (D := D) ε) hR.JX 1 = 1 :=
      Subtype.ext (by show GeneralLinearGroup.map (cA D) (Formalism.L2.Theta.matHom M 1) = 1; rw [map_one, map_one])
    have h2 := hR.transp _ (hP P).1.2 1 h
    rw [h1, (hP P).2] at h2
    have h3 : ω.toSgn ε (1, h) = ω (1, h) := congrArg ω (Prod.ext (map_one (ofSgn ε M)) rfl)
    rw [h3] at e
    rw [← hact r (hP P).1]
    exact h2.trans e
end GlobalTheory.CompactStable
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_subspace_stable_maximal_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w),
    GlobalTheory.RealDict.PublishedHyps D Xs Ws Mo ψ' χX χW om τ → GlobalTheory.RealDict.IsPairReading ψ ε A B ω Xs Ws Mo ψ' om τ →
    ∀ Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
    Function.Injective Φ → LinearMap.range Φ = Mo.Pol ψ' τ → GlobalTheory.RealDict.IsFockMap ψ θ ε A B Mo Φ →
      ∀ N : Submodule ℂ (PolF D X.rank M.rank),
        GlobalTheory.RealQuot.IsStab (fun i : GlobalTheory.RealQuot.LieIx X => GlobalTheory.RealQuot.actT ε A B eS i.1.1 i.1.2) N →
        ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Ws τ, ∀ f ∈ N.map Φ, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om (1, k)) f f₁ → f₁ ∈ N.map Φ := by
  first | exact @_root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace | exact _root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace | (intros; apply _root_.GlobalTheory.CompactStable.maximal_compact_stable_theta_subspace <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumOmegaRational
section
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
noncomputable section
namespace GlobalTheory.ThetaRatPair
theorem theta_sum_omega_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' Φ hΦ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hX : X.J.det ≠ 0 := det_ne_zero_of_map X.J (B.emb w).1 (det_ne_zero_of_hasSig _ (hP.herm.sig w))
  have hW : W.J.det ≠ 0 := by
    refine det_ne_zero_of_map W.J (B.emb w).1 fun h0 => det_ne_zero_of_hasSig _ (hP.skew.sig w) ?_
    rw [Matrix.det_smul, h0, mul_zero]
  exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hP.base.cm B.ψ hP.base.std n d X.J W.J hP.herm.herm hX hP.skew.skew hW M.co
    hP.good.rat χX χW hP.hX hP.hW om hP.weil γ hγ γ' hγ' Φ hΦ
end GlobalTheory.ThetaRatPair
end
end

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pair_sum_rational : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  first | exact @_root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | exact _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational | (intros; apply _root_.GlobalTheory.ThetaRatPair.theta_sum_omega_rational <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspLiftMemCuspList
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult Matrix Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
variable {D : D7}
end GlobalTheory.StartCusp
namespace GlobalTheory.StartCusp
open Formalism.IndefR.Mult
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  intro hP _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  intro t y
  have hθ : ch.W.θ = R.θ := hch.toIsBase.weil.θ
  have hT := GlobalTheory.ProjectedLift.thDn_mem R t y
  have hT' := (GlobalTheory.MultMem.mem_mult_iff D R.θ _ _ (R.MY 0) _ _ _).1 hT
  have hu : ch.cv.lift t y = PiTensorProduct.lift (PiTensorProduct.lift.symm (R.thDn t y)) ch.cv.w := by
    rw [LinearEquiv.apply_symm_apply, ch.cv.thDn_w hS.core.chain]
  rw [hθ, hu]
  refine ⟨GlobalTheory.EndCusp.isAutFunSm_lift hT' _, isCuspFun_lift hT' _, fun τ => ?_⟩
  have h := star_lift_isTypeAt R.θ hP.harishChandraModules (R.MY 0) hT ch.cv.w τ
  rw [show Node.par D ch.sc.cGap (.grid 0 0) τ = (Ptw D).Dpar 0 τ from parV_zero D _ (Nat.zero_le _) τ]
  simp only [parB, dualPar_dualPar, Nat.zero_min] at h
  exact h
end GlobalTheory.StartCusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_lift_mem_cuspList : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (y : (R.HX t).H), IsCuspListed (G := ch.G) ch.W.θ (.grid 0 0) (ch.cv.lift t y) := by
  first | exact @_root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | exact _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList | (intros; apply _root_.GlobalTheory.StartCusp.cusp_lift_mem_cuspList <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDeformationLiftSmooth
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.DefLiftSmooth
theorem deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hω hθ hΦ hS _ hν h𝓕 hφ k τs Xs hX h
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  set κ := GlobalTheory.Mem.Lift.thKer ψ S T om with hκ
  let L : GlobalTheory.RealWeil.thetaSub ψ S T → GA D T → ℂ := fun f h => ∫ g in 𝓕, κ f g h * φ g ∂ν
  have hkinv : ∀ f, ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T), κ f (γ * g) h * φ (γ * g) = κ f g h * φ g := by
    intro f γ hγ g h
    have := hK.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [this, hφ.left γ hγ]
  have hcont : ∀ φ' ∈ Set.range L, Continuous φ' := by
    rintro _ ⟨f, rfl⟩
    exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun h g => κ f g h * φ g) (((hK.cont f).comp continuous_swap).mul (hφ.cont.comp continuous_snd))
      (fun γ hγ h g => hkinv f γ hγ g h)
  have hder : ∀ φ' ∈ Set.range L, ∀ τ, ∀ X ∈ lieAt T τ, ∃ φ'' ∈ Set.range L, ∀ h,
      HasDerivAt (fun t : ℝ => φ' (h * oneP θ T τ X t)) (φ'' h) 0 := by
    rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hK.derW τ X hX f
    refine ⟨L f', ⟨f', rfl⟩, fun h => ?_⟩
    have hoc := GlobalTheory.Mem.Lift.continuous_oneP (V := T) hθ hX
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t g => κ f g (h * oneP θ T τ X t) * φ g) (fun t g => κ f' g (h * oneP θ T τ X t) * φ g)
      (fun t => ((hK.cont f).comp (continuous_id.prodMk continuous_const)).mul hφ.cont)
      (((hK.cont f').comp (continuous_snd.prodMk (continuous_const.mul (hoc.comp continuous_fst)))).mul
        (hφ.cont.comp continuous_snd))
      (fun γ hγ t g => hkinv f γ hγ g _) (fun γ hγ t g => hkinv f' γ hγ g _)
      (fun t g => (GlobalTheory.Mem.Lift.hasDerivAt_oneP (φ := fun h => κ f g h) (φ' := fun h => κ f' g h) hθ hX
        (fun h => e g h) h t).mul_const (φ g)) 0
    simpa only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, L] using key
  have hsm := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T (Set.range L) hcont hder (L ⟨Φ, hΦ⟩) ⟨_, rfl⟩
  exact hsm k τs Xs hX h
end GlobalTheory.DefLiftSmooth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_deformation_lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), _root_.GlobalTheory.FunPr.ThetaLocalInputs → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  first | exact @_root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | exact _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth | (intros; apply _root_.GlobalTheory.DefLiftSmooth.deformation_lift_smooth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistDescentApproximation
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.DownApprox
open GlobalTheory.Grid GlobalTheory.ChainFr
open scoped ENNReal
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem upperArrow_approx : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P (i + 1)).Maps, F ∈ (G.P (i + 1)).Cusp R.θ → ∀ v : SmT (G.P (i + 1)).M, (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F v g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * F v g ∂(G.mP (i + 1)).ν‖ < ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG i hi Φ hΦ Fm hF v _ C hC ε hε
  classical
  have hθ : IsInfFam R.θ := hRB.inf
  have hW := (hG.arrows.dn i hi).weil
  have hω : IsWeilDatumO R.ψ (neg (G.P (i + 1)).V) (G.P i).V (G.chi (D.R.m - i)) (G.chi (D.R.m - i))
      ((G.dn i).ω.toSgn true) := hW
  obtain ⟨hν, hfd⟩ : (G.mP (i + 1)).ν.IsHaarMeasure ∧
      IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    have h := hG.meas.P (i + 1) hi
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have hFv : GlobalTheory.Grow.RapidDec (G.P (i + 1)).V (Fm v) := by
    have h := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ (G.P (i + 1)).M ∅ 1 Fm hF v
    exact (GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ h.1 h.2).rapidDec
  obtain ⟨μ, 𝓓, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (neg (G.P (i + 1)).V) (G.P i).V
  obtain ⟨U, hU, hΦU, happ⟩ := GlobalTheory.FockDensity.fockDense D _ _ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) R.θ R.ψ
    hω.std hθ μ 𝓓 hμ Φ hΦ
  haveI : BorelSpace (GA D (G.P (i + 1)).V) := ⟨rfl⟩
  haveI hfin : IsFiniteMeasure ((G.mP (i + 1)).ν.restrict (G.mP (i + 1)).fd) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.Chain.LiftReg.vol_ne_top hν hfd)
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact (G.P i).V hC
  have hbound : ∀ U' : AddSubgroup (WO (neg (G.P (i + 1)).V) (G.P i).V), IsOpen (U' : Set (WO (neg (G.P (i + 1)).V) (G.P i).V)) →
      ∃ (d : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel R.ψ (neg (G.P (i + 1)).V) (G.P i).V U', ∀ h ∈ C,
        IntegrableOn (fun g => thetaKO (G.dn i).ω g h f * Fm v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν ∧
        ‖∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h f * Fm v g ∂(G.mP (i + 1)).ν‖ ≤
          M * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := by
    intro U' hU'
    obtain ⟨d, Ae, K, hK0, hK⟩ := thetaKernel_le_sobolev_mul_height_source hθ hW μ 𝓓 hμ U' hU'
    obtain ⟨B, hB⟩ := hFv.decay Ae
    refine ⟨d, K * max H 1 ^ Ae * max B 0 * ((G.mP (i + 1)).ν (G.mP (i + 1)).fd).toReal, by positivity,
      fun f hf h hh => ?_⟩
    have hs : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
    have hcont : Continuous fun g => thetaKO (G.dn i).ω g h f * Fm v g :=
      ((hω.om_cont f hf.1 0).comp ((continuous_ofSgn_symm true _).prodMk continuous_const)).mul hFv.continuous
    have hpt : ∀ g, ‖thetaKO (G.dn i).ω g h f * Fm v g‖ ≤
        K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max H 1 ^ Ae * max B 0 := by
      intro g
      rw [norm_mul]
      have h1 := hK f hf g h
      have h2 : GlobalTheory.Grow.height (G.P i).V h ^ Ae ≤ max H 1 ^ Ae :=
        pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ h).le ((hH h hh).trans (le_max_left _ _)) Ae
      have h3 : ‖Fm v g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae ≤ max B 0 := (hB g).trans (le_max_left _ _)
      have h4 : 0 ≤ GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le Ae
      have h5 : 0 ≤ GlobalTheory.Grow.height (G.P i).V h ^ Ae := pow_nonneg (GlobalTheory.Grow.height_pos _ h).le Ae
      calc ‖thetaKO (G.dn i).ω g h f‖ * ‖Fm v g‖
          ≤ K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae *
              GlobalTheory.Grow.height (G.P i).V h ^ Ae * ‖Fm v g‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height (G.P i).V h ^ Ae *
              (‖Fm v g‖ * GlobalTheory.Grow.quotHeight (G.P (i + 1)).V g ^ Ae) := by ring
        _ ≤ K * (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d f).toReal * max H 1 ^ Ae * max B 0 := by
          gcongr
    refine ⟨Integrable.of_bound hcont.aestronglyMeasurable _ (.of_forall hpt), ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall hpt)).trans (le_of_eq ?_)
    simp only [Measure.real, Measure.restrict_apply_univ]
    ring
  obtain ⟨d, M, hM0, hMb⟩ := hbound U hU
  have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (M + 1)) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨g, hgS, hgU, hlt⟩ := happ d _ hδ
  obtain ⟨n, f, p, hf, rfl⟩ := exists_sum_of_mem_fockSpan hgS
  refine ⟨n, f, p, fun l => (isVacF_negFr _ _ (f l)).1 (hf l), fun h hh => ?_⟩
  have hpt : ∀ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l) =
      fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l) := fun l => ptF_negFr _ _ (f l) (p l)
  have hint : ∀ l, IntegrableOn (fun g => thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
      Fm v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    intro l
    have ht : IsThetaFunO R.ψ (neg (G.P (i + 1)).V) (G.P i).V
        (ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) :=
      GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ (hf l).1 (p l)
    obtain ⟨U', hU', hl'⟩ := GlobalTheory.Size.isTheta_iff_level.1 ht
    obtain ⟨_, _, _, hb⟩ := hbound U' hU'
    rw [← hpt l]
    exact (hb _ hl' h hh).1
  have e : (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * Fm v g ∂(G.mP (i + 1)).ν) -
      ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) *
        Fm v g ∂(G.mP (i + 1)).ν =
      ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h
        (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l)) * Fm v g ∂(G.mP (i + 1)).ν := by
    rw [← integral_finsetSum _ fun l _ => hint l, ← integral_sub (hMb Φ hΦU h hh).1 (integrable_finsetSum _ fun l _ => hint l)]
    refine integral_congr_ae (.of_forall fun g => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [thetaKO, map_sub, map_sum, Pi.sub_apply, Finset.sum_apply, sub_mul, Finset.sum_mul, hpt]
  rw [e]
  have hs := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hs0 : 0 ≤ (GlobalTheory.Size.sobO R.ψ R.θ μ 𝓓 d (Φ - ∑ l, ptF R.ψ R.θ (negFr (G.P (i + 1))) (Fr.ofModel (G.P i).M) (f l) (p l))).toReal :=
    ENNReal.toReal_nonneg
  refine ((hMb _ (sub_mem hΦU hgU) h hh).2).trans_lt ?_
  have hM1 : 0 < M + 1 := by linarith
  calc M * _ ≤ (M + 1) * _ := mul_le_mul_of_nonneg_right (by linarith) hs0
    _ < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hs hM1
    _ = ε := by field_simp
end GlobalTheory.DownApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_descent_approximation : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ F : (G.P (i + 1)).Maps, F ∈ (G.P (i + 1)).Cusp R.θ → ∀ v : SmT (G.P (i + 1)).M, (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * F v g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → ∀ C : Set (GA D (G.P i).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (f : Fin n → (WO (G.P (i + 1)).V (G.P i).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l)) ∧ ∀ h ∈ C, ‖(∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * F v g ∂(G.mP (i + 1)).ν) - ∑ l, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f l) (p l)) * F v g ∂(G.mP (i + 1)).ν‖ < ε := by
  first | exact @_root_.GlobalTheory.DownApprox.upperArrow_approx | exact _root_.GlobalTheory.DownApprox.upperArrow_approx | (intros; apply _root_.GlobalTheory.DownApprox.upperArrow_approx <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistLeftVertexParabolicIsGood
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.LeftVertexPar
theorem leftVertex_parabolic_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ τ, GoodPar (G.P i).V.rank ((G.P i).V.sig (tauE D τ)).1 ((G.P i).V.sig (tauE D τ)).2 ((G.P i).S τ) := by
  intro _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G _ hG i hi τ
  exact GlobalTheory.NodePar.goodPar_of_sigOK (G.P i) (hG.spaces.P i hi.le).sigOK τ
end GlobalTheory.LeftVertexPar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_leftVertex_parabolic_isGood : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ τ, GoodPar (G.P i).V.rank ((G.P i).V.sig (tauE D τ)).1 ((G.P i).V.sig (tauE D τ)).2 ((G.P i).S τ) := by
  first | exact @_root_.GlobalTheory.LeftVertexPar.leftVertex_parabolic_isGood | exact _root_.GlobalTheory.LeftVertexPar.leftVertex_parabolic_isGood | (intros; apply _root_.GlobalTheory.LeftVertexPar.leftVertex_parabolic_isGood <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistThetaLiftLeQuotientHeight
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ThetaArrowGrowth
theorem thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  intro _ _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  obtain ⟨K, n, hK, hb⟩ := GlobalTheory.ChainOnto.ThetaSwap.thetaKO_le_quotHeight hRB.inf hω hΦ
  refine ⟨n, n, K, hK, fun h g => ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact hb h g
end GlobalTheory.ThetaArrowGrowth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_thetaLift_le_quotientHeight : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g Φ‖ ≤ C * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @_root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | exact _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight | (intros; apply _root_.GlobalTheory.ThetaArrowGrowth.thetaLift_le_quotientHeight <;> assumption)
end
end

