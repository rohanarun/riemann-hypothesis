module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalar
section
namespace I195MixedCoordinates_29b19643a6a40f518f292300

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

end I195MixedCoordinates_29b19643a6a40f518f292300

public noncomputable abbrev _root_.I195MixedCoordinates_34172b91c8e709398ceb2b5d.source :=
  @_root_.I195MixedCoordinates_29b19643a6a40f518f292300.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem halfMod_eq_detPow {D : D7} {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := rfl

theorem halfMod_rank_zero {D : D7} (n : ℕ) (a : GL (Fin 0) (AE D)) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, Subsingleton.elim a 1, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem wittDecomposition_levi_emb_acts_isotropic {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.e.map (incA D) = d.e.map (incA D) ⬝ a.1 := by
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]

theorem wittDecomposition_levi_emb_acts_anisotropicCore {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.i₀.map (incA D) = d.i₀.map (incA D) ⬝ mt S₀ g := by
  have e2 : d.i₀.map (incA D) = d.j0 := rfl
  rw [e2, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]

theorem heisO_extX_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ)
    (f : WO S T → ℂ) : heisO ψ S T (d.extX T 0) f = f := by
  funext w
  simp only [heisO, map_zero, add_zero, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem levi_origin_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → (_root_.I195MixedCoordinates_29b19643a6a40f518f292300.source d) T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) ((_root_.I195MixedCoordinates_29b19643a6a40f518f292300.source d) T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨hz, -, hl⟩ := _root_.GlobalTheory.Unf.mixRankZero D ψ
    obtain ⟨-, -, -, hiso⟩ := _root_.GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hom.std
    refine ⟨1, 1, continuous_const, fun _ => rfl, continuous_const, fun _ _ => rfl, fun a g f hf => ?_⟩
    change I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 _ 0 = _ • om₀ (g, 1) (I195MixedCoordinates_00549d7c7323d43c39912169.source d T ψ μ 𝓕 f 0)
    rw [hz S S₀ T d μ 𝓕 hμ, hz S S₀ T d μ 𝓕 hμ, (hl S S₀ d).1, one_mul, hiso χS χT om om₀ hom hom₀ g 1 f hf,
      halfMod_rank_zero]
    simp
  · obtain ⟨hsp, hr, -, -, -, hm, -⟩ := _root_.GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    obtain ⟨α, ξ, hα, hξ, h⟩ := _root_.GlobalTheory.LeviChar.levi_scalars_autChar D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT om hom χS χT om₀ hom₀
    refine ⟨α, ξ, hα.1, hα.2, hξ.1, hξ.2, fun a g f hf => ?_⟩
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hr]; exact hμ
    change I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 _ 0 = _ • om₀ (g, 1) (I195MixedCoordinates_61fbc522a99e851221ffe16d.source d T ψ μ 𝓕 f 0)
    rw [hm, hm, heisO_extX_zero, heisO_extX_zero, halfMod_eq_detPow]
    exact h μ 𝓕 hμ' a g (d.levi a * d.emb0 g) (wittDecomposition_levi_emb_acts_isotropic d a g) (wittDecomposition_levi_emb_acts_anisotropicCore d a g) f hf

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionsBiThetaTwoVariablesCommute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrableOn_mul_star {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {𝓕 : Set X} (h𝓕 : μ 𝓕 ≠ ⊤) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    {M N : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hN : ∀ x, ‖g x‖ ≤ N) : IntegrableOn (fun x => f x * star (g x)) 𝓕 μ := by
  refine Measure.integrableOn_of_bounded (M := M * N) h𝓕
    ((hf.mul hg.star).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (hM x) (hN x) (norm_nonneg _) ((norm_nonneg _).trans (hM x))

theorem isBiTheta_left {A S A' : HSp D} {χA χS : (AE D)ˣ →* Circle} {oma : Om A S}
    (hA : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (p : GA D A × GA D S) :
    IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  have hF := GlobalTheory.BiTransfer.isThetaFunO_join d hC
  have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ hF Unit (0 : Measure Unit)
    (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) p).1
  simp only [GlobalTheory.BiTransfer.join_symm] at h
  exact GlobalTheory.BiTransfer.isBiTheta_of_join (C := fun u v => oma p (fun u' => C u' v) u) d h

theorem slice_right {A S A' : HSp D} {K : WO A S → WO S A' → ℂ} (hK : IsBiTheta ψ A S A' K) (u : WO A S) :
    IsThetaFunO ψ S A' (K u) := by
  refine ⟨fun γ w => hK.quasiR γ u w, ?_, hK.cont.comp (continuous_const.prodMk continuous_id), fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, h⟩ := hK.levR
    exact ⟨U, hU, fun a ha ha' => h a ha ha' u⟩
  · have := hK.smooth k 0 L continuous_zero hL (fun _ => by simp) hLf u w
    simpa using this

theorem comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle)
    (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb →
    ∀ C, IsBiTheta ψ A S A' C → ∀ p q u v,
      omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB C hC p q u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.MixModel.exists_isCovolOne D A'.rank S.rank
  have h𝓕 : μ 𝓕 ≠ ⊤ := by rw [hcov.2.2]; exact ENNReal.one_ne_top
  let v0 : VolM D A'.rank S.rank := ⟨μ, 𝓕, hcov⟩
  have : BorelSpace (WO S A') := ⟨rfl⟩
  have : BorelSpace (WO A' S) := ⟨rfl⟩

  have hC1 : IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := isBiTheta_left hA hC p
  have hC2 : IsBiTheta ψ A S A' fun u v => omb q (C u) v := _root_.GlobalTheory.BiActRight.isBiTheta_act_right D ψ A S A' χS' χA' omb hB C hC q
  have hC3 : IsBiTheta ψ A S A' fun u v => oma p (fun u' => omb q (C u') v) u := isBiTheta_left hA hC2 p
  have hL := hB.om_pres q _ (slice_right hC1 u)
  have hR := slice_right hC3 u

  have hint : ∀ f g : WO S A' → ℂ, IsThetaFunO ψ S A' f → IsThetaFunO ψ S A' g →
      IntegrableOn (fun w => f w * star (g w)) 𝓕 μ := by
    intro f g hf hg
    obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
    obtain ⟨N, hN⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hg
    exact integrableOn_mul_star h𝓕 hf.cont hg.cont hM hN
  have hintS : ∀ f : WO S A' → ℂ, IsThetaFunO ψ S A' f → Integrable (fun w => star (f w)) (μ.restrict 𝓕) := by
    intro f hf
    obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
    refine Measure.integrableOn_of_bounded (M := M) h𝓕 hf.cont.star.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_star]; exact hM x
  have hk : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') := (GlobalTheory.BiTransfer.continuous_dagger S A').measurable

  set Q : WO S A' → ℂ := fun w => omb q (fun v' => oma p (fun u' => C u' v') u) w -
    oma p (fun u' => omb q (C u') w) u with hQ
  suffices hQ0 : Q = 0 by
    have := congrFun hQ0 v
    simp only [hQ, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  refine GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta D ψ hψ S A' μ 𝓕 hcov.1 hcov.2.1 Q (hL.cont.sub hR.cont) (fun γ w => ?_) (fun f hf => ?_)
  · simp only [hQ]
    rw [mul_sub, ← hL.quasi γ w, ← hR.quasi γ w]
  ·
    set g := omb q⁻¹ f with hg
    have hgt : IsThetaFunO ψ S A' g := hB.om_pres _ _ hf
    have hfg : omb q g = f := by
      rw [hg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

    have e1 : ∫ w in 𝓕, omb q (fun v' => oma p (fun u' => C u' v') u) w * star (f w) ∂μ =
        ∫ w in 𝓕, oma p (fun u' => C u' w) u * star (g w) ∂μ := by
      have := GlobalTheory.WeilPairing.thPair_om_eq D ψ S A' χS' χA' omb hB v0 q _ g (slice_right hC1 u) hgt
      rw [hfg] at this
      exact this

    have e2 : ∫ w in 𝓕, oma p (fun u' => omb q (C u') w) u * star (f w) ∂μ =
        ∫ w in 𝓕, oma p (fun u' => C u' w) u * star (g w) ∂μ := by
      have c2 := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ (GlobalTheory.BiTransfer.isThetaFunO_join d hC2)
        (WO S A') (μ.restrict 𝓕) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') (fun w => star (f w)) hk (hintS f hf) p).2 u
      have c1 := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ (GlobalTheory.BiTransfer.isThetaFunO_join d hC)
        (WO S A') (μ.restrict 𝓕) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') (fun w => star (g w)) hk (hintS g hgt) p).2 u
      simp only [GlobalTheory.BiTransfer.join_symm, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger] at c1 c2
      have inner : (fun u' => ∫ w, star (f w) * omb q (C u') w ∂(μ.restrict 𝓕)) =
          fun u' => ∫ w, star (g w) * C u' w ∂(μ.restrict 𝓕) := by
        funext u'
        have := GlobalTheory.WeilPairing.thPair_om_eq D ψ S A' χS' χA' omb hB v0 q _ g (slice_right hC u') hgt
        rw [hfg] at this
        simp only [thPair, v0] at this
        simp only [mul_comm (star _)]
        exact this
      simp only [mul_comm _ (star _)]
      rw [← c2, inner, c1]
    simp only [hQ, sub_mul]
    rw [integral_sub (hint _ _ hL hf) (hint _ _ hR hf), e1, e2, sub_self]

end GlobalTheory.SeeSawComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumSourceInertPlaceEqLatticeIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAtPlaceSrc

open GlobalTheory.WeilAtPlace GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {lam : ℕ →* ℂ} {w₀ : 𝓞 D.host.E} {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}

theorem weilDatum_source_eq_scalar_smul_latticeIntertwiner (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) {g : GA D S} (hg : g ∈ GfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = c • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  obtain ⟨o, ho⟩ := exists_extend (thetaSub ψ S T) Om
  have ho' : ∀ p f (hf : IsThetaFunO ψ S T f), o p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => ho p ⟨f, hf⟩
  have hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (o p f) := fun p f hf => by
    rw [ho' p f hf]
    exact (Om p ⟨f, hf⟩).2
  have hheis : ∀ (g' : GA D S) (k' : GA D T), g' ∈ GfC S → k' ∈ GfC T → ∀ u f, IsThetaFunO ψ S T f →
      o (g', k') (heisO ψ S T u f) = heisO ψ S T (actO S T g' k' u) (o (g', k') f) := by
    intro g' k' hg' hk' u f hf
    obtain ⟨f', h1, h2⟩ := hL.Heisenberg₂ hψ hg' hk' u ⟨f, hf⟩
    rw [ho' _ f hf, ← h2, ← h1]
    exact ho _ f'
  obtain ⟨c, hc, h⟩ := GlobalTheory.ThetaSchur.schur D ψ hψ S T (om (g, 1) * o (g⁻¹, 1⁻¹))
    (fun f hf => hW.om_pres _ _ (hpres _ _ hf))
    (fun u f hf => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hheis _ _ (inv_mem hg) (inv_mem (one_mem _)) u f hf,
        hW.om_heis _ _ _ _ (hpres _ _ hf), GlobalTheory.FinWeilForm.actO_actO_inv])
    (fun μ 𝓕 hμ h𝓕 f hf => by
      rw [Module.End.mul_apply, hW.om_unit μ 𝓕 hμ h𝓕 _ _ (hpres _ _ hf), ho' _ f hf,
        hL.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, hf⟩])
  refine ⟨c, hc, fun f hf => ?_⟩
  have h1 := h _ (hpres (g, 1) f hf)
  rw [Module.End.mul_apply, ← Module.End.mul_apply (o _), ← map_mul,
    show ((g⁻¹, 1⁻¹) * (g, 1) : GA D S × GA D T) = 1 from inv_mul_cancel (g, (1 : GA D T)), map_one,
    Module.End.one_apply] at h1
  rw [h1, ho' _ f hf]

theorem exists_weilScalarCharacter_sourceFinitePart (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om)
    (hlam : GoodNorm (sgO D) lam) :
    ∃ ν : GA D S →* Circle, ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f),
      om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ) := by
  have hs := fun g : GA D S => weilDatum_source_eq_scalar_smul_latticeIntertwiner hψ hW hL hlam (pFin_mem S g)
  choose c hc h using hs
  obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
  have hne : ∀ p, (Om p ⟨f, hf⟩ : WO S T → ℂ) ≠ 0 := fun p h0 => f0 (by
    have h1 : Om p ⟨f, hf⟩ = 0 := Subtype.ext h0
    have h2 := congrArg (Om p⁻¹) h1
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at h2
    exact congrArg Subtype.val h2)
  refine ⟨MonoidHom.mk' (fun g => ⟨c g, mem_sphere_zero_iff_norm.2 (hc g)⟩) fun p q => Circle.ext ?_,
    fun g hg f hf => ?_⟩
  · show c (p * q) = c p * c q
    have e1 : (pFin S (p * q), (1 : GA D T)) = (pFin S p, 1) * (pFin S q, 1) :=
      Prod.ext (map_mul _ _ _) (one_mul _).symm
    have e2 := h (p * q) f hf
    rw [e1, map_mul, Module.End.mul_apply, h q f hf, map_smul, h p _ (Om (pFin S q, 1) ⟨f, hf⟩).2, smul_smul, map_mul,
      Module.End.mul_apply] at e2
    have e3 := smul_left_injective ℂ (hne ((pFin S p, 1) * (pFin S q, 1))) (a₁ := c q * c p) (a₂ := c (p * q)) (by
      simpa only [map_mul, Module.End.mul_apply] using e2)
    rw [← e3, mul_comm]
  · have e := h g f hf
    rwa [pFin_of_mem hg] at e

theorem weilScalar_source_eq_one_nonsplit_unramified (hψ : IsStdChar D ψ (-1)) (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS)
    (hT : IsSelfDualC T ΛT) (hL : IsLatRep hψ.1 ΛS ΛT w₀ lam Om) {ν : GA D S →* Circle}
    (hν : ∀ g ∈ GfC S, ∀ f (hf : IsThetaFunO ψ S T f), om (g, 1) f = (ν g : ℂ) • (Om (g, 1) ⟨f, hf⟩ : WO S T → ℂ))
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hv : NonSplitAt D v ε) (uS : UnramAt ε χS)
    (uT : UnramAt ε χT) {g : GA D S} (hg : SuppPl ε S g) : ν g = 1 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine _root_.GlobalTheory.InertChar.char_eq_one_of_nonSplit D S ΛS hS v ε hv ν (fun k hk hst => ?_) g hg
  have hvac' : ∃ f, f ≠ 0 ∧ IsThetaFunO ψ S T f ∧ ∀ v η, NonSplitAt D v η →
      ∀ u ∈ (latO S T ΛS ΛT fun w => w = v), heisO ψ S T u f = f := by
    obtain ⟨f, f0, hf⟩ := GlobalTheory.FinWeilForm.exists_theta hψ S T
    obtain ⟨e, he, e0⟩ : ∃ e, Fixes (opF hψ.1 S T w₀) (latF S T ΛS ΛT) e ∧ e ≠ 0 := by
      by_contra hn
      push_neg at hn
      have : (⊤ : Submodule ℂ (thetaSub ψ S T)) ≤ ⊥ := by
        rw [← hL.span, Submodule.span_le]
        rintro _ ⟨x, e, he, rfl⟩
        rw [hn e he, map_zero]
        exact zero_mem _
      exact f0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 (this (Submodule.mem_top (x := ⟨f, hf⟩)))))
    refine ⟨e, fun h0 => e0 (Subtype.ext h0), e.2, fun v η hv u hu => ?_⟩
    obtain ⟨b, hb, hb'⟩ := exists_half_of_nonSplit hv
    have hu' := GlobalTheory.PlaceModel.latO_le_top _ hu
    let a : XF S T := XF.mk u (GlobalTheory.SplitScalar.latO_fin hu')
    have ha : a ∈ latF S T ΛS ΛT := hu'
    have e0 : algebraMap (AF D.host.F) (AE D) η • u = u :=
      GlobalTheory.FinWeilForm.placeIdem_smul_self hv.1 hu
    have e1 : a = 2 • (b • a) := by
      rw [two_nsmul, ← add_smul, ← two_mul, hb']
      exact XF.ext e0.symm
    have e2 : b • a ∈ latF S T ΛS ΛT := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b hb _ ha
    have h1 := congrArg Subtype.val (he a ha)
    rw [coe_opF] at h1
    have h2 : phase ψ w₀ a = 1 := by rw [e1]; exact phase_two hL.sd w₀ e2
    rwa [h2, one_smul] at h1
  obtain ⟨f₀, f0, hf₀, hvac⟩ := hvac'
  have hfix := hvac v ε hv
  have hst' := _root_.GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T ΛS ΛT hS hT v ε hv.1 k 1 hst
    (fun y => by rw [GlobalTheory.FinWeilForm.finMat_one, Matrix.one_mulVec])
  have s1 : SuppPl ε T (1 : GA D T) := fun i j => by
    rw [GlobalTheory.FinWeilO.mt_one, sub_self, Matrix.zero_apply, mul_zero]
  have a := _root_.GlobalTheory.VacInert.fixesVacAt_of_unram D ψ hψ S T ΛS ΛT hS hT χS χT om
    ((GlobalTheory.Mem.EtaTilde.exists_etaTilde D).imp fun _ h => ⟨h.1, h.2.2.2, h.2.2.1, h.2.1⟩) hW v ε hv uS uT k 1 hk s1 hst'
    f₀ hf₀ hfix
  have b := hL.inert hv hk s1 (fun u hu => (hst' u).1 hu) ⟨f₀, hf₀⟩ hfix
  have hkf : k ∈ GfC S := GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hv.1).1 hk
  have c := hν k hkf f₀ hf₀
  rw [a, b] at c
  exact Circle.ext (smul_left_injective ℂ f0 (c.symm.trans (one_smul ℂ f₀).symm))

end GlobalTheory.WeilAtPlaceSrc

end

theorem GlobalTheory.WeilAtPlaceSrc.weilDatum_src_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (hψ : IsStdChar D ψ (-1)) (lam : ℕ →* ℂ) (w₀ : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (GlobalTheory.FinWeilO.thetaSub ψ S T)), GlobalTheory.FinWeilO.IsLatRep hψ.1 (frameLat S) (frameLat T) w₀ lam Om → GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ (a : Gv S v) (f : GlobalTheory.FinWeilO.thetaSub ψ S T), om (embV S v a, 1) f = (Om (embV S v a, 1) f : WO S T → ℂ) := by
  intro D ψ S T χS χT om hW hψ lam w₀ Om hL hlam v w h hi uS uT a f
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ν, hν⟩ := GlobalTheory.WeilAtPlaceSrc.exists_weilScalarCharacter_sourceFinitePart hψ hW hL hlam
  obtain ⟨ε, hns, hp⟩ := GlobalTheory.WeilAtPlace.exists_nonSplit_of_inert hi h
  have hsu : GlobalTheory.WeilParts.SuppPl ε S (embV S v a) := (Supp.suppF_iff_of_isPrimeIdem S hp h _).2 ⟨a, rfl⟩
  have hk : embV S v a ∈ GfC S :=
    GlobalTheory.IdemSupport.mem_GfC_of_suppF S (GlobalTheory.IdemSupport.place_comp hΦ hns.1).1 hsu
  have e1 := GlobalTheory.WeilAtPlaceSrc.weilScalar_source_eq_one_nonsplit_unramified hψ hW (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat S)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat T) hL hν hns
    (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uS) (GlobalTheory.WeilAtPlace.unramAt_of_unrAt hp uT) hsu
  have e2 := hν _ hk f.1 f.2
  rw [e1, Circle.coe_one, one_smul] at e2
  exact e2
end

