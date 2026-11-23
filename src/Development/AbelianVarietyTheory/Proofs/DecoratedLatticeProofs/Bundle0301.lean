module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdThetaInt

theorem integrable_theta : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ (Φ : schwartzA θ V.rank n) (g : G D n), Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν) := by
  intro hP D n V hn hr θ hθ ω ν hν Φ g
  set φ := ω g Φ with hφdef
  have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hθ ν hν φ
  have hcont : Continuous φ.1 := (_root_.GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ _ _ φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ φ.1 φ.2)).1
  have hleft := GlobalTheory.SiegelWeilLitCompare.leftInv_theta ω Φ g
  have hterm : ∀ h, theta ω Φ g h = ∑' ξ, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) := fun h => rfl
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ :=
      ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
    have hae' : ∀ᵐ h ∂ν, GlobalTheory.SiegelFormula.absTheta V φ.1 h < ⊤ := by
      have := (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)).ae hae
      filter_upwards [this] with h hh
      rwa [(GlobalTheory.SiegelFormula.leftInv_absTheta V φ.1).descend_mk] at hh
    haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
    haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
    have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E =>
        φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) :=
      hae'.mono fun h hh => Summable.of_enorm hh.ne
    have hlim := aestronglyMeasurable_of_tendsto_ae (μ := ν)
      (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
      (f := fun F h => ∑ ξ ∈ F, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ))
      (fun F => (continuous_finsetSum F fun ξ _ =>
        hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
      (hsum.mono fun h hh => hh.hasSum)
    exact hlim.congr (Filter.Eventually.of_forall fun h => (hterm h).symm)
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.StdThetaInt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMemKfin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.Core.Mi.StepSpans

theorem isKFin_of_mem_kfin {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

end GlobalTheory.Core.Mi.StepSpans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatSchwartzAddSmul
section
namespace I195MixedCoordinates_16a87883d9a2fbb6523804b0

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

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_16a87883d9a2fbb6523804b0

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatAdd

variable {D : D7}

theorem mixS_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source d) T ψ μ 𝓕 (f + g) x = (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source d) T ψ μ 𝓕 f x + (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source d) T ψ μ 𝓕 g x := by
  funext w₀
  have h1 := d.integrableOn_mixS hψ hμ hf x w₀
  have h2 := d.integrableOn_mixS hψ hμ hg x w₀
  simp only [HypDec.integrandS_eq] at h1 h2
  change (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) (f + g))) 0 ∂μ) =
    (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) f)) 0 ∂μ) +
    (∫ a in 𝓕, heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w₀) g)) 0 ∂μ)
  simp only [HypDec.integrandS_eq, Pi.add_apply]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem continuous_mixS {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (T : HSp D) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)} (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) : Continuous ((_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source d) T ψ μ 𝓕 f x) := by
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have c0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
  refine GlobalTheory.MixCont.continuous_covolOne_integral hμ
    (fun (w : WO S₀ T) a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) ?_
    (fun w γ hγ a => d.integrandS_periodic hf x w γ hγ a)
  have e : Function.uncurry (fun (w : WO S₀ T) a =>
      heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0) =
      fun z => ψ (symplOH S T (d.extY T z.2) (d.extX T x)) * f (d.extY T z.2 + d.extX T x + d.ext0 T z.1) := by
    funext z; exact d.integrandS_eq _ _ _ _
  rw [e]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH (cY.comp continuous_snd) continuous_const)).mul
    (hf.cont.comp (((cY.comp continuous_snd).add continuous_const).add (c0.comp continuous_fst)))

theorem integrableOn_mixT_of_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) (S : HSp D) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hc : Continuous f)
    (hq : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (y : Mx D S.rank ρ) (w₀ : WO S T₀) :
    IntegrableOn
      (fun ξ => heisO ψ S T (d.incX S ξ) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0) 𝓕 μ := by
  refine covolOne_integrableOn hμ _ ?_ (GlobalTheory.MixCont.integrandT_periodic_of_quasi d hq y w₀)
  have cX : Continuous (d.incX S) := continuous_const.matrix_mul continuous_id
  simp only [HypDec.integrandT_eq]
  exact (hψ.comp (GlobalTheory.OrientedHeis.continuous_symplOH cX continuous_const)).mul
    (hc.comp ((cX.add continuous_const).add continuous_const))

theorem evalAt_add {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (hg : IsThetaFunO ψ V W g) (x : Mx D W.rank ρ)
    (y : Mx D V₀.rank σ) :
    evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (f + g) x y =
      evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 f x y + evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 g x y := by
  funext w₀
  have h1 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hf x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hf x δ w) y w₀
  have h2 := integrableOn_mixT_of_quasi hψ dW V₀ vT.covol (continuous_mixS hψ dV W vS.covol hg x)
    (fun δ w => GlobalTheory.MixModel.Check.mixS_quasi dV vS.μ vS.𝓕 hg x δ w) y w₀
  simp only [HypDec.integrandT_eq] at h1 h2
  change _root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.target dW V₀ ψ vT.μ vT.𝓕
      (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 (f + g) x) y w₀ =
    _root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.target dW V₀ ψ vT.μ vT.𝓕
      (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 f x) y w₀ +
    _root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.target dW V₀ ψ vT.μ vT.𝓕
      (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 g x) y w₀
  rw [mixS_add hψ dV W vS.covol hf hg x]
  change (∫ a in vT.𝓕, heisO ψ V₀ W (dW.incX V₀ a) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w₀) (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 f x + _root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 g x))) 0 ∂vT.μ) = _
  change (∫ a in vT.𝓕, heisO ψ V₀ W (dW.incX V₀ a) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w₀) (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 f x + _root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 g x))) 0 ∂vT.μ) =
    (∫ a in vT.𝓕, heisO ψ V₀ W (dW.incX V₀ a) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w₀) (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 f x))) 0 ∂vT.μ) +
    (∫ a in vT.𝓕, heisO ψ V₀ W (dW.incX V₀ a) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w₀) (_root_.I195MixedCoordinates_16a87883d9a2fbb6523804b0.source dV W ψ vS.μ vS.𝓕 g x))) 0 ∂vT.μ)
  simp only [HypDec.integrandT_eq, Pi.add_apply]
  rw [← integral_add h1 h2]
  congr 1; funext a; ring

theorem flatFB_add_smul : ∀ (D : D7), FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (f g : WO J.W B.V → ℂ),
    IsThetaFunO ψ J.W B.V f → IsThetaFunO ψ J.W B.V g →
    flatFB st (f + g) = flatFB st f + flatFB st g ∧ ∀ a : ℂ, flatFB st (a • f) = a • flatFB st f := by
  intro D hF ψ hψ σ J B st f g hf hg
  refine ⟨?_, fun a => GlobalTheory.HandHom.flatFB_smul st a f⟩
  have hif := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 f hf).1
  have hig := (hF ψ hψ J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d st.vS st.vT st.vU (GlobalTheory.Unf.FlatTheta.lastQ B)
    (GlobalTheory.Unf.FlatTheta.lastQ_indep B) 0 g hg).1
  rw [GlobalTheory.Unf.FlatTheta.rat_lastQ] at hif hig
  funext w
  simp only [flatFB, flatLast, flatAt, Pi.add_apply]
  rw [← integral_add (hif w) (hig w)]
  congr 1; funext u
  simp only [flatFun, evalAt_add hψ.1.1 J.d B.d st.vS st.vT hf hg, Pi.add_apply, mul_add]

end GlobalTheory.FlatAdd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawLoc
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocOm

def LawLoc {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (ω : Om S T) (μS μT : kˣ →* ℂˣ) (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO S T → ℂ))
    (g : GA D S) (gk : GL Y' k) (h : GA D T) (hk : GL Y k) : Prop :=
  ∀ Φ Φ' : SB (Matrix Y Y' k),
    Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ.1 →
      ω (g, h) (Tm Φ) = Tm Φ'

def Enl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (gk : GL Y' k) (hk : GL Y k) : Prop :=
  ∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) →
    ∀ r q, ((↑(hk⁻¹) : Matrix Y Y k) * x * (↑gk : Matrix Y' Y' k)) r q ∈ 𝒪[k]

end GlobalTheory.LocOm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.ResLift

open GlobalTheory.AdelicU

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

def swapProj (φ : SplitProj D v) : D.host.E ⊗[D.host.F] Fv D.host.F v →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.comm D.host.F D.host.E (Fv D.host.F v)).toAlgHom.toRingHom

theorem swapProj_one_tmul (φ : SplitProj D v) (a : Fv D.host.F v) : swapProj φ ((1 : D.host.E) ⊗ₜ[D.host.F] a) = a := by
  change φ (a ⊗ₜ[D.host.F] (1 : D.host.E)) = a
  exact φ.commutes a

theorem swapProj_prV (φ : SplitProj D v) (z : EAf D) : swapProj φ (Formalism.UG.prV v z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b y => rfl

theorem swapProj_prV_oToS (φ : SplitProj D v) (x : 𝓞 D.host.E) :
    swapProj φ (Formalism.UG.prV v (Formalism.L2.DIV.oToS D.host.F D.host.E x).1) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E) := by
  rw [swapProj_prV, Formalism.L2.DIV.oToS_coe]
  change φ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 1) ⊗ₜ[D.host.F] (x : D.host.E)) = _
  rw [map_one]
  rfl

theorem isIdemOf_idem (φ : SplitProj D v) : IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]
  rfl

theorem eq_splitPrime {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP) :
    PP = splitPrime (GlobalTheory.SplitProjChart.emb φ) :=
  HeightOneSpectrum.ext (Ideal.ext fun x => (hφ x).trans (mem_splitPrime (GlobalTheory.SplitProjChart.emb φ) x).symm)

theorem exists_mem_only (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : ∃ p ∈ (splitPrime τ).asIdeal,
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v → p ∈ P.asIdeal → P = splitPrime τ := by
  obtain ⟨p, hp, hp'⟩ : ∃ p ∈ (splitPrime τ).asIdeal, p ∉ (splitPrime (τ.comp D.sp.cm.sig)).asIdeal := by
    by_contra hc
    push Not at hc
    have h := (splitPrime τ).isMaximal.eq_of_le (splitPrime (τ.comp D.sp.cm.sig)).isPrime.ne_top hc
    exact splitPrime_comp_ne (isCMExt_host D) τ (HeightOneSpectrum.ext h.symm)
  refine ⟨p, hp, fun P hP hpP => ?_⟩
  have hm : P.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨P.isPrime, ⟨hP ▸ rfl⟩⟩
  rw [primesOver_eq_split (isCMExt_host D) τ] at hm
  rcases hm with h | h
  · exact HeightOneSpectrum.ext h
  · exact absurd (h ▸ hpP) hp'

theorem resS_eq {φ : SplitProj D v} {PP : Pl D.host.E} (hφ : IsProjAt φ PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (x : 𝓞 D.host.E)
    (h : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ s.1 - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) < 1) :
    resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal x := by
  obtain ⟨p, hp, hp'⟩ := exists_mem_only (GlobalTheory.SplitProjChart.emb φ)
  rw [← eq_splitPrime hφ] at hp hp'
  obtain ⟨ρ, ι, hρ, hρr⟩ := GlobalTheory.SplitResidue.exists_residue_equiv D.host.F D.host.E v PP
    (swapProj φ) p (swapProj_one_tmul φ) ((hφ p).1 hp) hp'
  have h0 : IsLocalRing.residue _ (ρ s) = IsLocalRing.residue _ (ρ (oToS D.host.F D.host.E x)) := by
    refine Ideal.Quotient.eq.2 ((GlobalTheory.SplitResidue.mem_maximalIdeal_iff v _).2 ?_)
    rw [AddSubgroupClass.coe_sub, hρ, hρ, swapProj_prV_oToS, swapProj_prV]
    exact h
  rw [hρr, hρr, resS_oToS] at h0
  exact ι.injective h0

theorem exists_unit_lift {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {e : A} (hee : e * e = e)
    (hs : Function.Surjective π) (hk : ∀ a, π a = 0 ↔ e * a = 0) (u : Kˣ) :
    ∃ x : Aˣ, (1 - e) * (x : A) = 1 - e ∧ e * ((x : A) - 1) = (x : A) - 1 ∧ π x = u := by
  obtain ⟨U, hU⟩ := hs (u : K)
  obtain ⟨U', hU'⟩ := hs ((u⁻¹ : Kˣ) : K)
  have h1 : e * (U * U' - 1) = 0 := (hk _).1 (by rw [map_sub, map_mul, hU, hU', map_one, Units.mul_inv, sub_self])
  have h2 : π (1 - e) = 0 := (hk _).2 (by linear_combination -hee)
  have h3 : π e = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h2
    exact h2.symm
  refine ⟨⟨e * U + (1 - e), e * U' + (1 - e), by linear_combination h1 + (U * U' - U - U' + 1) * hee,
    by linear_combination h1 + (U * U' - U - U' + 1) * hee⟩, ?_, ?_, ?_⟩
  · change (1 - e) * (e * U + (1 - e)) = 1 - e
    linear_combination (1 - U) * hee
  · change e * (e * U + (1 - e) - 1) = e * U + (1 - e) - 1
    linear_combination (U - 1) * hee
  · change π (e * U + (1 - e)) = u
    rw [map_add (f := _), map_mul, h2, h3, hU, one_mul, add_zero]

theorem liftsChar_of_resAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (PP : Pl D.host.E) (a : (kP PP)ˣ →* ℂˣ), GlobalTheory.StepLaw.ResAt χ PP a → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) → LiftsChar φ PP μ a := by
  intro D χ PP a hres v φ hφ μ hμ u k ⟨x0, hx0k, hx0⟩
  have he := isIdemOf_idem φ
  generalize GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) = e at he
  have hch := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hAt : Formalism.L2.NTheta.IsIdemAt e PP := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hφ).2.2 e he).1
  obtain ⟨x, h1, h2, h3⟩ := exists_unit_lift (rdA φ) he.1.1 hch.1 hch.2.1 u
  have hu : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F := by
    have h4 : (u : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F := hx0.le
    have h5 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ∈ v.adicCompletionIntegers D.host.F :=
      apply_coe_mem (GlobalTheory.SplitProjChart.emb φ) x0
    have h6 := add_mem h4 h5
    rwa [sub_add_cancel] at h6
  have hint : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have h4 : finPart D (e * ((x : AE D) - 1)) ∈ intAE D := by
      refine (hch.2.2.2 _).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
      rw [RingHom.map_sub, h3, RingHom.map_one]
      exact sub_mem hu (one_mem _)
    have h5 := (GlobalTheory.SplitDec.int_iff _).1 h4
    rw [h2, RingHom.map_sub, RingHom.map_one] at h5
    have h6 := add_mem h5 (one_mem _)
    rwa [sub_add_cancel] at h6
  have hk : resS D.host.F PP ⟨_, hint⟩ = Ideal.Quotient.mk PP.asIdeal x0 := by
    refine resS_eq hφ _ x0 ?_
    change Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ (toEAf D (x : AE D)) - _) < 1
    rw [GlobalTheory.SplitProjChart.rdE_toEAf, h3]
    exact hx0
  rw [hμ x u ⟨e, he, h1, h3⟩]
  exact Units.ext (hres e hAt x h2 hint k (hk.trans hx0k).symm)

end GlobalTheory.ResLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
section
namespace I195MixedCoordinates_6f24fc13148e8b26f9b44878

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

end I195MixedCoordinates_6f24fc13148e8b26f9b44878

public noncomputable abbrev _root_.I195MixedCoordinates_0c0ca1362b7f04403a7fc3a9.source :=
  @_root_.I195MixedCoordinates_6f24fc13148e8b26f9b44878.source

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem extY_map_infPart_eq_zero {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (a : Mx D T.rank ρ) (ha : a.map (infPart D) = 0) : (d.extY T a).map (infPart D) = 0 := by
  rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]

theorem mixS_support_inBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w, (_root_.I195MixedCoordinates_6f24fc13148e8b26f9b44878.source d) T ψ v.μ v.𝓕 f x w ≠ 0 → InBox K x := by
  intro D ψ hψ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hbox⟩ := _root_.GlobalTheory.AnnihBox.annihilator_inBox D ψ hψ S S₀ T ρ d U hU
  refine ⟨K, hK, fun f hf x w hne => hbox x fun a ha haU => ?_⟩
  have hY := (_root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf.1).2.1 x a
  rw [hf.2 _ haU (extY_map_infPart_eq_zero d T a ha)] at hY
  have hw := congrFun hY w
  rw [Pi.smul_apply, smul_eq_mul] at hw
  have h1 : (ψ (symplO S T (d.extX T x) (d.extY T a)) - 1) * (_root_.I195MixedCoordinates_6f24fc13148e8b26f9b44878.source d) T ψ v.μ v.𝓕 f x w = 0 := by
    rw [sub_mul, one_mul, ← hw, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hne)

end GlobalTheory.Unf
end

