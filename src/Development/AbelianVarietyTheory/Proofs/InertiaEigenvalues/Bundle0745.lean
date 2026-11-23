module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDiagTangentUnitFrameHolomorphicArcLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLocalMatrixDivisionPointQuotientStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_localMatrixDivisionPointQuotient : ∀ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (N m n : ℕ), 0 < N → Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) = Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  first | exact @GlobalTheory.DivPtLocal.Count.card_locQ | exact GlobalTheory.DivPtLocal.Count.card_locQ | (intros; apply GlobalTheory.DivPtLocal.Count.card_locQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArc
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ArcBdd

theorem norm_prod_pow_le {ι : Type} [Fintype ι] (f : ι → ℂ) (e : ι → ℕ) (B : ℝ) (hf : ∀ i, ‖f i‖ ≤ B) :
    ‖∏ i, f i ^ e i‖ ≤ B ^ (∑ i, e i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hf i) _

theorem pnorm_unitFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (hx : GlobalTheory.FrameNorm.IsUnitFr X x) :
    X.pnorm la P x = ‖P x‖ := by
  unfold Data.pnorm
  have h1 : ∀ τ (i : Fin r), ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ = 1 := by
    intro τ i
    rw [norm_div, hx τ i.succ, hx τ i.castSucc, div_one]
  simp only [h1, Real.one_rpow, Finset.prod_const_one, mul_one]

theorem holSub_bdd {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : (k : Comp) → Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X)
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) :
    ∃ C : ℝ, ∀ x ∈ (X k).dom, (X k).pnorm (la k) (P k) x ≤ C := by
  unfold Formalism.L2.PjFree.holSub at hP
  induction hP using Submodule.span_induction with
  | mem P hP => exact (hP k).1.2
  | zero => exact ⟨0, fun x _ => by
      have := Formalism.L2.Pj.pnorm_zero (X k) (la k) x
      simpa using this.le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨C1, h1⟩ := hP
    obtain ⟨C2, h2⟩ := hQ
    exact ⟨C1 + C2, fun x hx => (Formalism.L2.Pj.pnorm_add_le (X k) (la k) (P k) (Q k) x).trans (add_le_add (h1 x hx) (h2 x hx))⟩
  | smul s P _ hP =>
    obtain ⟨C1, h1⟩ := hP
    exact ⟨‖s‖ * C1, fun x hx => by
      have := Formalism.L2.Pj.pnorm_smul (X k) (la k) s (P k) x
      simp only [Pi.smul_apply] at this ⊢
      rw [this]
      exact mul_le_mul_of_nonneg_left (h1 x hx) (norm_nonneg _)⟩

theorem cusp_bounded_at_unitFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Formalism.L2.PjFree.GoodEmb c σ → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ M : ℝ, ∀ (k : (U σ).Comp) (x : ((U σ).X k).dom), GlobalTheory.FrameNorm.IsUnitFr ((U σ).X k) x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x))‖ ≤ M := by
  intro E _ _ _ H Dw l Xo c r U σ a' n F hG hF
  haveI := (U σ).fin
  have hF' : Formalism.L2.PjFree.rdU (U σ) F ∈ Formalism.L2.PjFree.holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) := by
    unfold Formalism.L2.PjFree.cusp at hF
    rw [Submodule.mem_inf, Submodule.mem_iInf] at hF
    have := hF.2 σ
    rw [Submodule.mem_iInf] at this
    exact Submodule.mem_comap.mp (this hG)
  choose C hC using holSub_bdd (U σ).X (Formalism.L2.PjFree.laU (U σ) a' n) _ hF'
  refine ⟨∑ k, max (C k) 0, fun k x hx => ?_⟩
  have h1 := hC k x.1 x.2
  rw [pnorm_unitFr _ _ _ _ hx] at h1
  have h2 : Formalism.L2.PjFree.rdU (U σ) F k x.1 = Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) := by
    simp [Formalism.L2.PjFree.rdU, x.2]
  rw [← h2]
  refine h1.trans ((le_max_left (C k) 0).trans ?_)
  exact Finset.single_le_sum (f := fun k => max (C k) 0) (fun k _ => le_max_right _ _) (Finset.mem_univ k)

theorem cusp_values_bounded_on_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c r U σ Uw _ _ O _ β Y a χ W Ha th Θ z hU hG hz a' n F hD hF
  obtain ⟨T1, B1, h1⟩ := _root_.GlobalTheory.ArcLieBound.norm_diag_le E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨T2, B2, h2⟩ := _root_.GlobalTheory.ArcGenBound.gen_ratio_bounded E H Dw l Xo c r σ (U σ) Uw O β Y a χ W Ha th Θ z hG (hU σ hG) hz
  obtain ⟨M, hM⟩ := cusp_bounded_at_unitFr E H Dw l Xo c r U σ a' n F hG hF
  have hev : GlobalTheory.Reg.EvLaws Xo c := by
    have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
    obtain ⟨-, -, hwd, hwt, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hB E H Dw l Xo c
    have hbc : GlobalTheory.Reg.FrBC Xo c := fun S T _ _ _ _ φ y =>
      GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c S T φ y
    exact ⟨hwd, _root_.GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c, hwt, hbc⟩
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  set B := max 1 (max B1 B2)
  refine ⟨max T1 T2, max M 0 * B ^ (∑ i, ex Dw a' n i), ?_⟩
  intro w hw yw hyw
  obtain ⟨k, x, t, hux, hb⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r (U σ) hG (hU σ hG)).2 yw
  have hsc := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a' n F (Formalism.L2.PjFree.cusp_le_sec Xo c U a' n hF) (CAt σ)).2 inferInstance).1 t _ _ hb
  have ht : ∀ i, ‖Formalism.L2.PjFree.toC (t i : CAt σ)‖ ≤ B := by
    intro i
    rcases i with _ | j
    · exact (h2 w (lt_of_le_of_lt (le_max_right _ _) hw) yw hyw k x t hux hb).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (h1 w (lt_of_le_of_lt (le_max_left _ _) hw) yw hyw k x t hux hb j).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hw' : ‖Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t)‖ ≤ B ^ (∑ i, ex Dw a' n i) :=
    norm_prod_pow_le (fun i => Formalism.L2.PjFree.toC (t i : CAt σ)) (ex Dw a' n) B ht
  rw [hsc]
  change ‖(Formalism.L2.PjFree.toC (wchar (ex Dw a' n) t) * Formalism.L2.PjFree.toC (evR Xo c F ((U σ).un k x)) : ℂ)‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul ((hM k x hux).trans (le_max_left _ _)) hw' (norm_nonneg _) (le_max_right _ _)

end GlobalTheory.ArcBdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquivStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_inert_tensor_completion_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  first | exact @GlobalTheory.InertTransferCanon.exists_canonical_equiv | exact GlobalTheory.InertTransferCanon.exists_canonical_equiv | (intros; apply GlobalTheory.InertTransferCanon.exists_canonical_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FormInner

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax


omit [IsCMField L] in
theorem exists_trunc (b : AFplus L) : ∃ c : AFplus L, (∀ w, c w ∈ w.adicCompletionIntegers (maximalRealSubfield L)) ∧
    ∀ w, b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → c w = b w := by
  have h : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), ∃ z : w.adicCompletion (maximalRealSubfield L),
      z ∈ w.adicCompletionIntegers (maximalRealSubfield L) ∧ (b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → z = b w) := by
    intro w
    by_cases hw : b w ∈ w.adicCompletionIntegers (maximalRealSubfield L)
    · exact ⟨b w, hw, fun _ => rfl⟩
    · exact ⟨0, zero_mem _, fun h => absurd h hw⟩
  choose z h1 h2 using h
  exact ⟨⟨z, Filter.Eventually.of_forall h1⟩, h1, h2⟩

theorem exists_int_off (z : AL L) : ∃ S : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∃ Y ∈ ALint L,
    ∀ w ∉ S, ReciprocityTheory.Aut.compAt L w z = ReciprocityTheory.Aut.compAt L w Y := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, zero_mem _, fun _ _ => rfl⟩
  | add x y hx hy =>
    obtain ⟨S, Y, hY, h⟩ := hx
    obtain ⟨S', Y', hY', h'⟩ := hy
    refine ⟨S ∪ S', Y + Y', add_mem hY hY', fun w hw => ?_⟩
    rw [Finset.mem_union, not_or] at hw
    rw [map_add (f := _), map_add (f := _), h w hw.1, h' w hw.2]
  | tmul x a =>
    obtain ⟨m, hm, o, ho⟩ := GlobalTheory.FinTypCount.exists_nat_smul_int x
    have hm' : (m : maximalRealSubfield L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    obtain ⟨b, hb⟩ : ∃ b : AFplus L, b = (m : maximalRealSubfield L)⁻¹ • a := ⟨_, rfl⟩
    have e : (x ⊗ₜ[maximalRealSubfield L] a : AL L) = (o : L) ⊗ₜ[maximalRealSubfield L] b := by
      rw [ho, hb, ← Nat.cast_smul_eq_nsmul (maximalRealSubfield L), TensorProduct.smul_tmul, smul_inv_smul₀ hm']
    have hfin : {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) |
        b w ∉ w.adicCompletionIntegers (maximalRealSubfield L)}.Finite := Filter.eventually_cofinite.1 b.2
    obtain ⟨c, hc, hc'⟩ := exists_trunc b
    refine ⟨hfin.toFinset, (o : L) ⊗ₜ[maximalRealSubfield L] c, GlobalTheory.FinTypCount.tmul_mem_ALint o hc, fun w hw => ?_⟩
    rw [e, compAt_tmul, compAt_tmul, hc' w (by simpa using hw)]

theorem mem_ALint_of_comp (z : AL L) (h : ∀ w, ∃ Y ∈ ALint L, ReciprocityTheory.Aut.compAt L w Y = ReciprocityTheory.Aut.compAt L w z) : z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, hS⟩ := exists_int_off z
  choose Z hZ e using h
  have key : z - (Y + ∑ v ∈ S, (Z v - Y) * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1)) = 0 := by
    apply eq_zero_of_compAt
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_add (f := _), map_sum]
    simp only [map_mul, compAt_tmul]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => by rw [sgl_ne L v 1 (Ne.symm hv), TensorProduct.tmul_zero, mul_zero])
        (fun h => absurd hw h), sgl_same, ← Algebra.TensorProduct.one_def, mul_one, map_sub, e]
      ring
    · rw [Finset.sum_eq_zero fun v hv => by
        rw [sgl_ne L v 1 (fun h : w = v => hw (h ▸ hv)), TensorProduct.tmul_zero, mul_zero], hS w hw]
      ring
  rw [sub_eq_zero.1 key]
  exact add_mem hY (Subring.sum_mem _ fun v _ => mul_mem (sub_mem (hZ v) hY) (one_tmul_sgl_mem L v 1 (one_mem _)))

theorem le_Umax_of_prod {J : Subgroup (GAf L n)} (hJ : NG.IsProdLevel J)
    (h : ∀ v, ∀ κ ∈ J, TrivOutside {v} κ → κ ∈ Umax L n) : J ≤ Umax L n := by
  intro κ hκ i j
  refine mem_ALint_of_comp _ fun w => ?_
  obtain ⟨κ', h1, h2, h3⟩ := hJ κ hκ w
  exact ⟨_, h w κ' h1 h2 i j, congrFun (congrFun h3 i) j⟩

theorem mem_Umax_of_para (s : SplitPlace L) {r : ℕ} {κ : GAf L n} (h1 : TrivOutside {s.v} κ) (h2 : NG.ParaRT s r (s.loc n κ)) :
    κ ∈ Umax L n := by
  have h := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 h2.1
  exact GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ h1 h.1 (fun i j => by
    rw [map_inv]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h.2 i j))

end Plain

theorem exists_split_of_gPl (D : D7) : ∀ v ∈ Formalism.L2.gPl D, ∃ (k : Fin 2) (u : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.v = v ∧ s.w = D.naut.plGw k u := by
  rintro v ⟨w, hw, k, hk⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DimPartsCompare.cover k w hk
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, u⟩
  refine ⟨k, u, s, HeightOneSpectrum.ext ?_, hs⟩
  rw [← s.w_under, hs]
  refine Eq.trans ?_ hw
  rcases hu with rfl | rfl
  · rfl
  · ext a
    refine GlobalTheory.DimPartsCompare.isConjPl_cPl _ _ _ ?_
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
    exact ((IsCMField.complexConj D.host.E).commutes (a : maximalRealSubfield D.host.E)).symm

theorem level_le_Umax {D : D7} {M : MtFam D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (h : MtInput D M tup Q) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J ≤ Umax D.host.E D.R.nV := by
  refine le_Umax_of_prod (h.prod w j) fun v κ hκ hv => ?_
  by_cases hg : v ∈ Formalism.L2.gPl D
  · obtain ⟨k, u, s, rfl, hs⟩ := exists_split_of_gPl D v hg
    obtain ⟨ψ₀, ξ, -, -, hl⟩ := h.uni w j k u s hs
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ).1
  by_cases hq : v ∈ qPl D (tup (D.what₂.muTw w) j)
  · obtain ⟨s, ξ, rfl, -, hl⟩ := h.para w j v hq
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ)
  · refine (h.hyp w j κ fun u hu => hv u ?_).1.1 hκ
    rintro rfl
    exact hu fun h' => h'.elim hg hq

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.DepthZeroPass

theorem fixed_ne_bot_of_isSubquotient {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (hρ : IsSmooth ρ) (h : IsSubquotient τ ρ)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (hτ : fixed τ H ≠ ⊥) : fixed ρ H ≠ ⊥ := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hτ
  obtain ⟨u, rfl⟩ := hf w
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g : G | S.toRepresentation g v = v} = {g : G | ρ g (v : V) = v} := by
      ext g
      simp only [Set.mem_setOf_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  obtain ⟨v, hv, hfv⟩ := IwahoriOnto.exists_fixed_map_eq hS hH f.toLinearMap u fun g hg => by
    have h1 := mem_fixed.1 hw g hg
    show f (S.toRepresentation g u) = f u
    exact (f.isIntertwining _ _ g u).trans h1
  refine (Submodule.ne_bot_iff _).2 ⟨(v : V), mem_fixed.2 fun g hg => ?_, ?_⟩
  · have := mem_fixed.1 hv g hg
    exact congrArg Subtype.val this
  · intro h0
    apply hw0
    have hv0 : v = 0 := Subtype.ext h0
    have hfv' : f v = f u := hfv
    rw [← hfv', hv0, map_zero]

theorem fixed_piTensor_ne_bot {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (H : ∀ a, Subgroup (Γ a)) (h : ∀ a, fixed (ρ a) (H a) ≠ ⊥) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ H) ≠ ⊥ := by
  choose v hv hv0 using fun a => (Submodule.ne_bot_iff _).1 (h a)
  choose l hl using fun a => Module.Projective.exists_dual_eq_one ℂ (hv0 a)
  refine (Submodule.ne_bot_iff _).2 ⟨PiTensorProduct.tprod ℂ v, mem_fixed.2 fun g hg => ?_, fun h0 => ?_⟩
  · rw [piTensor_tprod]
    congr 1
    funext a
    exact mem_fixed.1 (hv a) (g a) (hg a trivial)
  · have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap l)) h0
    simp [hl] at this

theorem isCompact_leviKOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] :
    IsCompact (leviKOne k m : Set (Levi k m)) := by
  rw [leviKOne, Subgroup.coe_pi]
  exact isCompact_univ_pi fun a => levelPre_bot (k := k) (n := m a) ▸ isCompact_levelPre ⊥

theorem depthZeroInduction : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInduction := by
  intro hG hBZ hZ k _ _ _ _ _ x s hs hfix
  obtain ⟨r, u, e, hu, hsq⟩ := GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport hG hBZ hZ k x s hs
  have hxs : IsSmooth x.rep := x.2.rep.smooth
  have h1 : fixed (piTensor fun a => (u a).rep) (leviKOne k fun a => Fin (u a).1) ≠ ⊥ :=
    fixed_piTensor_ne_bot _ _ fun a => hfix _ (hu a)
  have h2 := fixed_ne_bot_of_isSubquotient (isSmooth_jac e hxs) hsq isCompact_leviKOne h1
  obtain ⟨y, hy1, hy0⟩ := (Submodule.ne_bot_iff _).1 h2
  have hy2 : y ∈ fixed (jacU e x.rep) (leviKOne k fun a => Fin (u a).1) := mem_fixed.2 fun g hg => by
    have h3 := mem_fixed.1 hy1 g hg
    have h4 : deltaHalf k (fun a => Fin (u a).1) g = 1 :=
      deltaHalf_of_mem_leviK fun a _ => StepData.KOne_le_KO (hg a trivial)
    simpa [GlobalTheory.SmGL.jac, twist_apply, h4] using h3
  obtain ⟨v, hv, rfl⟩ := _root_.GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq k e x.rep ((hBZ k).1 _ _ x.rep hxs x.2.rep.irr) y hy2
  refine (Submodule.ne_bot_iff _).2 ⟨v, mem_fixed.2 fun g hg => mem_fixed.1 hv g (KOne_le_proRad e hg), ?_⟩
  rintro rfl
  exact hy0 rfl

end GlobalTheory.DepthZeroPass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorThroughFrameEvalFinitePointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_through_frame_eval_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (D : InertDatum L n v w) (U0 : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU D.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ y, D.loc y = b⁻¹ * cLoc w (F.j y) * b) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU D.σw n), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U0, NG.rt L n κ f = f) → ∀ (lam : W →ₗ[ℂ] ℂ) (φ : UA L n → ℂ), (∀ g, φ (F.j g) = lam (f g)) → ∀ g, GlobalTheory.LFun.heckeVec ((RU L n).comp (locU n w).subtype) ((Formalism.UG.KU D.σw n).comap p) (fun x => h (p x)) φ (F.j g) = lam (heckeFunI L n U0 D h f g) := by
  first | exact @GlobalTheory.InertTransfer.heckeVec_frame_eval | exact GlobalTheory.InertTransfer.heckeVec_frame_eval | (intros; apply GlobalTheory.InertTransfer.heckeVec_frame_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.LocLanglands.isL_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (l : List (Segment k)) (l' : List (Segment k')) (x : IrrGL (k := k)) (x' : IrrGL (k := k')), List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) l l' → RepRel i x x' → IsL (l : Multiset (Segment k)) x.rep → IsL (l' : Multiset (Segment k')) x'.rep := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi l l' x x' hl hx hL
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero k k' i hi
  have hC := (GlobalTheory.T.transport_keeps_cuspidal_twists_characters k k' i hi).1
  have hprod := GlobalTheory.T.transport_keeps_products_cosocles k k' i hi
  have hcusp : ∀ y, y.IsCusp → (T y).IsCusp := fun y hy => (hC y (T y) ((hT _ _).2 rfl)).1.1 hy
  have hnu : ∀ (y : IrrGL (k := k)) (s : ℂ), T (y.nu s) = (T y).nu s := fun y s =>
    (hT _ _).1 ((hC y (T y) ((hT _ _).2 rfl)).2 s)
  have hcls : ∀ {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      (y : IrrGL (k := K)), GlobalTheory.LocLanglands.cls y.2.rep = y := by
    intro K _ _ _ _ y
    obtain ⟨n, c⟩ := y
    unfold GlobalTheory.LocLanglands.cls
    exact congrArg (Sigma.mk n) c.cl_rep

  have H : ∀ (y : IrrGL (k := k)) (y' : IrrGL (k := k')), RepRel i y y' → ∀ (r r' : ℕ) (e : r = r') (xs : Fin r → IrrGL (k := k))
      (xs' : Fin r' → IrrGL (k := k')) (hd : ∑ a, (xs a).1 = y.1) (hd' : ∑ a, (xs' a).1 = y'.1),
      (∀ a, RepRel i (xs a) (xs' (Fin.cast e a))) →
      IsCosocle y.rep (prodIrr xs hd) → IsCosocle y'.rep (prodIrr xs' hd') := by
    intro y y' hy r r' e xs xs' hd hd' hxs hc
    subst e
    obtain ⟨n, c⟩ := y
    obtain ⟨n', c'⟩ := y'
    have e : n' = n := by
      have := hTd ⟨n, c⟩
      rw [(hT _ _).1 hy] at this
      exact this
    subst e
    exact hprod r n' xs xs' hd hd' c.rep c'.rep (fun a => hxs a)
      (by rw [hcls ⟨n', c⟩, hcls ⟨n', c'⟩]; exact hy) hc

  obtain ⟨S, hS1, hS2⟩ : ∃ S : Segment k → Segment k', (∀ Δ, (S Δ).first = T Δ.first) ∧ ∀ Δ, (S Δ).len = Δ.len :=
    ⟨fun Δ => Segment.ofFirst (T Δ.first) (hcusp _ Δ.isCusp_first) Δ.len Δ.len_pos,
      fun Δ => Segment.first_ofFirst _ _ _ _, fun Δ => Segment.len_ofFirst _ _ _ _⟩
  have key : ∀ (m : List (Segment k)) (m' : List (Segment k')),
      List.Forall₂ (fun (Δ : Segment k) (Δ' : Segment k') => RepRel i Δ.first Δ'.first ∧ Δ.len = Δ'.len) m m' →
      m' = m.map S := by
    intro m m' hm
    induction hm with
    | nil => rfl
    | @cons Δ Δ' _ _ h _ ih =>
      rw [List.map_cons, ih]
      exact congrArg (· :: _) (Segment.ext_first (by rw [hS1]; exact ((hT _ _).1 h.1).symm)
        (by rw [hS2]; exact h.2.symm))
  have hl' := key l l' hl
  have hprec : ∀ Δ Δ' : Segment k, (S Δ).Precedes (S Δ') → Δ.Precedes Δ' := by
    intro Δ Δ' h
    rw [Segment.precedes_iff, hS2, hS2, hS1, hS1] at h
    rw [Segment.precedes_iff]
    obtain ⟨j, h1, h2, h3, e⟩ := h
    exact ⟨j, h1, h2, h3, T.injective (by rw [hnu]; exact e)⟩
  have hseg : ∀ (Δ : Segment k) (y : IrrGL (k := k)), IsLSeg Δ y.rep → IsLSeg (S Δ) (T y).rep := by
    intro Δ y hy
    unfold IsLSeg at hy ⊢
    obtain ⟨hd, hc⟩ := hy
    have ht : ∀ a, T (Δ.term a) = (S Δ).term (Fin.cast (hS2 Δ).symm a) := fun a => by
      simp only [Segment.term, Fin.val_cast, hS1, hnu]
    have hd' : ∑ a, ((S Δ).term a).1 = (T y).1 := by
      rw [hTd, ← hd]
      refine Fintype.sum_equiv (finCongr (hS2 Δ)) _ _ fun a => ?_
      rw [← hTd (Δ.term _), ht]
      rfl
    exact ⟨hd', H y (T y) ((hT _ _).2 rfl) Δ.len (S Δ).len (hS2 Δ).symm Δ.term (S Δ).term hd hd'
      (fun a => (hT _ _).2 (ht a)) hc⟩
  obtain ⟨r, xs, hd, ⟨Δ, hord, hΔ⟩, hc⟩ := hL
  have hx' : T x = x' := (hT _ _).1 hx
  have hd' : ∑ a, (T (xs a)).1 = x'.1 := by
    rw [← hx', hTd, ← hd]
    exact Finset.sum_congr rfl fun a _ => hTd _
  refine ⟨r, fun a => T (xs a), hd', ⟨fun a => S (Δ a), ⟨?_, fun a b hab hp => hord.2 a b hab (hprec _ _ hp)⟩,
    fun a => hseg _ _ (hΔ a)⟩, H x x' hx r r rfl xs _ hd hd' (fun a => (hT _ _).2 rfl) hc⟩
  rw [hl', ← Multiset.map_coe, ← hord.1, Multiset.map_map]
  rfl
end

