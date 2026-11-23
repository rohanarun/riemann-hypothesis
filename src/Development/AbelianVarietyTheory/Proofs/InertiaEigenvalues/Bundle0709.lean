module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Formalism.AdmissibleDesigns.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
open GlobalTheory.Grow
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.AdjUnfold


set_option maxHeartbeats 4000000 in
theorem integral_val_thF_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t v n b y u
  have hm := hL.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hL.thP.ωP i t
  have hpt := hL.thP.pt_theta i t
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hHV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have hHW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hm.νW i).2
  have hJt : ∀ k, IsThetaFunO R.ψ (Vc D i) (Wc D i) (jointVec R i t v (b k)) := fun k => hpt _
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ u)
  have hFc : Continuous (R.extV i t u) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t u (γ * h) = R.extV i t u h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hGk : ∀ k, RapidDec (Vc D i) (fun h => ⟪R.extV i t u h, b k⟫_ℂ) := fun k =>
    RapidDec.of_isCompact (fun γ hγ h => by simp only [hFi γ hγ h]) (hFc.inner continuous_const) hK
      (fun g => by
        obtain ⟨γ, hγ, c', hc', e⟩ := hKc g
        exact ⟨γ⁻¹, inv_mem hγ, by rw [e, inv_mul_cancel_left]; exact hc'⟩)
  obtain ⟨-, hr, -⟩ := hm.HW i (sg0 D A)
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  have hF : RapidDec (Wc D i) (fun g => starRingEnd ℂ (val R i v y g)) :=
    (rapidDec_of_cuspForm hP hθ (hTm.aut fun ρ => v ρ) (hTm.cusp fun ρ => v ρ)).conj
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin n → GA D (Wc D i) → GA D (Vc D i) → ℂ, Φ = fun k g h =>
      thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) * starRingEnd ℂ (val R i v y g) *
        starRingEnd ℂ ⟪R.extV i t u h, b k⟫_ℂ := ⟨_, rfl⟩
  have hint : ∀ k, Integrable (Function.uncurry (Φ k))
      (((R.νW i).restrict (R.fdW i)).prod ((R.νV i t).restrict (R.fdV i t))) := fun k => by
    rw [hΦ]
    exact GlobalTheory.ChainOnto.ThetaSwap.integrable_prod hθ hω (hJt k) hHV hfdV hHW hfdW (hGk k) hF
  have hthF : ∀ g, R.thF i t u (fun ρ => v ρ) g = ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) ∂(R.νV i t) :=
    fun g => (hL.thP.thF i t).elim fun _ h => (congrFun (h.2 u v) g).trans
      (h.1.eq ((R.extV i t).rangeRestrict u) (PiTensorProduct.tprod ℂ v) g)
  have hexp : ∀ g h, thetaKO (R.ωP i t) h g
      (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) =
      ∑ k, ⟪b k, R.extV i t u h⟫_ℂ * thetaKO (R.ωP i t) h g (jointVec R i t v (b k)) := by
    intro g h
    have e : (R.cV i).ext ((R.HV i t).e u) h = ∑ k, ⟪b k, R.extV i t u h⟫_ℂ • b k := (b.sum_repr' _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    unfold jointVec RealDat.ptP
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, thetaKO, LinearMap.sum_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hL1 : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g =
      ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) := by
    have hae : ∀ᵐ g ∂((R.νW i).restrict (R.fdW i)), ∀ k,
        Integrable (fun h => Φ k g h) ((R.νV i t).restrict (R.fdV i t)) :=
      ae_all_iff.2 fun k => (hint k).prod_right_ae
    filter_upwards [hae] with g hg
    rw [hthF g, ← integral_const_mul]
    have e : ∀ h, star (val R i v y g) * thetaKO (R.ωP i t) h g
        (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ v) ((R.cV i).ext ((R.HV i t).e u) h))) = ∑ k, Φ k g h := by
      intro h
      rw [hexp g h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hΦ, inner_conj_symm, Complex.star_def]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e)]
    exact integral_finsetSum _ fun k _ => hg k
  have hR : ∀ h, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ = ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) := by
    intro h
    simp only [upVec, sum_inner, inner_smul_left]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hΦ, upLift]
    rw [integral_mul_const, ← integral_conj, inner_conj_symm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
  calc ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i)
      = ∫ g in R.fdW i, ∑ k, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) := integral_congr_ae hL1
    _ = ∑ k, ∫ g in R.fdW i, ∫ h in R.fdV i t, Φ k g h ∂(R.νV i t) ∂(R.νW i) :=
        integral_finsetSum _ fun k _ => (hint k).integral_prod_left
    _ = ∑ k, ∫ h in R.fdV i t, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        Finset.sum_congr rfl fun k _ => integral_integral_swap (hint k)
    _ = ∫ h in R.fdV i t, ∑ k, ∫ g in R.fdW i, Φ k g h ∂(R.νW i) ∂(R.νV i t) :=
        (integral_finsetSum _ fun k _ => (hint k).integral_prod_right).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun h => (hR h).symm)

end GlobalTheory.AdjUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcGeneratorRatioBoundedUnitFrame
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

noncomputable section

open scoped Matrix

namespace GlobalTheory.ArcGenBound

open Matrix

theorem affine_pos {T a b c : ℝ} (h : ∀ x s : ℝ, T < s → 0 < a + x * b + s * c) : b = 0 ∧ 0 ≤ c := by
  have h1 := h 0 (T + 1) (by linarith)
  constructor
  · by_contra hb
    have := h (-(a + (T + 1) * c) / b) (T + 1) (by linarith)
    rw [div_mul_cancel₀ _ hb] at this
    linarith
  · by_contra hc
    have hc' : 0 < -c := by linarith [not_le.1 hc]
    have hd : 0 < (a + (T + 1) * c) / (-c) := div_pos (by linarith) hc'
    have := h 0 (T + 1 + (a + (T + 1) * c) / (-c)) (by linarith)
    have e := div_mul_cancel₀ (a + (T + 1) * c) hc'.ne'
    nlinarith

theorem det_im_lower_bound {g : ℕ} (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (T : ℝ) (A B : Matrix (Fin g) (Fin g) ℂ)
    (haff : ∀ w, τ w = A + w • B) (hpos : ∀ w : ℂ, T < w.im → ((τ w).map Complex.im).PosDef) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, T + 1 < w.im → C ≤ ((τ w).map Complex.im).det := by
  have hq : ∀ (w : ℂ) (v : Fin g → ℝ), v ⬝ᵥ ((τ w).map Complex.im) *ᵥ v = v ⬝ᵥ (A.map Complex.im) *ᵥ v +
      w.re * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + w.im * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := by
    intro w v
    have e : (τ w).map Complex.im = A.map Complex.im + w.re • B.map Complex.im + w.im • B.map Complex.re := by
      ext i j
      simp [haff, add_assoc]
    rw [e]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h0 : T < (⟨0, T + 1⟩ : ℂ).im := by simp
  refine ⟨((τ ⟨0, T + 1⟩).map Complex.im).det, (hpos _ h0).det_pos, fun w hw => ?_⟩
  have hw' : T < w.im := by linarith
  have hD : ((τ w).map Complex.im - (τ ⟨0, T + 1⟩).map Complex.im).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((hpos w hw').isHermitian.sub (hpos _ h0).isHermitian) fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hp : ∀ x s : ℝ, T < s → 0 < v ⬝ᵥ (A.map Complex.im) *ᵥ v +
        x * (v ⬝ᵥ (B.map Complex.im) *ᵥ v) + s * (v ⬝ᵥ (B.map Complex.re) *ᵥ v) := fun x s hs => by
      have := (hpos ⟨x, s⟩ hs).dotProduct_mulVec_pos hv
      rwa [star_trivial, hq] at this
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, hq, hq]
    obtain ⟨hb, hc⟩ := affine_pos hp
    have := mul_nonneg (sub_pos.2 hw).le hc
    rw [hb]
    dsimp only
    linarith
  have := GlobalTheory.ClassFin.gramLB_det_mono (hpos _ h0) hD
  rwa [add_sub_cancel] at this

end GlobalTheory.ArcGenBound


open GlobalTheory.ArcGenBound in
theorem GlobalTheory.ArcGenBound.gen_ratio_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∃ T B : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), GlobalTheory.FrameNorm.IsUnitFr (U.X k) x.1 → FrBor t (U.un k x) yw → ‖Formalism.L2.PjFree.toC (t none : CAt σ)‖ ≤ B := by
  intro E _ _ _ H Dw l Xo c r σ U Uw _ _ O _ β Y a χ W Ha th Θ z _ _ _
  have haff : ∀ w, Θ.τ w = Matrix.of (fun i k => (Θ.h *ᵥ Ha.P₀ (Θ.bas (Pi.single (.inr k) 1))) i) +
      w • Matrix.of (fun i k => (Θ.h *ᵥ Ha.N (Θ.bas (Pi.single (.inr k) 1))) i) := by
    intro w
    ext i k
    have e := congrFun (Θ.per w k).2 i
    rw [Ha.Pw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one] at e
    simpa [Matrix.transpose_apply] using e.symm
  obtain ⟨C, hC, hdet⟩ := det_im_lower_bound Θ.τ Ha.T _ _ haff (fun w hw => (Θ.pos w hw).2)
  refine ⟨Ha.T + 1, Real.sqrt (‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ Uw.g * C))⁻¹), ?_⟩
  intro w hw yw hA k x t hx hb
  have hw' : Ha.T < w.im := by linarith
  obtain ⟨hLie, hGen⟩ := hA
  have V1 := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W Uw.g _ Uw.F Ha th Θ w yw hw' hLie.1 hGen
  have V2 := Uw.norm k x hx
  obtain ⟨G, -, -, hchg⟩ := (GlobalTheory.Frames.frBor_iff_frChg _ _ _).1 hb
  have hs := (GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 E H Dw l Xo c
    σ Uw.g _ Uw.F (Uw.ik k) Ha.i (Uw.Pm k x) (Ha.Pw w) (U.un k x) yw G (t none : CAt σ) 1 _ (Uw.period k x)
    (Ha.period w hw') (Uw.lie k x).1 hLie.1 hchg V2 V1).2
  rw [mul_one] at hs
  apply Real.le_sqrt_of_sq_le
  rw [← hs]
  have hd := hdet w hw
  have h2 : (0 : ℝ) < 2 ^ Uw.g := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (Real.sqrt_pos.2 (mul_pos h2 hC)) (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hd h2.le))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AttOfFrobMatch
section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)

theorem exists_aut {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    (φ ψ : O →+* Qbar l) (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hφ' : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (hψ' : ∀ z : ℤ_[l], ψ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ γ : Qbar l ≃+* Qbar l, ∀ x, γ (φ x) = ψ x := by
  have halg : Algebra.IsAlgebraic ℤ_[l] (Qbar l) :=
    haveI := IsLocalization.isAlgebraic (R := ℤ_[l]) ℚ_[l] (nonZeroDivisors ℤ_[l])
    Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (Qbar l)
  have key : ∀ (f : O →+* Qbar l) (hf : Function.Injective f),
      (∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) →
      letI := f.toAlgebra
      haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
      IsAlgClosure O (Qbar l) := fun f hf hf' => by
    letI := f.toAlgebra
    haveI : Module.IsTorsionFree O (Qbar l) := Module.isTorsionFree_iff_algebraMap_injective.2 hf
    haveI : IsScalarTower ℤ_[l] O (Qbar l) := IsScalarTower.of_algebraMap_eq fun z => (hf' z).symm
    have hi : Function.Injective (algebraMap ℤ_[l] O) := fun x y h => by
      have := (hf' x).symm.trans ((congrArg f h).trans (hf' y))
      exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective this)
    exact ⟨inferInstance, Algebra.IsAlgebraic.extendScalars hi⟩
  let e := @IsAlgClosure.equiv O _ _ (Qbar l) (Qbar l) _ _ ψ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ ψ.toAlgebra _ _ |>.2 hψ) (key ψ hψ hψ') φ.toAlgebra
    (@Module.isTorsionFree_iff_algebraMap_injective _ _ _ _ φ.toAlgebra _ _ |>.2 hφ) (key φ hφ hφ')
  exact ⟨@AlgEquiv.toRingEquiv O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e,
    fun x => @AlgEquiv.commutes O _ _ _ _ _ φ.toAlgebra ψ.toAlgebra e x⟩

variable {D : D7} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}

def brEmb (i : D.ntw.Tw) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) : D.ntw.O0 i →+* Qbar (D.ntw.l i) :=
  (algebraMap ↥(D.ntwbr i v hv).LL.1 (Om (D.ntw.l i))).comp (D.ntwbr i v hv).toLL

theorem isModel_brEmb (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) :
    IsModel (D.ntwbr i v hv) (resDec D.nd.plOm.1 (mapRep (brEmb i v hv) ρ) v) (D.ntwbr i v hv).LL
      (mapRep (D.ntwbr i v hv).toLL (ρ.comp (DecV D.nd v).subtype)) :=
  ⟨le_rfl, by ext g a b; rfl⟩

end GlobalTheory.TripleLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocalisationBoundAtPoint

theorem boundAtPoint_all_localisations_of_objectConditions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  intro hGAR hBK hLTD hLEC D h51 i r ρ π dc lenRow e' cB hR hA hl0 hl1
  have a51 := h51 i hl0 hl1 r ρ π dc lenRow e' cB hR hA
  obtain ⟨G1, G2, G3, G4, G5, G5x, G6, BK, TB, ROW, LIFT, Cont, SS, Decomp, Eps, Comparison₂, Shape, Font, H2, CFT⟩ := hA
  have TB78 : EmbeddingTypes.admTB i r π dc cB := fun w hw _ C hC => TB w hw C hC
  exact _root_.GlobalTheory.SelmerBoundAtPoint.main hGAR hLTD hLEC D i r ρ π dc lenRow e' cB G1 G2 G3 G4 G5 G5x G6 BK
    (_root_.GlobalTheory.BKaRows.bkaAll_of_hypotheses hBK hLTD hLEC D i) Cont Decomp Font (_root_.GlobalTheory.finAll_of_localTateDuality hLTD D i) Comparison₂ a51
    (GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc) ROW LIFT TB78 hl0 hl1

end GlobalTheory.LocalisationBoundAtPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspReadTOfCuspRead
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (k := w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

end GlobalTheory.RecT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory

theorem deRham_potentiallySemistable : GlobalTheory.Published.DeRhamPotSemistable :=
  _root_.GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm _root_.GlobalTheory.PMon.matThm_holds

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmallStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  first | (exact @GlobalTheory.SchurNear.blocks_small) | (exact GlobalTheory.SchurNear.blocks_small) | (intros; apply GlobalTheory.SchurNear.blocks_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryRationalMatrixOfFirstPresentationPo
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix

namespace GlobalTheory.RatPtsBridge

theorem exists_ratGL : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  intro L _ _ _ n γQ
  obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γQ.2)
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := hγ₀
  have h1 : conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) *
      (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := mul_eq_one_comm.1 h0
  have hmem : ratGL L n γ₀ ∈ UA L n := by
    show Formalism.UG.cT (conjAd L) ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
      ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1
    have e : Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) =
        (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map (algebraMap L (Ad L)) := by
      ext i j
      simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) * 1 *
      (γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) = 1
    rw [mul_one, e, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨ratGL L n γ₀, hmem⟩, γ₀, rfl, ?_⟩
  rw [← he]
  rfl

end GlobalTheory.RatPtsBridge
end
end

