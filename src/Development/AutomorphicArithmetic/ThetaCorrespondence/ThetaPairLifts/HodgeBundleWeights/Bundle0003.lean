module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0002
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ConstDeformationObjMapEq
section
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ConstDeform
theorem constDeformation_objMap_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]
  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := _root_.GlobalTheory.TorsConst.torsion_eq_const K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := _root_.GlobalTheory.T.const_deformation_action_trivial hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := _root_.GlobalTheory.T.cubical_structure_const_section_pullback hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩
end GlobalTheory.ConstDeform
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_deformation_obj_eq : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  first | exact @_root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | exact _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq | (intros; apply _root_.GlobalTheory.ConstDeform.constDeformation_objMap_eq <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.ExactRatioProof
open scoped InnerProductSpace ComplexConjugate
theorem exact_covolume_ratio : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  intro hP D Tu C t0 hC i P μ 𝓕 hF T _ hT ha θ hθ σ M hV F hFm f hf hc
  have hμ : μ.IsHaarMeasure := hF.1.1
  have hS : ∃ c, IsMultIP M μ 𝓕 F F c :=
    GlobalTheory.MultFinite.schurMult _root_.GlobalTheory.RapidDecay.cuspRapidDecay μ 𝓕 hθ hμ hF.2 F hFm F hFm
  refine ⟨hS, ?_⟩
  obtain ⟨v, hv1, hnorm⟩ : ∃ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) ∧
      ∀ g, ‖F v g‖ = ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f g‖ := by
    rcases hc with ⟨-, v, hv, e⟩ | ⟨-, v, hv, e⟩
    · exact ⟨v, fun τ => (hv τ).1, fun g => by rw [e]⟩
    · exact ⟨v, hv, fun g => by rw [e, RCLike.norm_conj]⟩
  have hFM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hFm
  have haut := hFM.aut v
  have h1 := (ipM_spec M μ 𝓕 F F hS v v).2
  have hprod : ∏ τ, ⟪(v τ : M.H τ), (v τ : M.H τ)⟫_ℂ = 1 :=
    Finset.prod_eq_one fun τ _ => by rw [inner_self_eq_norm_sq_to_K, hv1 τ]; simp
  rw [hprod, mul_one] at h1
  have hs : GoodEmb T.Q.c (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ) := goodEmb_goodOf _ _
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  set ψ : AutQ (Wc D i) → ℂ := fun q => ((‖F v q.out‖ / c : ℝ) : ℂ) with hψdef
  have hK2 := K2 D T hT i _ hs hV f
  have hK3 := K3 D T hT i _ hs f hf
  have hψm : AEStronglyMeasurable ψ (muQ1 (Wc D i)) := by
    haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
    have hm : Measurable fun q : AutQ (Wc D i) => F v q.out := by
      rw [measurable_from_quotient]
      have e : ((fun q : AutQ (Wc D i) => F v q.out) ∘ Quotient.mk'') = F v := funext fun g => by
        have h2 : g * (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out⁻¹ ∈ GQ (Wc D i) :=
          QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
        have h3 := haut.left _ h2 (Quotient.mk (QuotientGroup.rightRel (GQ (Wc D i))) g).out
        rw [inv_mul_cancel_right] at h3
        exact h3.symm
      rw [e]
      exact haut.cont.measurable
    refine Measurable.aestronglyMeasurable ?_
    exact Complex.measurable_ofReal.comp ((hm.norm).div_const c)
  have hE : eLpNorm ψ 2 (muQ1 (Wc D i)) = petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
    have e1 : eLpNorm ψ 2 (muQ1 (Wc D i)) =
        eLpNorm (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) := by
      have heq : ∀ q : AutQ (Wc D i), ‖ψ q‖ =
          (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) q := by
        intro q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm,
          abs_of_pos hc0, hnorm]
        ring
      have hm : AEStronglyMeasurable (c⁻¹ • fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) (muQ1 (Wc D i)) :=
        hψm.norm.congr (Filter.Eventually.of_forall heq)
      refine eLpNorm_congr_norm_ae hψm hm (Filter.Eventually.of_forall fun q => ?_)
      rw [← heq q, Real.norm_eq_abs, abs_norm]
    have hadm : AEStronglyMeasurable (fun q : AutQ (Wc D i) =>
        ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖)
        (muQ1 (Wc D i)) := by
      have heq : (fun q : AutQ (Wc D i) =>
          ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) =
          c • (fun q => ‖ψ q‖) := by
        funext q
        simp only [hψdef, Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_div, abs_norm, abs_of_pos hc0, hnorm]
        field_simp
      rw [heq]
      exact hψm.norm.const_smul c
    rw [e1, eLpNorm_const_smul]
    conv_lhs =>
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hadm]
    have ht : (2 : ENNReal).toReal = 2 := by norm_num
    rw [ht, hK2]
    rw [← mul_assoc, Real.enorm_eq_ofReal (inv_nonneg.2 hc0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.2 hc0.le), inv_mul_cancel₀ hc0.ne', ENNReal.ofReal_one, one_mul]
  have hψ : MemLp ψ 2 (muQ1 (Wc D i)) := by rw [memLp_iff, hE]; exact lt_top_iff_ne_top.2 hK3
  have hI := GlobalTheory.ReadingNorm.integral_star_mul (Wc D i) (D.sp.W_sig _) hμ hF.2 (F v) haut.left ψ hψ c
    (fun q => by
      simp only [hψdef, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hc0]
      field_simp)
  have hL : ‖hψ.toLp ψ‖ = (petE (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ))
      (T.dict ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (muQ1 (T.V ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)))
      (modelWt (T.U ((i : ℕ) + 1) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.gd T σ)) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f).toReal := by
    rw [Lp.norm_toLp, hE]
  rw [Formalism.IndefR.Links.ipAt, ← h1, hI, L1 D i σ, hL]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.probSq
  push_cast
  ring
end GlobalTheory.ExactRatioProof
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_ratio_eq_index : ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ExactRatio C i P μ 𝓕 := by
  first | exact @_root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | exact _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio | (intros; apply _root_.GlobalTheory.ExactRatioProof.exact_covolume_ratio <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCmPointFrameNeZeroOfDominant
section
section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.AllWt (bergOn framesOn)
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace _root_.CategoryTheory.Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.CovDetectDom
theorem exists_cmPoint_frame_ne_zero_of_dominant : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  classical
  intro hP D T j Y e o hG hdeg _ _ la _ _ _ hstar F hF hF0
  have hσ : GoodEmb Y.d.c₂ Y.d.c₂.F.val.toRingHom := rfl
  have hU := hG.unf _ hσ
  have hFm := GlobalTheory.AllWt.mem_cuspW.1 hF
  obtain ⟨k, x₁, hx₁, hne₁⟩ := GlobalTheory.exists_rdU_ne_zero_of_mem_secZ _ _ _ _ _ _ _ _ _ hU _ F hFm.1 hF0
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.CovData.exists_dataX_good D T j Y e o hG _ hσ k
  have hbdd := (Formalism.L2.Pj.abelian₂.holSub_SS ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _ _ (hFm.2 _ hσ) k).1
  have hr : 0 < D.R.r := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    unfold Ranks.r; omega
  obtain ⟨La, x, lam, hx, hB, hne⟩ := GlobalTheory.CMDetect.exists_cm_frame Xx _ hX hr _ _ hbdd hx₁ hne₁
  obtain ⟨z, σ₁, hz, hzx⟩ := GlobalTheory.LamT.exists_good_cmPt_at_frame _ _ _ _ _ _ hstar _ _ hU hr k ⟨x, hx⟩ Xx hX 𝔄 h𝔄 hΛ
    La lam hB
  have hev : evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, hx⟩) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x ∈ ((Y.U _).X k).dom then toC (evR Y.d.Xo₂ Y.d.c₂ F ((Y.U _).un k ⟨x, h⟩)) else 0) = 0
    rw [dite_eq_left hx]
    exact h0
  obtain ⟨y, hy, hyne⟩ := GlobalTheory.FrameDenseZ.exists_frame_evR_ne_zero_of_complex _ _ _ _ _ _ z.K z.y _ F hFm.1 _ σ₁ _ hzx hev
  exact ⟨z, La, y, hz, hy.trans hz.2.2.2.1, hyne⟩
end GlobalTheory.CovDetectDom
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace _root_.CategoryTheory.Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmPoint_detects_dominant_covering : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 → ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K), z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  first | exact @_root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | exact _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant | (intros; apply _root_.GlobalTheory.CovDetectDom.exists_cmPoint_frame_ne_zero_of_dominant <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsUniformizingIntegralFrameExtension
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnifTrait
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end Frames
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
section Split
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
end Split
end GlobalTheory.UnifTrait
namespace GlobalTheory.UnifTrait
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem exists_extension_integral_frame_uniformizer : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  intro _ E _ _ _ H Dw l Xo c TF T io
  letI := io.toAlgebra
  intro P w hw
  have hz : FlagMod.frX P ≫ TF.Y.j = spMap (algebraMap T.V T.Fr) ≫ w := by
    rw [hw, (TF.X.lies_ptY P).1]
  have hzs : FlagMod.frX P ≫ pullback.snd _ _ = spMap io := FlagMod.frX_snd P
  obtain ⟨y₀, tt, hB⟩ := exists_intFr_frBor T io c.F (RingHom.id c.F) TF.Y w (FlagMod.frX P) hz hzs P
    (FlagMod.frX_fst P).symm
  obtain ⟨G₀, ⟨m₀⟩⟩ : ∃ G₀ : SAB H (Sp T.V), Nonempty (SABMap G₀ TF.Y.t w) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull w TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₀, m1₀, m2₀, -⟩ := genFibre Xo c Out.CubePf.cubePull T io c.F (RingHom.id c.F) TF.Y w _ hz hzs G₀ m₀
  have : CharZero (ResidueField T.V) := charZero_residue_of_map T.V (w ≫ TF.Y.s)
  obtain ⟨W, _, _, _, _, _, hf, hi, hS⟩ := exists_split_baseChange T.V G₀.G G₀.semi
  have : CharZero W := charZero_of_injective_ringHom hi
  let T' : CDVR := { V := W }
  let j : T.V →+* T'.V := algebraMap T.V W
  have hfin : j.Finite := RingHom.finite_algebraMap.2 hf
  obtain ⟨i, r, hr0, hφ, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' j hi hfin
  letI := (i.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z', hz'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
    T.Fr T'.Fr ψ y₀.1
  let y' : IntFr Xo c T' (i.comp io) := ⟨z', GlobalTheory.NonIntegralFrameExample.spread_holds Xo c T'.Fr z',
    GlobalTheory.IntegralExt.integral_baseChange T T' io (i.comp io) j hi ψ hφ y₀.1 z' hz' y₀.2.2⟩
  obtain ⟨G, ⟨mG⟩⟩ : ∃ G : SAB H (Sp T'.V), Nonempty (SABMap G TF.Y.t (spMap j ≫ w)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap j ≫ w) TF.Y.t
    exact ⟨_, ⟨m⟩⟩
  have hι : i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j := RingHom.ext hφ
  have hio : spMap (algebraMap T'.V T'.Fr) ≫ spMap j = spMap i ≫ spMap (algebraMap T.V T.Fr) := by
    rw [GlobalTheory.EtaVal.spMap_comp_spMap, GlobalTheory.EtaVal.spMap_comp_spMap, hι]
  have hz2 : (spMap i ≫ FlagMod.frX P) ≫ TF.Y.j = spMap (algebraMap T'.V T'.Fr) ≫ spMap j ≫ w := by
    rw [Category.assoc, hz, ← Category.assoc, ← hio, Category.assoc]
  have hzs2 : (spMap i ≫ FlagMod.frX P) ≫ pullback.snd _ _ = spMap (i.comp io) := by
    rw [Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap]
  obtain ⟨t', m1, m2, -⟩ := genFibre Xo c Out.CubePf.cubePull T' (i.comp io) c.F (RingHom.id c.F) TF.Y
    (spMap j ≫ w) _ hz2 hzs2 G mG
  have hx' : y'.1.x = (spMap i ≫ FlagMod.frX P) ≫ pullback.fst _ _ := by
    rw [Category.assoc, FlagMod.frX_fst, ← hB.1]
    exact hz'.1
  obtain ⟨Pu, -⟩ := GlobalTheory.IntegralExt.exists_unif_of_split T T' j i hφ m1₀ m2₀ (Category.assoc _ _ _) m1 m2 hS
  have hloc : IsLocalHom j := hfin.to_isIntegral.isLocalHom hi
  refine ⟨T', i, j, r, y', G, mG, Pu, t', (by rw [hx']; exact m1), m2, hr0, hv, hι, fun a ha => map_nonunit j a ha,
    ?_⟩
  rw [TF.X.ptY_frBor hB, ← TF.X.ptY_frMap hz']
end GlobalTheory.UnifTrait
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizing_integral_frame_extension : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (P : FrPt Xo c T.Fr) (w : Sp T.V ⟶ TF.Y.X), spMap (algebraMap T.V T.Fr) ≫ w = TF.X.ptY P ≫ TF.X.π → ∃ (T' : Formalism.L2.Pj.CDVR) (i : T.Fr →+* T'.Fr) (j : T.V →+* T'.V) (r : ℕ) (y' : IntFr Xo c T' (i.comp io)) (G : SAB H (Sp T'.V)) (_ : SABMap G TF.Y.t (spMap j ≫ w)) (_ : PELUnif (IsLocalRing.maximalIdeal T'.V) G) (t' : SAB H (Sp T'.Fr)) (_ : letI := (i.comp io).toAlgebra; SABMap t' Xo.univ.t y'.1.x) (_ : SABMap t' G (spMap (algebraMap T'.V T'.Fr))), 0 < r ∧ (∀ x, Formalism.L2.Pj.vV T'.V (i x) = (r : ℤ) * Formalism.L2.Pj.vV T.V x) ∧ i.comp (algebraMap T.V T.Fr) = (algebraMap T'.V T'.Fr).comp j ∧ (∀ a ∈ IsLocalRing.maximalIdeal T.V, j a ∈ IsLocalRing.maximalIdeal T'.V) ∧ (letI := (i.comp io).toAlgebra; TF.X.ptY y'.1 = spMap i ≫ TF.X.ptY P) := by
  first | exact @_root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | exact _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer | (intros; apply _root_.GlobalTheory.UnifTrait.exists_extension_integral_frame_uniformizer <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerPairingSymmetric
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers TensorProduct TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CrysConn
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSSym
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X ⟶ Sp (DualNumber R)}
open GlobalTheory.Published
end GlobalTheory.KSSym
namespace GlobalTheory.KSSym
open NumberField Formalism.L2.Pj MonObj
theorem kodairaSpencer_map_symm : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X)
    (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)),
    IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
    GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ →
    ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' →
      ψ f k' + ψ k g = 0 := by
  rintro Pr E _ _ _ H Dw l Xo K _ x x' A _ A' _ π π' i h ψ hπ hπ' rfl hψ f g k k' ⟨d, hd, ed⟩ ⟨d', hd', ed'⟩
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨ψ', hψ', iso, -⟩ := GlobalTheory.PolExistsRing.polForm_exists Pr.p5 Xo hπ'
  rw [← snd_polForm Pr.p5 hA gA h Xo.univ.t.PP.isLB hψ hψ' ed ed', iso _ hd _ hd']
  rfl
end GlobalTheory.KSSym
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)), IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' → ψ f k' + ψ k g = 0 := by
  first | exact @_root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | exact _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | (intros; apply _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm <;> assumption)
end
end

