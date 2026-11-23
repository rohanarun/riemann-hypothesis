module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.MeanHeightDescent.AverageDegreeBounds.GlobalBoundRefinements
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReproducingIdentityExtendsHarishChandraSpan
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HCF.ReproSpan

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem chart_zero' (g : GA E a) (x : Lie E a) : chart (0 : GA E a → ℂ) g x = 0 := by
  unfold chart; split_ifs <;> rfl

theorem chart_add' (φ ψ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (φ + ψ) g x = chart φ g x + chart ψ g x := by
  unfold chart; split_ifs <;> simp

theorem chart_smul' (c : ℂ) (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) :
    chart (c • φ) g x = c * chart φ g x := by
  unfold chart; split_ifs <;> simp

theorem integrable_chart_mul (ψ : Sm E a) (g : GA E a) (β : Lie E a → ℂ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ invSet E a) :
    MeasureTheory.Integrable (fun x => chart ψ.1 g x * β x) := by
  have hcont : Continuous (fun x => chart ψ.1 g x * β x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ invSet E a
    · exact (contDiffAt_chart ψ.2 g hx).continuousAt.mul hβ.continuousAt
    · have hxt : x ∉ tsupport β := fun h => hx (hs h)
      have hev : (fun x => chart ψ.1 g x * β x) =ᶠ[𝓝 x] fun _ => 0 := by
        have h0 : β =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxt
        filter_upwards [h0] with y hy
        simp [hy]
      exact (continuousAt_congr hev).mpr continuousAt_const
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : SigmaFinite (volume : Measure (Fin a → Cinf E)) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (volume : Measure (Lie E a)) :=
    MeasureTheory.Measure.pi.isFiniteMeasureOnCompacts _
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_left hc)

end GlobalTheory.HCF.ReproSpan


open GlobalTheory.HCF.ReproSpan in
theorem GlobalTheory.HCF.repro_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ) (β : Lie E a → ℂ),
    ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ invSet E a →
    (∀ φ ∈ formsGL E a L W X N, ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g) →
    ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N), ∀ g : GA E a, ∫ x, chart φ.1 g x * β x = φ.1 g := by
  intro E _ _ _ a L W X N β hβ hc hs hform φ hφ
  have hβc : Continuous β := hβ.continuous
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hform x hx
  | zero =>
    intro g
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
    simp [chart_zero']
  | add x y _ _ hx hy =>
    intro g
    have e : (fun z => chart (x + y).1 g z * β z) =
        fun z => chart x.1 g z * β z + chart y.1 g z * β z := by
      funext z
      rw [Submodule.coe_add, chart_add', add_mul]
    rw [e, MeasureTheory.integral_add (integrable_chart_mul x g β hβc hc hs)
      (integrable_chart_mul y g β hβc hc hs), hx g, hy g]
    rfl
  | smul c x _ hx =>
    intro g
    have e : (fun z => chart (c • x).1 g z * β z) = fun z => c * (chart x.1 g z * β z) := by
      funext z
      rw [Submodule.coe_smul, chart_smul', mul_assoc]
    rw [e, MeasureTheory.integral_const_mul, hx g]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem embedsBy_fA_of_isBCBasis (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ)
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (hB : IsAbelianScheme B) (hM : M.IsLB) (_hk : 1 ≤ k)
    (hVA : VeryAmpleAt B M k) (hb : IsBCBasis B M k bB) : GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  have hp : IsProper B.hom := hB.proper
  let t : Spec (CommRingCat.of Rg) ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  choose b' hb' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec B M (k : ℤ) (homAt t) (bB i)
  have hspan := (hb Rg t b' hb').2
  have hE := GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) t b' hspan
  have hS := fun i => GlobalTheory.SpanFrame.secScal_of_isPullSec B hM (k : ℤ) (homAt t) (hb' i)
  haveI : IsIso (homAt t) := by
    haveI : IsIso ((Over.forget _).map (homAt t)) := by change IsIso t; infer_instance
    exact isIso_of_reflects_iso (homAt t) (Over.forget _)
  haveI : IsIso (homAt t ▷ B).left := inferInstanceAs (IsIso ((Over.forget _).map (homAt t ▷ B)))
  haveI : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Rg)))
  have hw : (homAt t ▷ B).left ≫ fA B = (fst (baseAt t) B).left ≫ 𝟙 _ := by
    have e1 := Over.w (homAt t ▷ B)
    have e2 := Over.w (fst (baseAt t) B)
    have e3 : (baseAt t).hom = 𝟙 _ := by simp [baseAt, t, baseOver]
    rw [Category.comp_id, fA, e1, ← e2, e3, Category.comp_id]
  have sq : IsPullback (inv (homAt t ▷ B).left) (fA B) (fst (baseAt t) B).left (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, hw, Category.comp_id]
  exact GlobalTheory.AmpleSpan.EmbedsBy.secScal hM sq hE
    fun i => GlobalTheory.AmpleSpan.secScal_symm hM (hS i) (IsIso.inv_hom_id _)

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadLeAt
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem spread_le_at {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) (τ : ι)
    (j : ℕ) (hj : j ≤ N - W.kc) :
    (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ 6 * ∑ i, |(W.u' τ i : ℝ)| := by
  classical
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.MeanTop.nodes_far_and_spread ι N W hW hD τ
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hW.p_lt
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨a, ha⟩ := exists_eq_ciSup_of_finite (f := reWt W.u' τ)
  obtain ⟨b, hb⟩ := exists_eq_ciInf_of_finite (f := reWt W.u' τ)
  have hsp : (⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i ≤ 3 / 2 * W.w τ / W.T := by
    rw [← ha, ← hb]; exact h2 a b
  have h0 : 0 ≤ 3 / 2 * W.w τ / W.T := by simpa using h2 a a
  have hkN : W.kc < N := hW.kc_lt.trans hW.p_lt
  set s : Finset (Fin N) := Finset.Ici (⟨W.kc, hkN⟩ : Fin N) with hs
  have hcard : s.card = N - W.kc := by simp [hs]
  have hsum : (s.card : ℝ) * (W.w τ / (4 * W.T)) ≤ ∑ i ∈ s, |(W.u' τ i : ℝ)| := by
    have := Finset.card_nsmul_le_sum s (fun i => |(W.u' τ i : ℝ)|) (W.w τ / (4 * W.T))
      (fun i hi => (h1 i (by simpa [hs, Fin.le_def] using hi)).2)
    simpa [nsmul_eq_mul] using this
  have hsub : ∑ i ∈ s, |(W.u' τ i : ℝ)| ≤ ∑ i, |(W.u' τ i : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  have hjc : (j : ℝ) ≤ s.card := by rw [hcard]; exact_mod_cast hj
  have he : 3 / 2 * W.w τ / W.T = 6 * (W.w τ / (4 * W.T)) := by ring
  calc (j : ℝ) * ((⨆ i, reWt W.u' τ i) - ⨅ i, reWt W.u' τ i) ≤ j * (3 / 2 * W.w τ / W.T) :=
        mul_le_mul_of_nonneg_left hsp (Nat.cast_nonneg _)
    _ ≤ s.card * (3 / 2 * W.w τ / W.T) := mul_le_mul_of_nonneg_right hjc h0
    _ = 6 * (s.card * (W.w τ / (4 * W.T))) := by rw [he]; ring
    _ ≤ _ := by linarith

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqNormClassSumMatrixLeCauchySchwarz
section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mat_opOf_apply {F F' : GFam K} (M : GFam.Mat F F') (hF : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (b' : F'.β)
    (d' : F'.D b') :
    ((M.opOf hF s φ b' : (F'.mem b').EqFun) : F'.D b' → F'.V) d' =
      ∑ b, (M b b').appOf (hF b) (s b) (φ b : (F.mem b).D → F.V) d' := by
  simp only [GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem step_le (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : 0 ≤ h') (hp : ∀ b, PosAt ((Q.F i).mem b) v) (hp' : ∀ b, PosAt ((Q.F (i + 1)).mem b) v)
    (hc : ∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) (hc' : ∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h')
    (hk : ∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) (φ : (Q.F i).Forms) :
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t *
        (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  have hN : (famIpAt (Q.F i) (Q.hF i) v φ φ).re =
      ∑ b, (((Q.F i).mem b).ipAt (Q.hF i b) v (φ b : ((Q.F i).mem b).D → (Q.F i).V) (φ b : ((Q.F i).mem b).D → (Q.F i).V)).re := by
    unfold famIpAt
    rw [Complex.re_sum]
  have hN0 : 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
    rw [hN]
    exact Finset.sum_nonneg fun b _ => ipAt_self_nonneg _ v _ (hp b) _
  have hB : ∀ b' d', (((Q.F (i + 1)).mem b').pairAt v ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')
      ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by
    intro b' d'
    have e := mat_opOf_apply (Q.kk i) (Q.hF i) (fun b => ((Q.F i).mem b).outSec) φ b' d'
    change ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d') = _ at e
    rw [e]
    refine (pairAt_sum_le ((Q.F (i + 1)).mem b') v (hp' b') _ _).trans ?_
    rw [Finset.card_univ, hN, Finset.mul_sum _ _ t, Finset.mul_sum _ _ h]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
    refine (appOf_le v (Q.kk i b b') (Q.hF i b) (hp b) (hp' b') t ht _ d' fun d => hk b b' d d').trans ?_
    exact mul_le_mul_of_nonneg_right (hc b) (mul_nonneg ht (ipAt_self_nonneg _ v _ (hp b) _))
  have hB0 : 0 ≤ (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by positivity
  calc (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re
      ≤ ∑ _b' : (Q.F (i + 1)).β, h' * ((Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re))) := by
        rw [famIpAt, Complex.re_sum]
        refine Finset.sum_le_sum fun b' _ => ?_
        exact (ipAt_self_le _ v _ (hp' b') _ _ (hB b')).trans (mul_le_mul_of_nonneg_right (hc' b') hB0)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.ColNorms.SumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPullbackEllipticModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowFibre

section Pow

variable {S : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G₀ G j)

theorem over_ext {T : Over S} {a b : T ⟶ G₀} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem left_ext {T : Scheme.{0}} {a b : T ⟶ G₀.left} (h₀ : a ≫ G₀.hom = b ≫ G₀.hom)
    (h : ∀ i, a ≫ (p.pr i).left = b ≫ (p.pr i).left) : a = b := by
  have := over_ext p (T := Over.mk (b ≫ G₀.hom)) (a := Over.homMk a h₀) (b := Over.homMk b rfl)
    fun i => Over.OverMorphism.ext (h i)
  exact congrArg (·.left) this

theorem exists_left_lift {T : Scheme.{0}} (s : T ⟶ S) (a : Fin j → (T ⟶ G.left)) (ha : ∀ i, a i ≫ G.hom = s) :
    ∃ x : T ⟶ G₀.left, x ≫ G₀.hom = s ∧ ∀ i, x ≫ (p.pr i).left = a i := by
  let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk s) fun i => Over.homMk (a i) (ha i)
  exact ⟨(p.lim.lift c).left, Over.w (p.lim.lift c), fun i => congrArg (·.left) (p.lim.fac c ⟨i⟩)⟩

end Pow

section Pull

variable {S S' : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {G₀' G' : Over S'} [GrpObj G₀'] [GrpObj G']
  {j : ℕ} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_pow_pullback (p : Out.IsPowGrp G₀ G j) (p' : Out.IsPowGrp G₀' G' j) (h : IsGrpPullback G' G f φ) :
    ∃ φ₀ : G₀'.left ⟶ G₀.left, IsGrpPullback G₀' G₀ f φ₀ ∧ ∀ i, φ₀ ≫ (p.pr i).left = (p'.pr i).left ≫ φ := by
  obtain ⟨φ₀, hw, hφ₀⟩ := exists_left_lift p (G₀'.hom ≫ f) (fun i => (p'.pr i).left ≫ φ) fun i => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
  refine ⟨φ₀, ⟨⟨⟨hw⟩, ⟨?_⟩⟩, fun T x y x₀ y₀ hx hy => ?_⟩, hφ₀⟩
  · have hs : ∀ (s : PullbackCone G₀.hom f) (i : Fin j), (s.fst ≫ (p.pr i).left) ≫ G.hom = s.snd ≫ f :=
      fun s i => by rw [Category.assoc, Over.w, s.condition]
    choose l hl₁ hl₂ using fun s : PullbackCone G₀.hom f =>
      exists_left_lift p' s.snd (fun i => h.1.lift _ _ (hs s i)) fun i => h.1.lift_snd _ _ _
    refine PullbackCone.IsLimit.mk _ l (fun s => left_ext p ?_ fun i => ?_) hl₁
      fun s m h₁ h₂ => left_ext p' (h₂.trans (hl₁ s).symm) fun i => ?_
    · rw [Category.assoc, hw, ← Category.assoc, hl₁, s.condition]
    · rw [Category.assoc, hφ₀, ← Category.assoc, hl₂, h.1.lift_fst]
    · rw [hl₂]
      refine h.1.hom_ext ?_ ?_
      · rw [h.1.lift_fst, Category.assoc, ← hφ₀, ← Category.assoc, h₁]
      · rw [h.1.lift_snd, Category.assoc, Over.w, h₂]
  · refine left_ext p ?_ fun i => ?_
    · rw [Over.w, Category.assoc, hw, ← Category.assoc, Over.w]
      rfl
    · have := p.hom i
      have := p'.hom i
      have e := h.2 T (x ≫ p'.pr i) (y ≫ p'.pr i) (x₀ ≫ p.pr i) (y₀ ≫ p.pr i)
        (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hφ₀])
        (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hφ₀])
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, Over.comp_left, Over.comp_left] at e
      rw [e, Category.assoc, Category.assoc, hφ₀]

end Pull



end GlobalTheory.PowFibre

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPeriodEqPeriodOverThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GaussManinTaylor

theorem prod_zero_of_pow_eq_bot {R : Type} [CommRing R] (J : Ideal R) (n₀ : ℕ) (h : J ^ n₀ = ⊥) (N' : ℕ)
    (hN : n₀ ≤ N' + 1) (s : Fin (N' + 1) → R) (hs : ∀ a, s a ∈ J) : ∏ a, s a = 0 := by
  have h1 : ∏ a, s a ∈ ∏ _a ∈ (Finset.univ : Finset (Fin (N' + 1))), J := Ideal.prod_mem_prod (fun a _ ↦ hs a)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Ideal.pow_le_pow_right hN h1
  rw [h] at h2
  simpa using h2

end GlobalTheory.GaussManinTaylor

open GlobalTheory.GaussManinTaylor in
theorem GlobalTheory.GaussManinTaylor.taylor_period_eq_period_over_thickening : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B D : Type} [CommRing B] [CommRing D] [Algebra ℂ D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (u₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → 0 ∈ F.V → (∀ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, u₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (π : D →ₐ[ℂ] ℂ), IsNilpotent (RingHom.ker π) → ∀ {J : Ideal D} (dl : DividedPowers J), (∀ d ∈ J, π d = 0) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap (π : D →+* ℂ) → ∀ (n : IsMor (dp0 B) s dl s' j φ₀) (ψ : X₀ ⟶ X₀) (k : IsMor (dp0 ℂ) s₀ dl s' (algebraMap ℂ D) ψ), ψ = 𝟙 X₀ → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ {io : Type} (S : Finset io) (d : io → D) (a : io → FirstDeRham s₀) (p : io → Λ → ℂ) (p' : io → (Λ →+ Hol F₀.V)), (∀ i l, p' i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod u₀ (a i) (p' i)) → n.pull1 c = ∑ i ∈ S, d i • k.pull1 (a i) → ∀ l, ∑ i ∈ S, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B D _ _ _ X X₀ s s₀ σ e u₀ hX hX₀ h0V hV₀ hτ φ₀ hφ₀ π hπ J dl hJ N t ht hprod j hj s' hs' n ψ kk hψ c per hper ιo S d a p p' hp' hpa hsum l

  obtain ⟨R, _, _, io, π', m, hinj, hπ', hnil, hm0, hmm, hmsum⟩ :=
    GlobalTheory.SquareZeroSum.exists_sum_sq_zero N D π t hπ ht hprod
  set t' : I → R := fun i ↦ ∑ j, m j i with ht'def
  have ht' : (fun i ↦ io (t i)) = t' := funext hmsum
  have hprod' : ∀ s : Fin (N + 1) → I, ∏ a, t' (s a) = 0 := by
    intro s
    rw [← ht']
    simp only
    rw [← map_prod, hprod, map_zero]
  obtain ⟨n₀, hn₀⟩ := hnil
  set N' := N + n₀ with hN'
  have hker : ∀ s : Fin (N' + 1) → R, (∀ a, s a ∈ RingHom.ker (π' : R →+* ℂ)) → ∏ a, s a = 0 :=
    fun s hs ↦ prod_zero_of_pow_eq_bot _ n₀ hn₀ N' (by omega) s hs
  have ht'ker : ∀ i, t' i ∈ RingHom.ker (π' : R →+* ℂ) := fun i ↦ by
    have h1 : io (t i) = t' i := congrFun ht' i
    rw [RingHom.mem_ker, ← h1]
    change π' (io (t i)) = 0
    rw [hπ', ht]
  have hprodN' : ∀ s : Fin (N' + 1) → I, ∏ a, t' (s a) = 0 := fun s ↦ hker _ fun a ↦ ht'ker (s a)

  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.AnPer.exists_taylor_algHom N' t' hprodN' F.V h0V
  have hθio : ∀ f : Hol F.V, θ f = io (GlobalTheory.PeriodFamily.taylor N t f.fn) := by
    intro f
    rw [hθ, GlobalTheory.PeriodFamily.taylor_eq_of_le N t' hprod' N' (by omega),
      (GlobalTheory.PeriodFamily.taylor_formal_properties N t).2.2.2.2.1 R io f.fn, ht']

  have hdef : (default : Empty → ℂ) ∈ F₀.V := hV₀ _
  obtain ⟨K₀, K, ka, hRich, hU₀, hU, hmemk, hka⟩ := GlobalTheory.T.exists_small_chart_pair_along_linear_map u₀ e (fun _ ↦ (0 : I → ℂ))
    (fun _ _ ↦ analyticAt_const) (fun _ _ ↦ h0V) (LinearMap.id) (AddMonoidHom.id Λ)
    (fun l z _ ↦ (hτ l z).symm)
  have hmem0 : ∀ k, ∀ q ∈ K₀.W k, (((0 : I → ℂ), q.2) : Tot I g) ∈ K.W (ka k) := fun k q hq ↦ hmemk k q hq
  have hka' : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k) := fun h ↦ hka _ _ _ h
  obtain ⟨r₀, hr₀, -⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor u₀ hX₀ K₀ hU₀
  obtain ⟨r, hr, -⟩ := _root_.GlobalTheory.AnPer.exists_real_isFor e hX K hU
  have han : AnalyticOnNhd ℂ (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) ⊤ :=
    fun _ _ ↦ analyticAt_const.prod analyticAt_snd
  let res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k) := fun k ↦
    (Hol.comap (fun q : Tot Empty g ↦ (((0 : I → ℂ), q.2) : Tot I g)) (fun q _ ↦ han q trivial) (hmem0 k)).toRingHom
  have hres : ∀ k (h : Hol (K.W (ka k))) {q : Tot Empty g}, q ∈ K₀.W k → (res k h).fn q = h.fn ((0 : I → ℂ), q.2) :=
    fun k h q hq ↦ Hol.fn_comap _ _ _ h hq

  choose ρ hρ using fun k ↦ _root_.GlobalTheory.AnPer.exists_sliceZero_isTay N' t' hprodN' (K.W (ka k)) (K₀.W k) (hmem0 k)
  let M : Ideal R := RingHom.ker (π' : R →+* ℂ)
  let et : Hol F₀.V →ₐ[ℂ] R := (Algebra.ofId ℂ R).comp (Hol.ev default hdef)
  have hcst : ∀ k f, ρ k (K.cst (ka k) f) = θ.toRingHom f ⊗ₜ[ℂ] 1 := fun k f ↦ by
    rw [_root_.GlobalTheory.AnPer.isTay_apply_of_fn_eq_param N' t' _ _ (hmem0 k) (ρ k) (hρ k) _ f.fn (fun q hq ↦ Charts.fn_cst _ _ _ hq)]
    exact congrArg (· ⊗ₜ[ℂ] (1 : Hol (K₀.W k))) (hθ f).symm
  have hdw : ∀ k (a : Fin g) (h : Hol (K.W (ka k))), ρ k (dw a h) = LinearMap.lTensor R (dw (W := K₀.W k) a).toLinearMap (ρ k h) := fun k a h ↦
    GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation N' t' _ _ (hmem0 k) (ρ k) (hρ k) a h
  have hclose : ∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka' h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k)) := by
    intro l k' k h
    have hρk := hρ k
    have hρk' := hρ k'
    rw [ht'def] at hρk hρk'
    exact _root_.GlobalTheory.AnPer.close_taylor_shift K K₀ M N' hker N m (fun j i ↦ hm0 j i) hmm hτ l (ka k) (ka k') k k' (hka' h) h (hmem0 k') (ρ k) (ρ k') hρk hρk'
  have hred : ∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k)) :=
    fun k h ↦ _root_.GlobalTheory.AnPer.taylor_reduces_to_slice N' t' π' (fun i ↦ ht'ker i) _ _ (hmem0 k) (ρ k) (hρ k) h (res k h) (fun q hq ↦ hres k h hq)
  obtain ⟨ρ', hρ'1, hρ'2, hρ'3⟩ := GlobalTheory.T.exists_points_translationFamilyCharts_thickenings K K₀ et M θ.toRingHom ka hka' ρ hcst hdw hclose res hred
  have hetc : ∀ x : ℂ, et (algebraMap ℂ (Hol F₀.V) x) = algebraMap ℂ R x := fun x ↦ et.commutes x
  have H : IsOver (et : Hol F₀.V →+* R) M s₀ (algebraMap ℂ (Hol F₀.V)) J s' (π : D →+* ℂ) (io : D →+* R) :=
    { w := hs'
      mem := fun d hd ↦ by
        rw [RingHom.mem_ker]
        change π' (io d) = 0
        rw [hπ', hJ d hd]
      red := fun d ↦ by
        rw [RingHom.mem_ker, map_sub]
        change π' (io d) - π' (et (algebraMap ℂ (Hol F₀.V) (π d))) = 0
        rw [hetc, AlgHom.commutes, hπ']
        simp }
  have hpt : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀ := fun k ↦ by
    refine _root_.GlobalTheory.AnPer.point_hol_ext_of_isSeparated (K₀.W k) hX _ _ (fun q hq ↦ ?_)
    have hq' := hmem0 k q hq
    have hev : (Hol.ev q hq).toRingHom.comp (res k) = (Hol.ev (((0 : I → ℂ), q.2) : Tot I g) hq').toRingHom :=
      RingHom.ext fun h ↦ by
        change Hol.ev q hq (res k h) = Hol.ev _ hq' h
        rw [Hol.ev_apply, Hol.ev_apply, hres k h hq]
    rw [← Category.assoc, ← GlobalTheory.Cris.spMap_comp, hev, hr (ka k) _ hq', ← Category.assoc, hr₀ k q hq, hφ₀ q]
  have hθj : ∀ b, θ.toRingHom (σ b) = io (j b) := fun b ↦ by
    rw [hj]
    exact hθio (σ b)
  have hfam := _root_.GlobalTheory.AnPer.period_restrict_family K K₀ (et : Hol F₀.V →+* R) M θ.toRingHom ka hka' res ρ' hρ'1 hρ'2 hρ'3 r r₀ dl H j φ₀ n hθj hpt c per (hper K r hr)
  have hfib : ∀ i, (r₀.coefD dl H).pull1 (kk.pull1 (a i)) = K₀.perClD (et : Hol F₀.V →+* R) M ((et : Hol F₀.V →+* R).toAddMonoidHom.comp (p' i)) :=
    fun i ↦ _root_.GlobalTheory.AnPer.period_const_ext K₀ (et : Hol F₀.V →+* R) M r₀ dl H (algebraMap ℂ D) ψ kk hψ
      (fun b ↦ by
        change et (algebraMap ℂ (Hol F₀.V) b) = io (algebraMap ℂ D b)
        rw [hetc, AlgHom.commutes]) (a i) (p' i) (hpa i K₀ r₀ hr₀)
  have hmain := congrArg (r₀.coefD dl H).pull1 hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hfam, map_sum] at hmain
  simp only [map_smulₛₗ, hfib] at hmain
  have het : ∀ (f : Hol F₀.V), ∀ z ∈ F₀.V, (et : Hol F₀.V →+* R) f = algebraMap ℂ R (f.fn z) := fun f z hz ↦ by
    have : z = default := Subsingleton.elim _ _
    subst this
    change algebraMap ℂ R (Hol.ev default hdef f) = _
    rw [Hol.ev_apply]
  have hdu := _root_.GlobalTheory.AnPer.perClD_relation_unique K₀ (et : Hol F₀.V →+* R) M hRich hV₀ ⟨n₀, hn₀⟩ het S _ _ _ hmain l
  apply hinj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← hθio]
  refine Eq.trans ?_ hdu.symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change io (d i * algebraMap ℂ D (p i l)) = io (d i) * et (p' i l)
  rw [map_mul, AlgHom.commutes, hp', hetc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassCoeffsIntegralAverageChangeOfVariableStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι] (X Y : ι → ℂ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → V.valuation (Fintype.card ι : ℂ) = 1 → (∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V) → (∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V) → (∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) → IntV V ((⟨u, (∑ i, X i) / Fintype.card ι, (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι, (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  first | exact @GlobalTheory.CMModel.intV_average | exact GlobalTheory.CMModel.intV_average | (intros; apply GlobalTheory.CMModel.intV_average <;> assumption)
end

