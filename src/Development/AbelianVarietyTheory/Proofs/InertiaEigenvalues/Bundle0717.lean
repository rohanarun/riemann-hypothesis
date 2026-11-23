module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0707
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormUnderEqOfInertiaDegOne
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.NormDegOne

theorem normV_under_eq : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (w : HeightOneSpectrum (𝓞 L)), w.asIdeal.inertiaDeg ℤ = 1 → normV (w.under (𝓞 K)) = normV w := by
  intro K L _ _ _ _ _ w h
  classical
  set P := w.asIdeal with hP
  set Q := (w.under (𝓞 K)).asIdeal with hQ
  have hQP : Q = P.under (𝓞 K) := rfl
  have : P.IsPrime := w.isPrime
  have : Q.IsPrime := (w.under (𝓞 K)).isPrime
  have hlo : P.LiesOver Q := ⟨hQP⟩
  have htow := Ideal.inertiaDeg_tower (R := ℤ) Q P
  rw [h] at htow
  have hQ1 : Q.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_right htow.symm
  have hunder : Q.under ℤ = P.under ℤ := by rw [hQP, Ideal.under_under]
  have e1 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) P
  have : Q.LiesOver (P.under ℤ) := ⟨hunder.symm⟩
  have e2 := Ideal.absNorm_pow_inertiaDeg (P.under ℤ) Q
  rw [h, pow_one] at e1
  rw [hQ1, pow_one] at e2
  change Nat.card (𝓞 K ⧸ Q) = Nat.card (𝓞 L ⧸ P)
  rw [← Ideal.absNorm_eq_natCard Q, ← Ideal.absNorm_eq_natCard P]
  rw [← e1, ← e2]

end GlobalTheory.NormDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrimeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  first | exact @GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | exact GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | (intros; apply GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf

namespace GlobalTheory.GoodFree

end GlobalTheory.GoodFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContainsAfterLocalization
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

namespace GlobalTheory.CoefDuty.MemberO

variable {D : D7}

set_option maxHeartbeats 1000000 in
theorem live_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem zdecomp_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) : ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem chosen_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) (S : Set ℂ) :
    Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem goodR_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem taken_iff (L : LocAll (lay0 D)) (i : L.X.nd.Loc) :
    (∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔
      ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ := Iff.rfl

end GlobalTheory.CoefDuty.MemberO

namespace GlobalTheory.CoefDuty.MemberO



end GlobalTheory.CoefDuty.MemberO

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRestrictScalarsHomMaximalRealSubfield
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

open scoped Topology
namespace GlobalTheory

theorem restrictScalarsHom_maximalRealSubfield_continuous :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  intro E Ω _ _ _ _ _
  set F := maximalRealSubfield E
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem mspanR_rt {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_kerOp {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    kerOp ν k γ F ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk

theorem word_nil (φ : Sm E a) : GlobalTheory.GLFin.word [] φ = φ := by simp [GlobalTheory.GLFin.word]

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by simp [GlobalTheory.GLFin.word]

theorem word_append (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.map_append, List.prod_append]

theorem word_single (X : Lie E a) (φ : Sm E a) : GlobalTheory.GLFin.word [X] φ = lie E a X φ := by simp [GlobalTheory.GLFin.word]

def adH (h : GA E a) (X : Lie E a) : Lie E a :=
  toL ((GeneralLinearGroup.map (pInf E) h)⁻¹.val * Matrix.of X * (GeneralLinearGroup.map (pInf E) h).val)

theorem lie_rt (h : GA E a) (X : Lie E a) (φ : Sm E a) :
    lie E a X (rt E a h φ) = rt E a h (lie E a (adH h X) φ) := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have eh : h = infGL E a y * finGL E a k := (infGL_mul_finGL h).symm
  have e1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e2 : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e2] at e1
  have e3 := lie_rt_fin (adH h X) k
  have key : lie E a X * rt E a h = rt E a h * lie E a (adH h X) := by
    have e4 : rt E a h = rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [← map_mul, ← eh]
    rw [e4, ← mul_assoc, ← e1, mul_assoc]
    change _ * (lie E a (adH h X) * _) = _
    rw [e3, ← mul_assoc]
  exact LinearMap.congr_fun key φ

theorem word_rt (h : GA E a) : ∀ (l : List (Lie E a)) (φ : Sm E a),
    GlobalTheory.GLFin.word l (rt E a h φ) = rt E a h (GlobalTheory.GLFin.word (l.map (adH h)) φ)
  | [], φ => by simp [GlobalTheory.GLFin.word]
  | X :: l, φ => by rw [word_cons, word_rt h l, lie_rt, List.map_cons, word_cons]


variable (E a) in
def bccSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsBCC F}
  zero_mem' := (_root_.GlobalTheory.JSW.isBCC_zero_and_add E a).1
  add_mem' {F G} hF hG := by simpa using (_root_.GlobalTheory.JSW.isBCC_zero_and_add E a).2 1 F G hF hG
  smul_mem' c F hF := by simpa using (_root_.GlobalTheory.JSW.isBCC_zero_and_add E a).2 c F 0 hF (_root_.GlobalTheory.JSW.isBCC_zero_and_add E a).1

def dSub (π : CuspSub E a) : Submodule ℂ (Sm E a) :=
  ⨅ l : List (Lie E a), (mspanR π ⊓ bccSub E a).comap ((Sm E a).subtype ∘ₗ GlobalTheory.GLFin.word l)

theorem mem_dSub {π : CuspSub E a} {φ : Sm E a} :
    φ ∈ dSub π ↔ ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  simp only [dSub, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_inf, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

theorem lie_mem_dSub {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ dSub π) (X : Lie E a) : lie E a X φ ∈ dSub π :=
  mem_dSub.2 fun l => by rw [← word_append]; exact mem_dSub.1 h _

theorem isBCC_rt {F : GA E a → ℂ} (hF : IsBCC F) (h : GA E a) : IsBCC (fun g => F (g * h)) := by
  refine ⟨hF.cont.comp (continuous_mul_const h), ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hF.bdd
    exact ⟨C, fun g => hC (g * h)⟩
  · intro r h0 h1 _ _ μ 𝓕 hμ hF' g
    simpa only [mul_assoc] using hF.cusp r h0 h1 μ 𝓕 hμ hF' (g * h)
  · intro γ g
    simpa only [mul_assoc] using hF.left γ (g * h)

theorem rt_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) (h : GA E a) : rt E a h φ ∈ dSub π :=
  mem_dSub.2 fun l => by
    rw [word_rt]
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ (l.map (adH h))
    exact ⟨mspanR_rt h1 h, isBCC_rt h2 h⟩

theorem isBCC_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : IsBCC φ.1 :=
  ⟨(π.cusp φ h).1.continuous, hB.of_isUnitary hπ h, (π.cusp φ h).2, (π.cusp φ h).1.left⟩

theorem word_mem (π : CuspSub E a) : ∀ (l : List (Lie E a)) {φ : Sm E a}, φ ∈ π.V → GlobalTheory.GLFin.word l φ ∈ π.V
  | [], _, h => by rw [word_nil]; exact h
  | X :: l, _, h => by rw [word_cons]; exact π.stable (.lie X) _ (word_mem π l h)

theorem mem_dSub_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : φ ∈ dSub π :=
  mem_dSub.2 fun l => ⟨mem_mspanR_of_mem (word_mem π l h), isBCC_of_mem hB hπ (word_mem π l h)⟩

theorem isBCC_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : IsBCC φ.1) :
    IsBCC (kerOp ν k γ φ.1) := by
  refine ⟨(_root_.GlobalTheory.JSW.kerOp_integrable_continuous E a X ν k γ hk φ hφ.cont hφ.bdd).2,
    ?_, _root_.GlobalTheory.JSW.isCuspidal_kerOp E a X ν k γ hk φ hφ, ?_⟩
  · obtain ⟨C, hC⟩ := hφ.bdd
    have hi : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
    refine ⟨C * ∫ x, ‖k x‖ ∂ν, fun g => ?_⟩
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · intro γ' g
    simp only [kerOp, mul_assoc, hφ.left]

theorem hasFDerivAt_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (hk : IsRapidInf ν k γ) (φ : Sm E a) (hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2)
      (oneL E a) := by
  rw [← _root_.GlobalTheory.JSW.integral_fderiv_chart_eq E a X ν k γ hk φ hd g]
  exact _root_.GlobalTheory.JSW.hasFDerivAt_chart_kerOp E a X ν k γ hk φ hb hd g

theorem kerOp_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    ∃ ψ ∈ dSub π, ψ.1 = kerOp ν k γ φ.1 := by
  let K : Set (GA E a → ℂ) := {f | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (φ : Sm E a), IsRapidInf ν k γ ∧ φ ∈ dSub π ∧ f = kerOp ν k γ φ.1}
  have hder : ∀ f ∈ K, ∃ fs : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a)) → GA E a → ℂ,
      (∀ p, fs p ∈ K) ∧ ∀ g, HasFDerivAt (chart f g) (∑ p, fs p g • lieCoord E a p.2) (oneL E a) := by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    have hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by simpa [word_nil] using (mem_dSub.1 hφ []).2.bdd
    have hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C := fun i => by
      simpa [word_single] using (mem_dSub.1 hφ [lieBasis E a i]).2.bdd
    exact ⟨fun p => kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1,
      fun p => ⟨X, _, ν, inferInstance, _, γ, _, _root_.GlobalTheory.JSW.isRapidInf_mul_adCoef E a X ν k γ hk p, lie_mem_dSub hφ _, rfl⟩,
      hasFDerivAt_kerOp ν k γ hk φ hb hd⟩
  have hSm : ∀ f ∈ K, f ∈ Sm E a := _root_.GlobalTheory.SmOfDeriv.mem_Sm_of_hasFDerivAt E a K fun f hf => by
    obtain ⟨fs, h1, h2⟩ := hder f hf
    exact ⟨_, inferInstance, fs, fun p => lieCoord E a p.2, h1, h2⟩
  have hspan : Submodule.span ℂ K ≤ Sm E a := Submodule.span_le.2 hSm
  have hlie : ∀ f ∈ Submodule.span ℂ K, ∀ (h : f ∈ Sm E a) (Y : Lie E a),
      (lie E a Y ⟨f, h⟩).1 ∈ Submodule.span ℂ K := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      intro h Y
      obtain ⟨fs, h1, h2⟩ := hder f hf
      have e : (lie E a Y ⟨f, h⟩).1 = ∑ p, (lieCoord E a p.2 Y) • fs p := by
        funext g
        rw [CuspRep.lie_apply, lieD, (h2 g).fderiv]
        simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          smul_eq_mul, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (h1 p))
    | zero =>
      intro h Y
      have : (⟨0, h⟩ : Sm E a) = 0 := rfl
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | add f f' hf hf' ihf ihf' =>
      intro h Y
      have : (⟨f + f', h⟩ : Sm E a) = ⟨f, hspan hf⟩ + ⟨f', hspan hf'⟩ := rfl
      rw [this, map_add (f := _)]
      exact Submodule.add_mem _ (ihf _ Y) (ihf' _ Y)
    | smul c f hf ihf =>
      intro h Y
      have : (⟨c • f, h⟩ : Sm E a) = c • ⟨f, hspan hf⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c (ihf _ Y)
  have hword : ∀ (l : List (Lie E a)) (ψ : Sm E a), ψ.1 ∈ Submodule.span ℂ K →
      (GlobalTheory.GLFin.word l ψ).1 ∈ Submodule.span ℂ K := by
    intro l
    induction l with
    | nil => intro ψ h; rwa [word_nil]
    | cons Y l ih => intro ψ h; rw [word_cons]; exact hlie _ (ih ψ h) _ Y
  have hgood : Submodule.span ℂ K ≤ mspanR π ⊓ bccSub E a := Submodule.span_le.2 (by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ []
    rw [word_nil] at h1 h2
    exact ⟨mspanR_kerOp h1 ν k γ hk, isBCC_kerOp ν k γ hk φ h2⟩)
  have hmem : kerOp ν k γ φ.1 ∈ K := ⟨X, _, ν, inferInstance, k, γ, φ, hk, hφ, rfl⟩
  exact ⟨⟨_, hSm _ hmem⟩, mem_dSub.2 fun l => hgood (hword l _ (Submodule.subset_span hmem)), rfl⟩

theorem mspanR_le (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    mspanR π ≤ (dSub π).map (Sm E a).subtype := by
  refine sInf_le ⟨fun φ hφ => ⟨φ, mem_dSub_of_mem hB hπ hφ, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩ h
    exact ⟨rt E a h φ, rt_mem_dSub hφ h, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩ X _ ν _ k γ hk
    obtain ⟨ψ, h1, h2⟩ := kerOp_mem_dSub hφ ν k γ hk
    exact ⟨ψ, h1, h2⟩

theorem mspanR_words (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  intro F hF
  obtain ⟨φ, hφ, rfl⟩ := mspanR_le hB hπ hF
  exact ⟨φ, rfl, mem_dSub.1 hφ⟩

theorem mspanR_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    GlobalTheory.Published.CuspFormsBoundedGL → ∀ π : CuspSub E a, π.IsUnitary → ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      (∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  intro E _ _ _ a hB π hπ F hF
  obtain ⟨φ, rfl, h⟩ := mspanR_words hB hπ F hF
  have h0 := (h []).2
  rw [word_nil] at h0
  exact ⟨φ, rfl, fun l => (h l).1, h0.cusp, h0.bdd⟩

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryAutForm_eq_zero_of_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ), IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  first | exact @GlobalTheory.DefiniteDense.eq_zero_of_finU | exact GlobalTheory.DefiniteDense.eq_zero_of_finU | (intros; apply GlobalTheory.DefiniteDense.eq_zero_of_finU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downward_theta_integral_sobolev_continuous : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  first | exact @GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | exact GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | (intros; apply GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConstantIntegralArcFramesStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_integral_arc_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  first | exact @GlobalTheory.ArcFrame.exists_arcFrame | exact GlobalTheory.ArcFrame.exists_arcFrame | (intros; apply GlobalTheory.ArcFrame.exists_arcFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_nhd_one_in_unitary_principal_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ), 0 < N → ∃ O : Set (finU (E := L) (n := n)), IsOpen O ∧ (1 : finU (E := L) (n := n)) ∈ O ∧ ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  first | exact @GlobalTheory.CongOpen.exists_open_cong | exact GlobalTheory.CongOpen.exists_open_cong | (intros; apply GlobalTheory.CongOpen.exists_open_cong <;> assumption)
end

