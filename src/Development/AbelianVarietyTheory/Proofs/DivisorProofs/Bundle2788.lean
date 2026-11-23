module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitOfPoint

variable {p : ℕ} [Fact p.Prime]

theorem base_integralClosure (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ _ : IsDiscreteValuationRing (integralClosure ℤ_[p] K), GlobalTheory.Mum.Base (integralClosure ℤ_[p] K) := by
  haveI := GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  exact ⟨inferInstance, ⟨inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure K⟩, GlobalTheory.charZero_integralClosure_padicInt⟩

theorem lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have hft := h.ft
  have := M.lft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

end GlobalTheory.Poinc.TraitOfPoint


open GlobalTheory.Poinc.TraitOfPoint Polynomial in
theorem GlobalTheory.Poinc.exists_trait_of_classical_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  intro g n F Z i hi W8 X₁ Y πY p _ y hy
  haveI := hi
  haveI := lft_toInt Y
  obtain ⟨K, hK, H⟩ := GlobalTheory.padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := H K le_rfl
  obtain ⟨hdvr, hbase⟩ := base_integralClosure K

  have hinj₀ : Function.Injective (algebraMap (integralClosure ℤ_[p] K) (PadicAlgCl p)) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  let ι₀ : FractionRing (integralClosure ℤ_[p] K) →+* PadicAlgCl p := IsFractionRing.lift hinj₀
  have hgen : gPt p ≫ spMap j₀ = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) :=
    GlobalTheory.ArcPointDescent.sp_sq fun a => by
      simp only [ι₀, IsFractionRing.lift_algebraMap]
      exact hj₀ a
  have hrange : Set.range (jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hw : w = spMap ι₀ (IsLocalRing.closedPoint (PadicAlgCl p)) := Subsingleton.elim _ _
    refine hy ⟨IsLocalRing.closedPoint (PadicAlgCl p), ?_⟩
    have e : gPt p ≫ y ≫ πY ≫ X₁.π = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := by
      rw [← hy₀]
      simp only [← Category.assoc]
      rw [hgen]
    rw [e, hw]
    exact Scheme.Hom.comp_apply _ _ _
  let yK := IsOpenImmersion.lift i _ hrange
  obtain ⟨T, f, fK, hfinj, -, hffin, hfK, hTy⟩ :=
    _root_.GlobalTheory.Poinc.traitExtSt g n (cycAway n) (zetaAway n) F (integralClosure ℤ_[p] K) hbase hdvr yK

  letI : Algebra (integralClosure ℤ_[p] K) T.V := f.toAlgebra
  haveI : Module.Finite (integralClosure ℤ_[p] K) T.V := hffin
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) T.V :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (FractionRing T.V) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    rw [IsScalarTower.algebraMap_eq (integralClosure ℤ_[p] K) T.V (FractionRing T.V)]
    exact (IsFractionRing.injective T.V (FractionRing T.V)).comp hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (PadicAlgCl p) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj₀
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) T.V := inferInstance
  haveI : Algebra.IsAlgebraic T.V (FractionRing T.V) := IsLocalization.isAlgebraic _ (nonZeroDivisors T.V)
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) (FractionRing T.V) :=
    Algebra.IsAlgebraic.trans (integralClosure ℤ_[p] K) T.V (FractionRing T.V)
  let ι' : FractionRing T.V →ₐ[integralClosure ℤ_[p] K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι : FractionRing T.V →+* PadicAlgCl p := ι'.toRingHom
  have hιf : ∀ a : integralClosure ℤ_[p] K, ι (algebraMap T.V (FractionRing T.V) (f a)) = ((a : K) : PadicAlgCl p) := by
    intro a
    have h1 := ι'.commutes a
    rw [IsScalarTower.algebraMap_apply (integralClosure ℤ_[p] K) T.V (FractionRing T.V)] at h1
    exact h1

  let φ : ℤ_[p] →+* T.V := f.comp (algebraMap ℤ_[p] (integralClosure ℤ_[p] K))
  have hcomp : ι.comp ((algebraMap T.V (FractionRing T.V)).comp φ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
    ext c
    change ι (algebraMap T.V (FractionRing T.V) (f (algebraMap ℤ_[p] (integralClosure ℤ_[p] K) c))) = _
    rw [hιf]
    rfl
  have hφint : φ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x) hffin.to_isIntegral

  have hint : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, hPm, hP⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (ι x)).2 hx
      have hTV : IsIntegral T.V x := by
        refine ⟨P.map φ, hPm.map φ, ?_⟩
        rw [Polynomial.eval₂_map]
        apply ι.injective
        rw [Polynomial.hom_eval₂, hcomp, map_zero]
        exact hP
      exact IsIntegrallyClosed.isIntegral_iff.1 hTV
    · rintro ⟨v, rfl⟩
      obtain ⟨P, hPm, hP⟩ := hφint v
      apply (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
      refine ⟨P, hPm, ?_⟩
      have h2 := congrArg (ι.comp (algebraMap T.V (FractionRing T.V))) hP
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [← hcomp, ← RingHom.comp_assoc]
      exact h2
  let j : T.V →+* OO p := (ι.comp (algebraMap T.V (FractionRing T.V))).codRestrict (OO p) fun v =>
    (mem_OO_iff _).2 ((hint _).2 ⟨v, rfl⟩)
  have hjf : j.comp f = j₀ := by
    ext a
    change ι (algebraMap T.V (FractionRing T.V) (f a)) = ((j₀ a : OO p) : PadicAlgCl p)
    rw [hιf, hj₀]
  refine ⟨T, ι, j, spMap f ≫ y₀, hint, fun v => rfl, ?_, ?_, ?_⟩
  · refine ⟨fun v hv => ?_⟩
    have h1 : ‖ι (algebraMap T.V (FractionRing T.V) v)‖ = 1 :=
      le_antisymm ((hint _).2 ⟨v, rfl⟩) (not_lt.1 fun h => ((not_isUnit_OO_iff (j v)).2 h) hv)
    have h0 : algebraMap T.V (FractionRing T.V) v ≠ 0 := fun h => by
      rw [h, map_zero, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨w, hw⟩ := (hint (algebraMap T.V (FractionRing T.V) v)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective T.V (FractionRing T.V) ?_)
    rw [map_mul, map_one, hw, mul_inv_cancel₀ h0]
  · rw [← Category.assoc, GlobalTheory.ArcPointDescent.sp_comp (h := j₀) (fun a => by rw [← hjf]; rfl), hy₀]
  · have e1 : jK T.V ≫ spMap f = spMap fK ≫ jK (integralClosure ℤ_[p] K) :=
      GlobalTheory.ArcPointDescent.sp_sq fun a => (hfK a).symm
    have hyK : yK ≫ i = jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
    rw [hTy, Category.assoc (spMap fK) yK i, hyK]
    simp only [← Category.assoc]
    rw [e1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

noncomputable section

namespace GlobalTheory.KerConjMean

theorem pow_le_exp_posLog (x : ℝ) (g : ℕ) : x ^ g ≤ Real.exp (g * Real.posLog x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases g with _ | g
    · simp
    · rw [zero_pow (Nat.succ_ne_zero g)]; exact (Real.exp_pos _).le
  · calc x ^ g ≤ |x ^ g| := le_abs_self _
      _ = |x| ^ g := abs_pow x g
      _ = Real.exp (g * Real.log |x|) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos (abs_pos.2 hx) g)]
      _ ≤ Real.exp (g * Real.posLog x) := by
          gcongr
          rw [Real.log_abs]; unfold Real.posLog; exact le_max_right _ _

theorem max_pow_le_exp_posLog (A : ℝ) (hA : 0 < A) (d : ℕ) :
    max 1 A⁻¹ ^ d ≤ Real.exp (d * Real.posLog A⁻¹) := by
  have h1 : max 1 A⁻¹ ≤ Real.exp (Real.posLog A⁻¹) := by
    refine max_le ?_ ?_
    · exact Real.one_le_exp (by unfold Real.posLog; exact le_max_left _ _)
    · calc A⁻¹ = Real.exp (Real.log A⁻¹) := (Real.exp_log (inv_pos.2 hA)).symm
        _ ≤ Real.exp (Real.posLog A⁻¹) := by gcongr; unfold Real.posLog; exact le_max_right _ _
  calc max 1 A⁻¹ ^ d ≤ Real.exp (Real.posLog A⁻¹) ^ d := pow_le_pow_left₀ (by positivity) h1 d
    _ = Real.exp (d * Real.posLog A⁻¹) := (Real.exp_nat_mul _ d).symm

theorem size_bound (K f N b rd Kx W1 W2 a bb c : ℝ) (g : ℕ) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hcf : c ≤ f) (hb3 : 3 ≤ b) (hN1 : 1 ≤ N) (hNb : N ≤ b)
    (hf1 : 1 ≤ f) (hfb : f ≤ b) (hrd0 : 0 ≤ rd) (hrd : rd ≤ b) (ha0 : 0 ≤ a) (haN : a ≤ N) (hbb0 : 0 ≤ bb)
    (hbN : bb ≤ N) (hW1 : W1 ≤ f * N * (8 * b)) (hW2 : W2 ≤ f * N * (8 * b)) (hW10 : 0 ≤ W1) (hW20 : 0 ≤ W2)
    (hg : (g : ℝ) = f * a * bb) (hKx : 0 < Kx)
    (hlogKx : Real.log Kx ≤ K * (W1 + W2 + c * (a + bb) ^ 2 + 1) * Real.log (2 + W1 + W2 + a + bb + c)) :
    Real.log (3 * (2 * (g : ℝ) * rd + 1) ^ g * Kx) ≤ (6 + 126 * K) * f * N * b * Real.log b ∧
      (g : ℝ) ≤ f * N * b := by
  have hb0 : 0 < b := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hlogb : 1 ≤ Real.log b := by
    have : Real.exp 1 ≤ b := by linarith [Real.exp_one_lt_d9]
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hfN1 : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf1 hN1
  have hfNb : 1 ≤ f * N * b := by nlinarith
  have hab : a * bb ≤ N * N := mul_le_mul haN hbN hbb0 hN0
  have hfNN : f * a * bb ≤ f * N * N := by
    have := mul_le_mul_of_nonneg_left hab hf0
    linarith
  have hNN : f * N * N ≤ f * N * b := mul_le_mul_of_nonneg_left hNb (by positivity)
  have hgG : (g : ℝ) ≤ f * N * b := by rw [hg]; linarith
  have hfNb3 : f * N * b ≤ b ^ 3 := by
    have h1 := mul_le_mul hfb hNb hN0 hb0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hb0.le
    calc f * N * b ≤ b * b * b := h2
      _ = _ := by ring
  have hg3 : (g : ℝ) ≤ b ^ 3 := hgG.trans hfNb3
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have hrdpos : 0 < 2 * (g : ℝ) * rd + 1 := by have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith
  have hq : 2 * (g : ℝ) * rd + 1 ≤ 3 * b ^ 4 := by
    have h1 := mul_le_mul hg3 hrd hrd0 (by positivity)
    have h2 : (1 : ℝ) ≤ b ^ 4 := one_le_pow₀ (by linarith)
    have h3 : b ^ 3 * b = b ^ 4 := by ring
    linarith
  have hl3 : Real.log 3 ≤ Real.log b := Real.log_le_log (by norm_num) hb3
  have hlq : Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * Real.log b := by
    calc _ ≤ Real.log (3 * b ^ 4) := Real.log_le_log hrdpos hq
      _ = Real.log 3 + 4 * Real.log b := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ _ := by linarith
  have hlq0 : 0 ≤ Real.log (2 * (g : ℝ) * rd + 1) := Real.log_nonneg (by
    have := mul_nonneg (mul_nonneg zero_le_two hg0) hrd0; linarith)
  have hY0 : 0 ≤ f * N * b * Real.log b := by positivity
  have hgl : (g : ℝ) * Real.log (2 * (g : ℝ) * rd + 1) ≤ 5 * (f * N * b * Real.log b) := by
    have := mul_le_mul hgG hlq hlq0 (by positivity); linarith
  have hKb : Real.log Kx ≤ 126 * K * (f * N * b * Real.log b) := by
    have hsq : (a + bb) ^ 2 ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hab2 : c * (a + bb) ^ 2 ≤ 4 * (f * N * b) := by
      have := mul_le_mul hcf hsq (by positivity) hf0
      have e : f * (2 * N) ^ 2 = 4 * (f * N * N) := by ring
      linarith
    have hQ1 : W1 + W2 + c * (a + bb) ^ 2 + 1 ≤ 21 * (f * N * b) := by linarith
    have hQ1' : 0 ≤ W1 + W2 + c * (a + bb) ^ 2 + 1 := by positivity
    have hArg0 : 0 < 2 + W1 + W2 + a + bb + c := by linarith
    have hb27 : (27 : ℝ) ≤ b ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hb3 3; norm_num at this; linarith
    have hbb3 : b ≤ b ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hArg : 2 + W1 + W2 + a + bb + c ≤ 27 * b ^ 3 := by linarith
    have hQ2 : Real.log (2 + W1 + W2 + a + bb + c) ≤ 6 * Real.log b := by
      calc _ ≤ Real.log (27 * b ^ 3) := Real.log_le_log hArg0 hArg
        _ = 3 * Real.log 3 + 3 * Real.log b := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
              show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
        _ ≤ _ := by linarith
    have hQ20 : 0 ≤ Real.log (2 + W1 + W2 + a + bb + c) := Real.log_nonneg (by linarith)
    have := mul_le_mul (mul_le_mul_of_nonneg_left hQ1 hK0) hQ2 hQ20 (by positivity)
    refine hlogKx.trans (this.trans (le_of_eq ?_))
    ring
  refine ⟨?_, hgG⟩
  rw [Real.log_mul (by positivity) hKx.ne', Real.log_mul (by norm_num) (pow_pos hrdpos g).ne', Real.log_pow]
  have hlY : Real.log b ≤ f * N * b * Real.log b := le_mul_of_one_le_left (by linarith) hfNb
  have e : (6 + 126 * K) * f * N * b * Real.log b =
      f * N * b * Real.log b + 5 * (f * N * b * Real.log b) + 126 * K * (f * N * b * Real.log b) := by ring
  rw [e]; linarith

end GlobalTheory.KerConjMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem exists_linearEquiv_of_rel {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : M → N → Prop) (h1 : ∀ c, ∃ h, p c h) (h2 : ∀ h, ∃ c, p c h)
    (h0 : ∀ c h, p c h → (c = 0 ↔ h = 0)) (hadd : ∀ a b h h', p a h → p b h' → p (a + b) (h + h'))
    (hsmul : ∀ (r : R) a h, p a h → p (r • a) (r • h)) : ∃ e : M ≃ₗ[R] N, ∀ c h, e c = h ↔ p c h := by
  choose f hf using h1
  have uniq : ∀ c h h', p c h → p c h' → h' = h := by
    intro c h h' ph ph'
    have q := hadd _ _ _ _ ph' (hsmul (-1) _ _ ph)
    rw [neg_one_smul, neg_one_smul, add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).1 rfl)
  let g : M →ₗ[R] N :=
    { toFun := f
      map_add' := fun a b ↦ uniq _ _ _ (hadd _ _ _ _ (hf a) (hf b)) (hf (a + b))
      map_smul' := fun r a ↦ uniq _ _ _ (hsmul r _ _ (hf a)) (hf (r • a)) }
  have inj : Function.Injective g := by
    intro a b hab
    have q := hadd _ _ _ _ (hf a) (hsmul (-1) _ _ (hf b))
    rw [neg_one_smul, neg_one_smul] at q
    have hab' : f a = f b := hab
    rw [hab', add_neg_cancel] at q
    exact add_neg_eq_zero.1 ((h0 _ _ q).2 rfl)
  have surj : Function.Surjective g := by
    intro h
    obtain ⟨c, hc⟩ := h2 h
    exact ⟨c, uniq _ _ _ hc (hf c)⟩
  refine ⟨LinearEquiv.ofBijective g ⟨inj, surj⟩, fun c h ↦ ⟨?_, fun ph ↦ uniq _ _ _ ph (hf c)⟩⟩
  rintro rfl
  exact hf c

end GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem crystallineSmoothLift_of_relations : GlobalTheory.Published.CrystallineSmoothLift := by
  have Λ : ∀ D : Data, Lift D := fun D ↦ Classical.choice (_root_.GlobalTheory.SmoothLift.LiftEx.nonempty_lift D)
  obtain ⟨hr1, hr2⟩ := _root_.GlobalTheory.PDForm.rel_total_zero
  have E1 : ∀ D : Data, ∃ e : CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s, ∀ c h, e c = h ↔ (Λ D).Rel1 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr1 D (Λ D)).1 (hr1 D (Λ D)).2.1 (hr1 D (Λ D)).2.2
      (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).1 (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).2.1
  have E2 : ∀ D : Data, ∃ e : CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s, ∀ c h, e c = h ↔ (Λ D).Rel2 c h := fun D ↦
    exists_linearEquiv_of_rel _ (hr2 D (Λ D)).1 (hr2 D (Λ D)).2.1 (hr2 D (Λ D)).2.2
      (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).2.2.1 (_root_.GlobalTheory.PDForm.rel_add_smul D (Λ D)).2.2.2
  choose e₁ he₁ using E1
  choose e₂ he₂ using E2
  have r1 : ∀ D c, (Λ D).Rel1 c (e₁ D c) := fun D c ↦ (he₁ D c _).1 rfl
  have r2 : ∀ D c, (Λ D).Rel2 c (e₂ D c) := fun D c ↦ (he₂ D c _).1 rfl
  refine ⟨e₁, e₂, ?_, ?_, ?_⟩
  · intro D a b
    exact (he₂ D _ _).2 (_root_.GlobalTheory.PDForm.Lift.lift_rel2_cup D (Λ D) a b _ _ (r1 D a) (r1 D b))
  · intro D m c
    exact (he₁ D _ _).2 (_root_.GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1 D (Λ D) m c)
  · intro D D' σ φ φ₀ h m hc
    exact ⟨fun c ↦ _root_.GlobalTheory.PDForm.LiftNat.main.1 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r1 D c) (r1 D' _),
      fun c ↦ _root_.GlobalTheory.PDForm.LiftNat.main.2 D D' (Λ D) (Λ D') σ φ φ₀ h m hc c _ _ (r2 D c) (r2 D' _)⟩

end GlobalTheory.SmoothLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomThetaIntegralNormSqEqPetersson
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.NormBigDict

theorem normSq_eq_petersson : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (P : PolF D WW.rank A.rank)
    (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure → IsFundamentalDomain (GQ WW) 𝓕 ν →
    ∃ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure ∧
      ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) =
        petersson WW ν (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) (up ((X.ω t).toSgn true) m (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) fun _ => 1) := by
  intro D T L sc G W i j A A' WW X hX t P ν 𝓕 hν h𝓕
  have h := hX.is
  obtain ⟨ν₁, hν₁, hfd, hint⟩ := GlobalTheory.SgnIdent.meas_sgn true A X.m X.fd h.meas.1 h.meas.2
  refine ⟨ν₁, hν₁, ?_⟩
  have hW := h.weil t
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ)
    X.rA.B X.rW.s X.rW.B (GlobalTheory.ConstRatio.theta_f h t).1 P
  set Φ := pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P with hΦd
  set om := (X.ω t).toSgn true with hom

  have hg : ∀ y : GA D WW, AutomorphicL2Unitary.LeftInv (GQ (GlobalTheory.Grid.neg A)) (fun g => thetaKO om g y Φ * (fun _ => (1 : ℂ)) g) := by
    intro y γ hγ g
    show om (γ * g, y) Φ 0 * 1 = om (g, y) Φ 0 * 1
    have e : ((γ * g, y) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (γ, 1) * (g, y) := by rw [Prod.mk_mul_mk, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    rw [hW.om_aut γ hγ 1 (GQ WW).one_mem _ (hW.om_pres _ _ hΦ)]

  have hup : ∀ y, up om ν₁ Φ (fun _ => 1) y = X.I W.ψ W.θ t P y := by
    intro y
    haveI := hν₁
    simp only [up, AutomorphicL2Unitary.autMeasure]
    rw [integral_quotMeasure hfd]
    simp only [(hg y).descend_mk]
    simp only [mul_one]
    exact (hint fun g => thetaKO (X.ω t) g y Φ).2

  have hinv : AutomorphicL2Unitary.LeftInv (GQ WW) (up om ν₁ Φ fun _ => 1) := by
    intro γ hγ y
    rw [hup, hup]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.ker]
    congr 1
    funext g
    exact GlobalTheory.ThetaMean.leftInv_theta hW hΦ ((GlobalTheory.Grid.ofSgn true A).symm g) γ hγ y
  haveI := hν
  simp only [petersson, pet]
  rw [integral_quotMeasure h𝓕]
  simp only [hinv.descend_mk, hup, Complex.mul_conj, ← Complex.sq_norm]
  exact (integral_ofReal).symm

end GlobalTheory.NormBigDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteThetaPairNormNeZeroOfCoordNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormPos

theorem norm_ne_zero_of_coord : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ) (Q : ℕ) (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q), (∃ h T, P.coord h T ≠ 0) → P.norm ≠ 0 := by
  intro D hI δ t0 Q P h
  exact ((GlobalTheory.NormSum.RepInv.rep_indep D hI ⊤ δ t0 Q P.crv P.pt0 P P.level_pos).2.2.2.2 h).ne'

end GlobalTheory.NormPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
end

