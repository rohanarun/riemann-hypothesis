module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMulOfEtaleSplitting
section
open GlobalTheory.JR MeasureTheory
open scoped Pointwise

namespace GlobalTheory.JR.EtProdAbs

theorem distribHaarChar_prod {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by
  borelize R₁ R₂
  let μ₁ : Measure R₁ := Measure.addHaar
  let μ₂ : Measure R₂ := Measure.addHaar
  obtain ⟨S₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₁) := inferInstance
  obtain ⟨S₂⟩ : Nonempty (TopologicalSpace.PositiveCompacts R₂) := inferInstance
  have h0₁ : μ₁ (S₁ : Set R₁) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₁ S₁.interior_nonempty).ne'
  have h0₂ : μ₂ (S₂ : Set R₂) ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ₂ S₂.interior_nonempty).ne'
  have h1₁ : μ₁ (S₁ : Set R₁) ≠ ⊤ := S₁.isCompact.measure_lt_top.ne
  have h1₂ : μ₂ (S₂ : Set R₂) ≠ ⊤ := S₂.isCompact.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ₁.prod μ₂) (s := (S₁ : Set R₁) ×ˢ (S₂ : Set R₂))
    (by rw [Measure.prod_prod]; exact mul_ne_zero h0₁ h0₂)
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top h1₁ h1₂) ?_
  have hs : v • ((S₁ : Set R₁) ×ˢ (S₂ : Set R₂)) =
      (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v • (S₁ : Set R₁)) ×ˢ
        (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v • (S₂ : Set R₂)) := by
    ext ⟨x, y⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_prod, Set.mem_prod, Set.mem_smul_set_iff_inv_smul_mem,
      Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ← map_inv]
    exact Iff.rfl
  rw [hs, Measure.prod_prod, Measure.prod_prod, ← distribHaarChar_mul μ₁, ← distribHaarChar_mul μ₂]
  push_cast
  ring

theorem absK_prod : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (t : A.K),
    A.absK t = A₁.absK (eK t).1 * A₂.absK (eK t).2 := by
  intro F E _ _ _ _ U A A₁ A₂ eK t
  have := U.ultraF; have := U.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₁.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A₂.K
  by_cases ht : IsUnit t
  · let u : A.Kˣ := ht.unit
    let v : (A₁.K × A₂.K)ˣ := Units.map (eK : A.K →* A₁.K × A₂.K) u
    let e' : A.K ≃ₜ+ A₁.K × A₂.K :=
      { eK.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap eK.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap eK.symm.toLinearMap }
    have h1 : distribHaarChar (A₁.K × A₂.K) v = distribHaarChar A.K u :=
      ModuleNorm.distribHaarChar_transport e' u v (fun x => by
        change eK ((u : A.K) * x) = eK (u : A.K) * eK x
        rw [map_mul])
    rw [distribHaarChar_prod] at h1
    have ht' : t = (u : A.K) := (IsUnit.unit_spec ht).symm
    have e1 : (eK t).1 = ((Units.map (RingHom.fst A₁.K A₂.K : A₁.K × A₂.K →* A₁.K) v : A₁.Kˣ) : A₁.K) := by
      rw [ht']; rfl
    have e2 : (eK t).2 = ((Units.map (RingHom.snd A₁.K A₂.K : A₁.K × A₂.K →* A₂.K) v : A₂.Kˣ) : A₂.K) := by
      rw [ht']; rfl
    rw [e1, e2, ht', EtMeas.absK_unit, EtMeas.absK_unit, EtMeas.absK_unit, ← h1]
    push_cast
    rfl
  · have h0 : A.absK t = 0 := by simp [Et.absK, ht]
    have hn : ¬ IsUnit (eK t) := fun h => ht ((isUnit_map_iff eK t).1 h)
    rw [Prod.isUnit_iff, not_and_or] at hn
    rw [h0]
    rcases hn with hn | hn
    · have : A₁.absK (eK t).1 = 0 := by simp [Et.absK, hn]
      rw [this, zero_mul]
    · have : A₂.absK (eK t).2 = 0 := by simp [Et.absK, hn]
      rw [this, mul_zero]

end GlobalTheory.JR.EtProdAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValNormUnramifiedInvolutionFieldExtEqMul
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr.NormVal

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem val_mul' {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by
  unfold val
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation E y ≠ 0 := by simpa using hy
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem val_one' : val O (1 : E) = 0 := by simp [val]

theorem val_pow' {x : E} (hx : x ≠ 0) (k : ℕ) : val O (x ^ k) = k * val O x := by
  induction k with
  | zero => simp [val_one']
  | succ k ih =>
    rw [pow_succ, val_mul' O (pow_ne_zero _ hx) hx, ih]
    push_cast; ring

theorem val_inv' {x : E} (hx : x ≠ 0) : val O x⁻¹ = -val O x := by
  have := val_mul' O hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, val_one'] at this
  omega

theorem exists_lift_of_val_eq_zero {x : E} (hx : x ≠ 0) (h : val O x = 0) : ∃ a : O, algebraMap O E a = x := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation E x ≠ 0 := by simpa using hx
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation E x = 1 := by
    unfold val at h
    rw [← WithZero.exp_log hx']
    have : WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x) = 0 := by omega
    rw [this, WithZero.exp_zero]
  exact IsDiscreteValuationRing.exists_lift_of_le_one h1.le

theorem val_algebraMap_unit (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by
  unfold val
  have : (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact fun h => (IsLocalRing.mem_maximalIdeal a).1 h ha
  rw [this]; simp

theorem exists_val_eq_one : ∃ π : E, val O π = 1 := by
  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal O).valuation_exists_uniformizer E
  exact ⟨π, by simp [val, hπ]⟩

end Gen

theorem norm_integral (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hφ : IsUnrExt K K' d φ) (hd : 0 < d) (z : K'.O) :
    ∃ a : K.O, algebraMap K.O K.E a = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt K K' d φ hφ hd
  have hwj : ∀ j, ∃ c : K'.O, algebraMap K'.O K'.E c = w j := by
    intro j
    refine (hw (w j)).2 fun k => ?_
    rw [w.repr_self, Finsupp.single_apply]
    split_ifs
    · exact ⟨1, map_one _⟩
    · exact ⟨0, map_zero _⟩
  have hM : ∀ i j, ∃ m : K.O, algebraMap K.O K.E m = Algebra.leftMulMatrix w (algebraMap K'.O K'.E z) i j := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    obtain ⟨c, hc⟩ := hwj j
    refine (hw _).1 ⟨z * c, ?_⟩ i
    rw [map_mul, hc]
  choose M hM using hM
  refine ⟨(Matrix.of M).det, ?_⟩
  rw [Algebra.norm_eq_matrix_det w, RingHom.map_det]
  congr 1
  ext i j
  simp [hM]

theorem normval : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d →
    ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by
  intro K K' d φ hφ hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hfr : Module.finrank K.E K'.E = d := hφ.2.2.2.2
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (hfr ▸ hd)
  by_cases hy : y = 0
  · subst hy
    rw [Algebra.norm_zero]
    simp [val]
  obtain ⟨π, hπ⟩ := exists_val_eq_one K.O (E := K.E)
  have hπ0 : π ≠ 0 := by rintro rfl; simp [val] at hπ
  have hφπ : val K'.O (φ π) = 1 := by rw [hφ.2.2.1, hπ]
  have hφπ0 : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
  set n := val K'.O y with hn
  set a := (-n).toNat
  set b := n.toNat
  have hab : (b : ℤ) - a = n := Int.toNat_sub_toNat_neg n
  set u := y * φ π ^ a * (φ π ^ b)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0))
  have hvu : val K'.O u = 0 := by
    rw [hu, val_mul' _ (mul_ne_zero hy (pow_ne_zero _ hφπ0)) (inv_ne_zero (pow_ne_zero _ hφπ0)),
      val_mul' _ hy (pow_ne_zero _ hφπ0), val_inv' _ (pow_ne_zero _ hφπ0), val_pow' _ hφπ0, val_pow' _ hφπ0, hφπ, ← hn]
    omega
  have hvu' : val K'.O u⁻¹ = 0 := by rw [val_inv' _ hu0, hvu]; rfl
  obtain ⟨u₁, hu₁⟩ := exists_lift_of_val_eq_zero K'.O hu0 hvu
  obtain ⟨u₂, hu₂⟩ := exists_lift_of_val_eq_zero K'.O (inv_ne_zero hu0) hvu'
  obtain ⟨m₁, hm₁⟩ := norm_integral K K' d φ hφ hd u₁
  obtain ⟨m₂, hm₂⟩ := norm_integral K K' d φ hφ hd u₂
  have hunit : IsUnit m₁ := by
    have h12 : m₁ * m₂ = 1 := by
      apply IsFractionRing.injective K.O K.E
      rw [map_mul, hm₁, hm₂, hu₁, hu₂, ← map_mul, mul_inv_cancel₀ hu0, map_one, map_one]
    exact IsUnit.of_mul_eq_one m₂ h12
  have hNu : val K.O (Algebra.norm K.E u) = 0 := by
    rw [← hu₁, ← hm₁]; exact val_algebraMap_unit K.O m₁ hunit
  have hNu0 : Algebra.norm K.E u ≠ 0 := Algebra.norm_ne_zero_iff.2 hu0
  have hNy0 : Algebra.norm K.E y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have hNφ : Algebra.norm K.E (φ π) = π ^ d := by
    rw [← hfr]; exact Algebra.norm_algebraMap π
  have key : y * φ π ^ a = u * φ π ^ b := by
    rw [hu, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hφπ0), mul_one]
  have key2 := congrArg (fun x => val K.O (Algebra.norm K.E x)) key
  simp only [map_mul, map_pow, hNφ] at key2
  rw [val_mul' _ hNy0 (pow_ne_zero _ (pow_ne_zero _ hπ0)), val_mul' _ hNu0 (pow_ne_zero _ (pow_ne_zero _ hπ0)),
    val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ (pow_ne_zero _ hπ0), val_pow' _ hπ0, hNu, hπ] at key2
  rw [← hab]
  push_cast at key2 ⊢
  linarith

end GlobalTheory.UnitLemma.Unr.NormVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaAllOrders
section
open GlobalTheory.PMonE

namespace GlobalTheory

theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact _root_.GlobalTheory.PMonE.glOnto_zero_and_glCount_zero
  · exact ⟨_root_.GlobalTheory.PMonE.glOnto_of_one N hN _root_.GlobalTheory.PMonE.gl1.1, _root_.GlobalTheory.PMonE.LinCount.glCount_of_one N hN _root_.GlobalTheory.PMonE.gl1.2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraEtaleOfSeparableCharpolyMulLeftStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  first | exact @GlobalTheory.etale_of_separable_charpoly_mulLeft | exact GlobalTheory.etale_of_separable_charpoly_mulLeft | (intros; apply GlobalTheory.etale_of_separable_charpoly_mulLeft <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapPadicIntFinExtInjective
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_padicInt_of_mem_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL) : ∃ y : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] y = x := by
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 x) := hx
  have hint' : IsIntegral ℤ_[l] x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

theorem algebraMap_padicInt_finExt_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

theorem algebraMap_padicInt_OL_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b h
  exact algebraMap_padicInt_finExt_injective LL (congrArg Subtype.val h)

private theorem associated_prime_of_valuation_eq_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (c : ℤ_[l]) (hc : P.v LL (algebraMap ℤ_[l] ↥LL.1 c) = 1) : Associated c (l : ℤ_[l]) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hc
    exact WithTop.top_ne_one hc
  have hspec := PadicInt.unitCoeff_spec hc0
  set u := PadicInt.unitCoeff hc0
  have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
    (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
  have hu0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
  have hval : c.valuation = 1 := by
    rw [hspec, map_mul, AddValuation.map_mul, hu0, zero_add, map_pow, AddValuation.map_pow,
      map_natCast, P.v_l LL, nsmul_one] at hc
    exact_mod_cast hc
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [hspec]
  rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem associated_of_v_sub_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (y : ℤ_[l]) (x : ↥(OL LL)) (hy : algebraMap ℤ_[l] ↥(OL LL) y = x)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x - 1) = 1) : Associated (y - 1) (l : ℤ_[l]) := by
  apply associated_prime_of_valuation_eq_one P LL
  have hx : algebraMap ↥(OL LL) ↥LL.1 x = algebraMap ℤ_[l] ↥LL.1 y := by
    rw [← hy]
    rfl
  rw [map_sub, map_one, ← hx]
  exact h

theorem exists_units_hom_lift {Γ R S : Type} [Group Γ] [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (c : Γ →* Sˣ) (hex : ∀ g, ∃ y : R, φ y = (c g : S)) :
    ∃ χ : Γ →* Rˣ, ∀ g, φ (χ g : R) = (c g : S) := by
  choose y hy using hex
  have hinv : ∀ g, y g * y g⁻¹ = 1 := fun g => hφ (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hinv' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hinv g⁻¹
  let u : Γ → Rˣ := fun g => ⟨y g, y g⁻¹, hinv g, hinv' g⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun g => hy g⟩
  · ext
    apply hφ
    simp [u, hy]
  · intro g h
    ext
    apply hφ
    simp [u, hy]

theorem exists_cyclotomicChar_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ (W.s = 1 → Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) := by
  intro l _ P K LL n W
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨h, rfl⟩ := W.resΓ_onto g
    have hmem : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ h : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res h]
      exact (W.χΓ (W.resΓ h) : ↥(OL LL)).2
    obtain ⟨y, hy⟩ := exists_padicInt_of_mem_OL LL _ hmem
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res h]
    rfl
  obtain ⟨χ, hχ⟩ := exists_units_hom_lift (algebraMap ℤ_[l] ↥(OL LL))
    (algebraMap_padicInt_OL_injective LL) W.χΓ hex
  refine ⟨χ, hχ, fun hs => ?_⟩
  apply associated_of_v_sub_one P LL _ _ (hχ W.gam)
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  exact hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBounded
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc.PosCount

section Idem

variable {ι : Type} [Fintype ι] {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem sum_smul_mul_idem {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (i : ι) (x : A) :
    (∑ j, c j • e j) * (e i * x) = c i • (e i * x) := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, ← mul_assoc, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_assoc, ← mul_assoc, he.ortho hj, zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_smul_mul {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (x : A) :
    (∑ j, c j • e j) * x = ∑ i, c i • (e i * x) := by
  calc (∑ j, c j • e j) * x = (∑ j, c j • e j) * (∑ i, e i * x) := by
        rw [← Finset.sum_mul, he.complete, one_mul]
    _ = ∑ i, (∑ j, c j • e j) * (e i * x) := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun i _ => sum_smul_mul_idem he c i x

theorem sum_smul_mul_cancel {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c c' : ι → R)
    (h : ∀ i, c' i * c i = 1) (x : A) : (∑ j, c' j • e j) * ((∑ j, c j • e j) * x) = x := by
  rw [sum_smul_mul he c x, Finset.mul_sum]
  calc ∑ i, (∑ j, c' j • e j) * (c i • (e i * x)) = ∑ i, e i * x :=
        Finset.sum_congr rfl fun i _ => by
          rw [mul_smul_comm, sum_smul_mul_idem he, smul_smul, mul_comm, h, one_smul]
    _ = x := by rw [← Finset.sum_mul, he.complete, one_mul]

end Idem

variable (K : UQ) (B : InvAlg K)

def Sandwich (a : K.O) (N : ℕ) : Set (Submodule K.O B.A) :=
  {M | (∀ r : B.A, IsIntegral K.O r → a ^ N • r ∈ M) ∧ ∀ m ∈ M, IsIntegral K.O m}

theorem finite_quotient_span_pow {a : K.O} (ha : a ≠ 0) (N : ℕ) :
    Finite (K.O ⧸ Ideal.span {a ^ N}) := by
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k * N, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton, mul_pow,
    ← Units.val_pow_eq_pow_val, Units.mul_left_dvd, ← pow_mul]

theorem sandwich_finite (hR : (Subalgebra.toSubmodule (integralClosure K.O B.A)).FG) {a : K.O} (ha : a ≠ 0)
    (N : ℕ) : (Sandwich K B a N).Finite := by
  set R := Subalgebra.toSubmodule (integralClosure K.O B.A) with hRdef
  haveI : Module.Finite K.O R := Module.Finite.iff_fg.mpr hR
  set I : Ideal K.O := Ideal.span {a ^ N}
  haveI := finite_quotient_span_pow K ha N
  set P : Submodule K.O R := I • (⊤ : Submodule K.O R)
  haveI : Module.Finite (K.O ⧸ I) (R ⧸ P) := Module.Finite.of_restrictScalars_finite K.O _ _
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (K.O ⧸ I)
  haveI : Finite (Submodule K.O (R ⧸ P)) :=
    Finite.of_injective (fun Q : Submodule K.O (R ⧸ P) => (Q : Set (R ⧸ P))) SetLike.coe_injective
  let Φ : Submodule K.O B.A → Submodule K.O (R ⧸ P) := fun M => (M.comap R.subtype).map P.mkQ
  have key : ∀ M ∈ Sandwich K B a N, M = ((Φ M).comap P.mkQ).map R.subtype := by
    intro M hM
    have hP : P ≤ M.comap R.subtype := by
      refine Submodule.smul_le.2 fun r hr n _ => ?_
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul]
      exact M.smul_mem b (hM.1 _ n.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 hP, Submodule.map_comap_subtype,
      inf_eq_right.2 fun m hm => hM.2 m hm]
  have hinj : Set.InjOn Φ (Sandwich K B a N) := by
    intro M₁ h₁ M₂ h₂ h
    rw [key M₁ h₁, key M₂ h₂, h]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

theorem card_pos_le : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O),
    B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ,
    {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  intro K B ι _ e π S a hP ha hF N
  have he : CompleteOrthogonalIdempotents e := hF.1.1
  haveI : Algebra.Etale K.E B.A := GlobalTheory.etale_of_separable_charpoly_mulLeft K.E B.A B.g hP
  have hR := GlobalTheory.IntegralClosureFG.integralClosure_fg K.O K.E B.A
  have hfin := sandwich_finite K B hR ha.1 N
  refine ⟨(Sandwich K B a N).ncard, fun p => ?_⟩
  have hal : al K a ≠ 0 := by
    simpa using (IsFractionRing.injective K.O K.E).ne ha.1
  set t : B.A := ∑ j, (al K a ^ (-p j)) • e j with ht
  set t' : B.A := ∑ j, (al K a ^ (p j)) • e j with ht'
  have hcancel : ∀ x : B.A, t' * (t * x) = x := fun x =>
    sum_smul_mul_cancel he (fun j => al K a ^ (-p j)) (fun j => al K a ^ (p j))
      (fun i => by rw [← zpow_add₀ hal, add_neg_cancel, zpow_zero]) x
  have hmaps : ∀ M ∈ {M : Submodule K.O B.A | Pos B a e N M p}, mulLat K.O t M ∈ Sandwich K B a N := by
    intro M hM
    refine ⟨fun r hr => ?_, fun m hm => ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, (al K a ^ (p i + N)) • (e i * r),
        Submodule.sum_mem _ fun i _ => (hM i).1 r hr, ?_⟩
      rw [LinearMap.mulLeft_apply, Finset.mul_sum]
      calc ∑ i, t * (al K a ^ (p i + N) • (e i * r)) = ∑ i, (al K a ^ N) • (e i * r) :=
            Finset.sum_congr rfl fun i _ => by
              rw [mul_smul_comm, ht, sum_smul_mul_idem he, smul_smul, ← zpow_add₀ hal,
                show p i + N + -p i = (N : ℤ) by ring, zpow_natCast]
        _ = a ^ N • r := by
            rw [← Finset.smul_sum, ← Finset.sum_mul, he.complete, one_mul, ← map_pow, algebraMap_smul]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hm
      rw [LinearMap.mulLeft_apply, ht, sum_smul_mul he]
      exact IsIntegral.sum _ fun i _ => (hM i).2 y hy
  have hinj : Set.InjOn (mulLat K.O t) {M : Submodule K.O B.A | Pos B a e N M p} := by
    intro M₁ _ M₂ _ h
    have hid : (LinearMap.mulLeft K.O t').comp (LinearMap.mulLeft K.O t) = LinearMap.id :=
      LinearMap.ext fun x => hcancel x
    have h' := congrArg (Submodule.map (LinearMap.mulLeft K.O t')) h
    simp only [mulLat, ← Submodule.map_comp, hid, Submodule.map_id] at h'
    exact h'
  exact ⟨Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 hmaps)) hinj,
    Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin⟩

end GlobalTheory.UnitLemma.Desc.PosCount
end
end

