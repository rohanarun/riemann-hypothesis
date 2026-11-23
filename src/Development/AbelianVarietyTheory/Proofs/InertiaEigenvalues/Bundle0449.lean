module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
section
noncomputable section

namespace GlobalTheory.DeRhamSplit

open _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finrank_split [inst : Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = Module.finrank Qp K)
    (ρ : Representation LL G V) [Module.Finite LL (DdR PD ρ)] :
    Module.finrank LL (DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (DdRE PD ρ τ) ∧
      ∀ a : ℤ, Module.finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
        ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (FildR PD ρ τ a) := by
  haveI := PD.finK
  obtain rfl : inst = minpoly.AlgHom.fintype Qp K LL := Subsingleton.elim _ _
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hst : ∀ c, ∀ x ∈ DdR PD ρ, m c x ∈ DdR PD ρ := fun c x hx =>
    (hD _).2 fun g => by rw [hc, (hD x).1 hx g]
  have hF : ∀ a c, ∀ x ∈ FilV PD (LL := LL) (V := V) a, m c x ∈ FilV PD (LL := LL) (V := V) a := by
    rintro a c _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      refine ⟨v ⊗ₜ ⟨c • (b : BdR), (PD.Fil a).smul_mem c b.2⟩, ?_⟩
      change v ⊗ₜ (c • (b : BdR)) = v ⊗ₜ (algebraMap K BdR c * (b : BdR))
      rw [Algebra.smul_def]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
  have hE : ∀ (τ : K →ₐ[Qp] LL) x, x ∈ DdRE PD ρ τ ↔ x ∈ DdR PD ρ ∧ ∀ c, m c x = τ c • x := fun τ x => by
    simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  refine ⟨GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ) hst (DdRE PD ρ) hE, fun a => ?_⟩
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (FildR PD ρ τ a) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  refine GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨hst c x hx.1, hF a c x hx.2⟩)
    (fun τ => FildR PD ρ τ a) fun τ x => ?_
  simp only [FildR, Submodule.mem_inf, hE]
  tauto

end General

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), Module.Finite ↥LL.1 ↥(DdR (P.PD K) ρ) → Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ ∀ a : ℤ, Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  intro l _ P K LL _ hs V _ _ _ _ ρ hfin
  exact finrank_split (P.PD K) hs.2 ρ

end GlobalTheory.DeRhamSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfInertiaFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.RegularDense

theorem fixed_of_inertia_frobenius : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l),
    (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) →
    ∀ y : ℂ_[l], (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σC g y = y) → Per.σC F y = y →
      ∀ g : GQ l, Per.σC g y = y := by
  intro l hl F hF y hI hFy g
  let H : Subgroup (GQ l) :=
    { carrier := {h | Per.σC h y = y}
      mul_mem' := fun {a b} ha hb => by
        show Per.σC (a * b) y = y
        have ha' : Per.σC a y = y := ha
        have hb' : Per.σC b y = y := hb
        rw [GlobalTheory.RingBasics.σC_mul, hb', ha']
      one_mem' := by
        show Per.σC 1 y = y
        rw [GlobalTheory.RingBasics.σC_one]
      inv_mem' := fun {a} ha => by
        show Per.σC a⁻¹ y = y
        have ha' : Per.σC a y = y := ha
        conv_lhs => rw [← ha']
        rw [← GlobalTheory.RingBasics.σC_mul, inv_mul_cancel, GlobalTheory.RingBasics.σC_one] }
  have hy := ax_sen_tate l H y (fun h hh => hh)
  have hcont : Continuous (fun z : ℂ_[l] => Per.σC g z) := by
    refine Isometry.continuous (Isometry.of_dist_eq fun a b => ?_)
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have hcl : IsClosed {z : ℂ_[l] | Per.σC g z = z} := isClosed_eq hcont continuous_id
  refine closure_minimal ?_ hcl hy
  rintro _ ⟨z, hz, rfl⟩
  show Per.σC g (z : ℂ_[l]) = z
  rw [GlobalTheory.RingBasics.σC_coe]
  congr 1
  have hzK : z ∈ MaximalUnramifiedExtension l := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
    intro h hh
    exact hz h (hI h hh)
  have hFz : F z = z := hz F hFy
  have hpow : ∀ n : ℕ, (F ^ n) z = z := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hFz, ih]
  obtain ⟨m, hm, hlm, hH⟩ := FrobLaws.exists_level hzK
  have hr : ∀ (n : ℕ) (ζ : Om l), ζ ^ m = 1 → (F ^ n) ζ = ζ ^ (l ^ n) := fun n ζ hζ => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF ζ m hm hlm hζ, ← pow_mul, pow_succ']
  obtain ⟨n, hn⟩ := FrobLaws.gal_root g hm hlm
  rw [hH g (F ^ n) fun ζ hζ => by rw [hn ζ hζ, hr n ζ hζ], hpow]

end GlobalTheory.RegularDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntO

theorem frobenius_integrality_vec_O : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ ι _ _ Y w z h i
  classical
  have key := GlobalTheory.FrobIntegralCoeff.integrality_baseChange (R := ℤ_[l]) (O := O) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) ι Unit
    (Matrix.of fun j (_ : Unit) => z j) Y 1 (Matrix.of fun j (_ : Unit) => w j) (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      refine Matrix.ext fun j u => ?_
      have := congrFun h j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fintype.sum_unique, Pi.add_apply] at this ⊢
      exact this) i ()
  exact key

end GlobalTheory.FrobIntO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorStrat

def idl (K : Type) [Field K] : Ideal K⟦X⟧⟦X⟧ := Ideal.span {C (X : K⟦X⟧), X}

theorem idl_ne_top (K : Type) [Field K] : idl K ≠ ⊤ := by
  intro h
  have hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧)) := by
    rw [idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp
  have h1 := hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)
  simp at h1

theorem eq_zero_of_forall_mem {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : ∀ m, g ∈ idl K ^ m) : g = 0 := by
  have := Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact h

theorem mem_idl_of_constantCoeff {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : constantCoeff g = 0) :
    g ∈ idl K := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.2 h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))

theorem taylor_eq_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
    (f : K⟦X⟧) (hf : PowerSeries.derivative (R := K) f = 0) : sh f = C f := by
  ext1 i
  rcases i with _ | i
  · simpa using hsh f 0
  · have h := hsh f (i + 1)
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 1).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [coeff_C, ite_eq_right (by omega)]
    exact (mul_eq_zero.1 h).resolve_left hne

theorem taylor_X {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) :
    sh X = C X + X := by
  ext1 i
  rcases i with _ | _ | i
  · simpa using hsh X 0
  · simpa using hsh X 1
  · have h := hsh X (i + 2)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero,
      Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 2).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [map_add (f := _), coeff_C, coeff_X, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    exact (mul_eq_zero.1 h).resolve_left hne

end GlobalTheory.TaylorStrat

namespace GlobalTheory.TaylorStrat

theorem map_idl_pow_le {K : Type} [Field K] (l : ℕ) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hshX : sh X = C X + X) (hC : φ₂ (C X) = C X ^ l) (hsh : φ₂ (sh X) = sh X ^ l)
    (m : ℕ) {g : K⟦X⟧⟦X⟧} (hg : g ∈ idl K ^ m) : φ₂ g ∈ idl K ^ (l * m) := by
  have hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have h1 : (idl K).map φ₂ ≤ idl K ^ l := by
    rw [Ideal.map_le_iff_le_comap, idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]
    · rw [hC]
      exact Ideal.pow_mem_pow hCm l
    · have hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l :=
        (congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans
          (by rw [map_sub, hsh, hC, hshX])
      rw [hφX]
      exact sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)
  have h2 := Ideal.mem_map_of_mem φ₂ hg
  rw [Ideal.map_pow] at h2
  rw [pow_mul]
  exact Ideal.pow_right_mono h1 m h2

theorem mul_mul_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] (J : Ideal R) (A N B : Matrix ι ι R)
    (hN : ∀ i j, N i j ∈ J) (i j : ι) : (A * N * B) i j ∈ J := by
  rw [Matrix.mul_apply]
  refine J.sum_mem fun k _ => J.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)

end GlobalTheory.TaylorStrat


open GlobalTheory.TaylorStrat in
theorem GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hshX := taylor_X sh hsh
  have hshC : ∀ c : K, sh (C c) = C (C c) := fun c => taylor_eq_C sh hsh _ (by simp)
  have hcc : ∀ f, constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hCX : φ₂ (C X) = C X ^ l := by rw [hφC, frob_X, map_pow]
  have hshl : φ₂ (sh X) = sh X ^ l := by rw [hφsh, frob_X, map_pow]
  have hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)
  let W : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => (P.xiMat τ)⁻¹ * P.mx τ
  let Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ
  let ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => (Y τ).map C * (W τ).map sh
  have hYW : ∀ τ, Y τ * W τ = 1 := by
    intro τ
    simp only [Y, W]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]
  have h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1 := by
    intro τ
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hYW τ) i) j
    simpa [ε₀, Matrix.mul_apply, hcc] using this
  have hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh =
      ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂ := by
    intro τ
    have F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφC]
    have F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφsh]
    have F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) =
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) := by
      intro M; ext1 p q; simp [hshC]
    have hM := P.mx_mul_xiMat τ
    rw [← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply] at hM
    have hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1 := by
      rw [← map_mul, hXi, map_one]
    have hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
      calc W τ = (P.xiMat τ)⁻¹ * (P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1))) *
            (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]
        _ = _ := by
          rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]
    have hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) *
        (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
      have h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) *
          (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
        rw [hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]
      show P.mxInv τ * P.xiMat τ = _
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]
    simp only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]
    rw [hW, hY]
    simp only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]
    rw [F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul,
      ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul,
      ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]
    have hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) *
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1 := by
      rw [← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]
    rw [hc, Matrix.one_mul]
  have hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1 := by
    intro τ
    rw [← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ *
      ((P.mxInv (τ - 1)).map (frob K l)).map sh := by
    intro τ
    have h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh =
        ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ := by
      rw [Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]
    calc ε τ - ε₀ τ = (ε τ - ε₀ τ) * (((P.mx (τ - 1)).map (frob K l)).map sh *
          ((P.mxInv (τ - 1)).map (frob K l)).map sh) := by rw [hinv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1]
  have hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro τ i j
      rw [zero_add, pow_one]
      apply mem_idl_of_constantCoeff
      have h1 := congrFun (congrFun (hε0 τ) i) j
      have h2 := congrFun (congrFun (h00 τ) i) j
      simp only [Matrix.map_apply] at h1 h2
      rw [Matrix.sub_apply, map_sub, h1, h2, sub_self]
    | succ m ih =>
      intro τ i j
      rw [hδ τ]
      apply mul_mul_mem
      intro p q
      rw [Matrix.map_apply]
      exact Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))
  have key : ε τ = ε₀ τ := by
    refine Matrix.ext fun i j => ?_
    exact sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))
  have hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1) := by
    ext1 τ
    rw [P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
    congr 1
    ext1 k
    simp [bas, Pi.single_apply]
  have hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) =
      P.xiExt (fun τ i => (PowerSeries.derivative (R := K))^[n] (w τ i)) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, mul_apply_eq_comp, P.nabla_xiExt, ih]
      rfl
  rw [hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]
  show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) =
    (Y τ *ᵥ fun k => (PowerSeries.derivative (R := K))^[n] ((W τ *ᵥ Pi.single j 1) k)) i
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDecompOfDisjoint
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
namespace GlobalTheory.InertiaEigenvalues

theorem galois_decomp_of_disjoint : ∀ (l : ℕ) [Fact l.Prime] (K M : IntermediateField ℚ_[l] (Om l)), FiniteDimensional ℚ_[l] K → IsGalois ℚ_[l] K → K ⊓ M = ⊥ → ∀ g : GQ l, ∃ h ∈ K.fixingSubgroup, ∃ k ∈ M.fixingSubgroup, g = h * k := by
  intro l _ K M _ _ hKM g
  let r : GQ l →* (K ≃ₐ[ℚ_[l]] K) := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) K
  have hr : ∀ (σ : GQ l) (y : K), ((r σ y : K) : Om l) = σ (y : Om l) := fun σ y =>
    AlgEquiv.restrictNormal_commutes σ K y
  let H : Subgroup (K ≃ₐ[ℚ_[l]] K) := M.fixingSubgroup.map r
  have hfix : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxM : (x : Om l) ∈ M := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro k
      have := hx ⟨r k, Subgroup.mem_map_of_mem r k.2⟩
      have h2 := congrArg (fun z : K => (z : Om l)) this
      change (k : GQ l) (x : Om l) = x
      simpa [hr] using h2
    have hxKM : (x : Om l) ∈ K ⊓ M := ⟨x.2, hxM⟩
    rw [hKM, IntermediateField.mem_bot] at hxKM
    obtain ⟨c, hc⟩ := hxKM
    rw [IntermediateField.mem_bot]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa using hc
  have hH : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfix, IntermediateField.fixingSubgroup_bot]
  have hg : r g ∈ H := by rw [hH]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
  refine ⟨g * k⁻¹, ?_, k, hk, by group⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : r (g * k⁻¹) = 1 := by rw [map_mul, map_inv, ← hkg, mul_inv_cancel]
  have := hr (g * k⁻¹) ⟨x, hx⟩
  rw [h1] at this
  simpa using this.symm

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeSubMemPowSmulEventually
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open scoped Pointwise

namespace GlobalTheory.BKGal.ContNear

theorem sub_mem_pow_smul_lattice_eventually :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (t : T.V), t ∈ T.L.T → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : ↥LL.1) ^ m) • t' := by
  intro l _ LL T t _ m
  have hO := GlobalTheory.HTW.Rec.goodO_finExt_integers l LL
  have hT : IsOpen (T.L.T : Set T.V) := GlobalTheory.Cyc.locLat_isOpen hO T
  have hc : ((l : ↥LL.1) ^ m) ≠ 0 := by
    refine pow_ne_zero _ ?_
    have h1 : (l : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by simp
    rw [h1, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hU : IsOpen (((l : ↥LL.1) ^ m) • (T.L.T : Set T.V)) := hT.smul₀ hc
  haveI := hO.2.2.2.1
  haveI := IsModuleTopology.topologicalAddGroup (↥LL.1) T.V
  have hf : Continuous fun g : Gl l => T.ρ g t - t := (T.cont t).sub continuous_const
  have h0 : (fun g : Gl l => T.ρ g t - t) 1 ∈ ((l : ↥LL.1) ^ m) • (T.L.T : Set T.V) := by
    simp only [map_one, Module.End.one_apply, sub_self]
    exact ⟨0, T.L.T.zero_mem, smul_zero _⟩
  filter_upwards [hf.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with g hg
  obtain ⟨t', ht', he⟩ := hg
  exact ⟨t', ht', he.symm⟩

end GlobalTheory.BKGal.ContNear
end

