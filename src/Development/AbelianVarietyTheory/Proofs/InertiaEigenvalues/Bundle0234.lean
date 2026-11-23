module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0186
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicBasisGaloisLatticeSameMatrices
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  have hsm : ∀ (c : R) (v : V), c • v = algebraMap R F c • v := fun _ _ => rfl
  haveI : IsScalarTower R F V := ⟨fun c a v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let f' : N →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) f' :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        have : ⇑(algebraMap R (Module.End R V) s) = fun v => algebraMap R F s • v := by
          ext v; rfl
        rw [this]
        exact (MulAction.toPerm (Units.mk0 _ h0) : Equiv.Perm V).bijective
      surj := fun v => by
        obtain ⟨c, hc, x, hx⟩ := hfull v
        exact ⟨(x, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hx⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b.ofIsLocalizedModule F (nonZeroDivisors R) f',
    fun j => b.ofIsLocalizedModule_apply F _ f' j,
    fun x i => b.ofIsLocalizedModule_repr_apply F _ f' x i⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)


include hφ in
omit [IsDomain R] in
theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]


include hφ hint in
theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3


include hφ hint in
theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemOL
section
namespace GlobalTheory.IntegerRingPowers

open Formalism.BasicNotions

theorem exists_pow_smul_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (a : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * a ∈ Loc.OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hint : IsIntegral ℚ_[l] a := IsIntegral.of_finite ℚ_[l] a
  obtain ⟨⟨m, hm⟩, hmi⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ_[l]) a hint
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.valuation, ?_⟩
  rw [Loc.OL, mem_integralClosure_iff]
  have hmi' : IsIntegral ℤ_[l] (m • a) := hmi
  have e := PadicInt.unitCoeff_spec hm0
  set u := PadicInt.unitCoeff hm0
  have key : (l : ↥LL.1) ^ m.valuation * a = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (m • a) := by
    conv_rhs => rw [e]
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast]
  rw [key]
  exact IsIntegral.smul _ hmi'

theorem smul_mem_of_mem_OL {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) {c : ↥LL.1} (hc : c ∈ Loc.OL LL)
    {w : T.V} (hw : w ∈ T.L.T) : c • w ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(Loc.OL LL)) hw
  have e := T.towO.smul_assoc (⟨c, hc⟩ : ↥(Loc.OL LL)) (1 : ↥LL.1) w
  have e2 : ((⟨c, hc⟩ : ↥(Loc.OL LL)) • (1 : ↥LL.1)) = c := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e2, one_smul] at e
  rw [e]; exact h

theorem natCast_pow_mem_OL {l : ℕ} [Fact (Nat.Prime l)] (LL : Loc.FinExt l) (k : ℕ) :
    (l : ↥LL.1) ^ k ∈ Loc.OL LL :=
  (Loc.OL LL).pow_mem ((Loc.OL LL).natCast_mem l) k

theorem pow_smul_smul_eq {l : ℕ} [Fact (Nat.Prime l)] {K LL : Loc.FinExt l}
    (T : LocLat ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)) (a : ↥LL.1) (x : T.V) (k n : ℕ) :
    (l : ↥LL.1) ^ (k + n) • a • x = ((l : ↥LL.1) ^ k * a) • ((l : ↥LL.1) ^ n • x) := by
  rw [pow_add, mul_smul, mul_smul]
  congr 1
  rw [← mul_smul, ← mul_smul, mul_comm]

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (K LL : Formalism.BasicNotions.Loc.FinExt l)
    (T : Formalism.BasicNotions.LocLat ↥(Formalism.BasicNotions.Loc.GK K) ℚ_[l]
      ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l)) ↥(Formalism.BasicNotions.Loc.OL LL))
    (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈
      Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ K LL T v
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := hy
    refine ⟨n + k, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL k) hn
    · rw [pow_add, mul_smul]
      exact smul_mem_of_mem_OL T (natCast_pow_mem_OL LL n) hk
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_smul_mem_OL LL a
    refine ⟨k + n, ?_⟩
    rw [pow_smul_smul_eq T a x k n]
    exact smul_mem_of_mem_OL T hk hn

end GlobalTheory.IntegerRingPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory.CyclotomicPrimes

theorem summable_subset_union_finite {ι : Type} (f : ι → ℝ) (A B C : Set ι) (hB : B.Finite) (h : C ⊆ A ∪ B)
    (hA : Summable fun x : A => f x) : Summable fun x : C => f x := by
  have h1 : Summable (f ∘ ((↑) : ↥(A ∪ B) → ι)) := by
    rw [← Set.union_sdiff_self]
    exact (HasSum.add_disjoint Set.disjoint_sdiff_right hA.hasSum ((hB.subset Set.sdiff_subset).summable f).hasSum).summable
  exact h1.comp_injective (i := Set.inclusion h) (Set.inclusion_injective h)

theorem exists_prime_absNorm_eq_of_irreducible_cyclotomic : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  classical
  intro K _ _ m hm hirr τ S hS
  have : Fact m.Prime := ⟨hm⟩
  let cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ := fun P =>
    if h : ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = 0 then 1 else Units.mk0 _ h
  have hcl : ∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) := by
    intro P hP
    simp only [cl]
    rw [dite_eq_right (by rwa [ZMod.natCast_eq_zero_iff])]
    rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨Z, hZ, hZ1, hZs⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero K
  refine GlobalTheory.Mem.RayPrimes.not_summable_class (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
    GlobalTheory.Mem.RayPrimes.two_le_absNorm cl
    (fun s hs => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow K).2 s hs).2) ?_ Z hZ.continuous hZ1 ?_ τ ?_
  · intro χ hχ
    obtain ⟨P, u, hu, hχu⟩ := _root_.GlobalTheory.NormChar.exists_prime_norm_char_ne_one K m hm hirr χ hχ
    have hP : ¬ m ∣ Ideal.absNorm P.asIdeal := by
      rw [← ZMod.natCast_eq_zero_iff, ← hu]; exact u.ne_zero
    refine _root_.GlobalTheory.NormCharL.exists_continuous_ne_zero_one K m hm χ cl hcl ⟨P, hP, ?_⟩
    rwa [show cl P = u from Units.ext ((hcl P hP).trans hu.symm)]
  · intro s hs
    simpa using hZs s (by simpa using hs)
  · have hfin : (S ∪ {P : HeightOneSpectrum (𝓞 K) | Ideal.absNorm P.asIdeal ≤ m}).Finite :=
      hS.union ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 K) m).preimage
        (f := fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h))
    refine summable_subset_union_finite (fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹)
      {P | ¬ (Ideal.absNorm P.asIdeal).Prime} _ {P | cl P = τ} hfin ?_ (_root_.GlobalTheory.summable_inv_absNorm_of_not_prime K)
    intro P hP
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_not] at hn hP
    have hd : ¬ m ∣ Ideal.absNorm P.asIdeal := fun h =>
      hn.2.2.ne ((Nat.prime_dvd_prime_iff_eq hm hn.1).1 h)
    exact hcon P hn.2.1 hn.1 (by rw [← hcl P hd, hP])

end GlobalTheory.CyclotomicPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio
section
open GlobalTheory.PMon.Gauss

open scoped Formalism.Per

namespace GlobalTheory.TiltRootApprox

open _root_.Ideal

variable {l : ℕ} [Fact l.Prime]

theorem pow_pow_add_mul {M : Type*} [Monoid M] {ξ : M} {o : ℕ} (h : ξ ^ (l ^ o) = ξ) (a k : ℕ) :
    ξ ^ (l ^ (a + o * k)) = ξ ^ (l ^ a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + o * (k + 1) = (a + o * k) + o by ring, pow_add, mul_comm, pow_mul, h, ih]

theorem exists_pow_pow_eq {M : Type*} [Monoid M] {ξ : M} {n : ℕ} (hn : 0 < n) (hl : ¬ l ∣ n)
    (h : ξ ^ n = 1) : ∃ o : ℕ, 0 < o ∧ ξ ^ (l ^ o) = ξ := by
  have hcop : l.Coprime n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hl
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : l ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  rw [← Nat.div_add_mod (l ^ n.totient) n, hmod, pow_add, pow_mul, h, one_pow, one_mul]
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have : n = 1 := by omega
    subst this
    simp only [pow_one] at h
    simp [h]

theorem exists_tilt_lift (ξ : Formalism.Per.OC l) {o : ℕ} (ho : 0 < o) (hξ : ξ ^ (l ^ o) = ξ) :
    ∃ ζ : Formalism.Per.Fl l, ζ ^ (l ^ o) = ζ ∧ ζ.untilt = ξ := by
  obtain ⟨q, rfl⟩ : ∃ q, o = q + 1 := ⟨o - 1, by omega⟩
  have hper := pow_pow_add_mul (l := l) hξ
  let s : ℕ → ModP (Formalism.Per.OC l) l := fun m =>
    Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (ξ ^ (l ^ (q * m)))
  have hs : ∀ m, s (m + 1) ^ l = s m := by
    intro m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_succ, show q * (m + 1) + 1 = q * m + (q + 1) * 1 by ring, hper]
  let ζ : Formalism.Per.Fl l := ⟨s, hs⟩
  refine ⟨ζ, ?_, ?_⟩
  · refine Perfection.ext fun m => ?_
    erw [map_pow]
    change s m ^ l ^ (q + 1) = s m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_add, show q * m + (q + 1) = q * m + (q + 1) * 1 by ring, hper]
  · refine Perfection.teichmuller_spec (I := span {((l : ℕ) : Formalism.Per.OC l)}) fun n => ?_
    refine ⟨ξ ^ (l ^ (q * n)), rfl, ?_⟩
    rw [← pow_mul, ← pow_add, show q * n + n = 0 + (q + 1) * n by ring, hper, pow_zero, pow_one]

end GlobalTheory.TiltRootApprox

namespace GlobalTheory.TiltRootApprox

open _root_.Ideal

theorem exists_root_approx : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 →
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧
      ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ <
        ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  intro l _ y y' hy' hn
  have h0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
    hy' (GlobalTheory.TiltAbs.eq_zero_of_untilt y' (Subtype.ext h))
  have hpos : 0 < ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_pos_iff.2 h0
  have hd : y'.untilt ∣ y.untilt := by
    refine ⟨⟨((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]),
      (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, hn, div_self hpos.ne']
    · change _ = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) * (_ / _)
      field_simp
  obtain ⟨u, rfl⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd hd
  have hmul : ∀ a b : Formalism.Per.Fl l, (((a * b).untilt : Formalism.Per.OC l) : ℂ_[l]) =
      ((a.untilt : Formalism.Per.OC l) : ℂ_[l]) * ((b.untilt : Formalism.Per.OC l) : ℂ_[l]) := by
    intro a b
    rw [map_mul]
    rfl
  have hu : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
    rw [hmul, norm_mul] at hn
    have := hn
    field_simp at this
    nlinarith [this]
  obtain ⟨ξ, hξ, hclose⟩ := ReciprocityTheory.ChartRestriction.L1.res_full l _ hu.le
  have hξn : ‖ξ‖ ≤ 1 := by
    calc ‖ξ‖ = ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ)‖ := by
          rw [sub_sub_cancel]
      _ ≤ max ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ‖ := by
          have := IsUltrametricDist.norm_add_le_max (((u.untilt : Formalism.Per.OC l) : ℂ_[l]))
            (-(((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ))
          rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hu.le hclose.le
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [sub_zero, hu] at hclose
    exact lt_irrefl _ hclose
  obtain ⟨n, hn0, hln, hξpow⟩ : ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ξ ^ n = 1 := by
    rcases Set.mem_insert_iff.1 hξ with h | h
    · exact absurd h hξ0
    · exact h
  obtain ⟨o, ho, hξo⟩ := exists_pow_pow_eq hn0 hln hξpow
  let ξ' : Formalism.Per.OC l := ⟨ξ, (GlobalTheory.RingBasics.mem_OC _).2 hξn⟩
  have hξ'o : ξ' ^ (l ^ o) = ξ' := Subtype.ext (by
    change ξ ^ (l ^ o) = ξ
    exact hξo)
  obtain ⟨ζ, hζo, hζu⟩ := exists_tilt_lift ξ' ho hξ'o
  refine ⟨ζ, o, ho, hζo, ?_, ?_⟩
  · rintro rfl
    apply hξ0
    have h00 : (0 : Formalism.Per.Fl l).untilt = 0 := Perfection.teichmuller_zero
    rw [h00] at hζu
    have := congrArg Subtype.val hζu
    exact this.symm
  · have e : y' * u - ζ * y' = (u - ζ) * y' := by ring
    rw [e, hmul, norm_mul]
    have hlt : ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ < 1 := by
      have hmk : Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) ((u - ζ).untilt) =
          Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (u.untilt - ζ.untilt) := by
        rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
          PreTilt.mk_untilt_eq_coeff_zero]
      rw [Ideal.Quotient.eq, ← pow_one (span {((l : ℕ) : Formalism.Per.OC l)}),
        GlobalTheory.RingBasics.mem_span_pow_OC, pow_one] at hmk
      have e2 : (((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l]) =
          ((((u - ζ).untilt - (u.untilt - ζ.untilt) : Formalism.Per.OC l)) : ℂ_[l]) +
            (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ) := by
        rw [hζu]
        push_cast
        ring
      rw [e2]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hclose)
      exact lt_of_le_of_lt hmk GlobalTheory.RingBasics.norm_p_lt
    calc ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖
        < 1 * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := mul_lt_mul_of_pos_right hlt hpos
      _ = _ := one_mul _

end GlobalTheory.TiltRootApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTmulOneOfFrobFixedOfMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem equivFinsuppOfBasisLeft_lTensor_apply {F : Type} [Field F] {V M N : Type}
    [AddCommGroup V] [Module F V] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    {ι : Type} [DecidableEq ι] (b : Module.Basis ι F V) (f : M →ₗ[F] N) (x : V ⊗[F] M) (i : ι) :
    equivFinsuppOfBasisLeft b (f.lTensor V x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem algebraTensorModule_map_id_apply {F L : Type} [Field F] [Field L] [Algebra F L]
    {V M N : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (x : V ⊗[F] M) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) f x = f.lTensor V x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v m => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exists_tmul_one_of_frob_fixed_of_mem_fil_zero :
    ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (x : V ⊗[Qp] B), φVB PD (LL := LL) (V := V) x = x → ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[Qp] (1 : B) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ x hφ hF
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  have key : ∀ i, ∃ c : Qp, algebraMap Qp B c = equivFinsuppOfBasisLeft b x i := by
    intro i
    apply PD.fund
    · have h := equivFinsuppOfBasisLeft_lTensor_apply b PD.φ.toLinearMap x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h2 : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) PD.φ.toLinearMap x = x := hφ
      rw [h2] at h
      exact h.symm
    · obtain ⟨y, hy⟩ := hF
      have h := equivFinsuppOfBasisLeft_lTensor_apply b
        (PD.ι.toLinearMap.restrictScalars Qp) x i
      rw [← algebraTensorModule_map_id_apply (L := LL)] at h
      have h' := equivFinsuppOfBasisLeft_lTensor_apply b
        ((PD.Fil 0).restrictScalars Qp).subtype y i
      rw [← algebraTensorModule_map_id_apply (L := LL), hy] at h'
      have h3 : PD.ι (equivFinsuppOfBasisLeft b x i)
          = ((PD.Fil 0).restrictScalars Qp).subtype (equivFinsuppOfBasisLeft b y i) :=
        h.symm.trans h'
      rw [h3]
      exact (equivFinsuppOfBasisLeft b y i).2
  choose c hc using key
  refine ⟨∑ i ∈ (equivFinsuppOfBasisLeft b x).support, c i • b i, ?_⟩
  have hx : x = (equivFinsuppOfBasisLeft b).symm (equivFinsuppOfBasisLeft b x) := by simp
  rw [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] at hx
  rw [TensorProduct.sum_tmul]
  refine hx.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hc i, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end GlobalTheory
end

