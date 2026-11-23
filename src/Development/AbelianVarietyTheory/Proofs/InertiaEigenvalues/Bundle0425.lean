module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import GroundTheory.LocalFields.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import GroundTheory.LocalFields.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReading
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.NormalSeparable

section SlopeTestRemainingChoices
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem aeval_mem (U : Submodule ℂ H) (S : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, Polynomial.aeval S q u ∈ U := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simpa [Module.algebraMap_end_apply] using U.smul_mem a hu
  · intro p r hp hr u hu
    simpa using U.add_mem (hp u hu) (hr u hu)
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS u hu)

theorem aeval_adj (U : Submodule ℂ H) (S S' : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (S u) v = inner ℂ u (S' v)) (hS' : ∀ u ∈ U, S' u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (Polynomial.aeval S q u) v
      = inner ℂ u (Polynomial.aeval S' (q.map (starRingEnd ℂ)) v) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu v hv
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  · intro p r hp hr u hu v hv
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, inner_add_left, inner_add_right,
      hp u hu v hv, hr u hu v hv]
  · intro n a ih u hu v hv
    have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial ℂ)
        = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e]
    generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
    have e2 : (p * Polynomial.X).map (starRingEnd ℂ) = Polynomial.X * p.map (starRingEnd ℂ) := by
      rw [Polynomial.map_mul, Polynomial.map_X, mul_comm]
    rw [e2, map_mul, Polynomial.aeval_X, Module.End.mul_apply, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, ih _ (hS u hu) v hv]
    exact hadj u hu _ (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _ v hv)

theorem aeval_comm (U : Submodule ℂ H) (S B : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hc : ∀ u ∈ U, S (B u) = B (S u)) (q : Polynomial ℂ) :
    ∀ u ∈ U, Polynomial.aeval S q (B u) = B (Polynomial.aeval S q u) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simp [Module.algebraMap_end_apply]
  · intro p r hp hr u hu
    simp only [map_add (f := _), LinearMap.add_apply, hp u hu, hr u hu]
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    simp only [Module.End.mul_apply]
    rw [hc u hu, ih _ (hS u hu)]

theorem normal_sq_zero (U : Submodule ℂ H) (A A' : Module.End ℂ H) (hA : ∀ u ∈ U, A u ∈ U)
    (hA' : ∀ u ∈ U, A' u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (A u) v = inner ℂ u (A' v))
    (hc : ∀ u ∈ U, A (A' u) = A' (A u)) (u : H) (hu : u ∈ U) (h : A (A u) = 0) : A u = 0 := by
  have hw : A u ∈ U := hA u hu
  have h1 : A' (A u) = 0 := by
    have h2 : inner ℂ (A' (A u)) (A' (A u)) = 0 := by
      rw [← hadj _ (hA' _ hw) _ hw, hc _ hw, h, map_zero, inner_zero_left]
    exact inner_self_eq_zero.mp h2
  have h3 : inner ℂ (A u) (A u) = 0 := by
    rw [hadj _ hu _ hw, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h3

end SlopeTestRemainingChoices

theorem minpoly_separable_of_normal : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  intro K V H _ _ _ _ _ _ φ j T S S' hlin hT hS' hadj hc
  haveI : CharZero K := φ.charZero
  set U : Submodule ℂ H := Submodule.span ℂ (Set.range j) with hU
  have hjU : ∀ x, j x ∈ U := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hSU : ∀ u ∈ U, S u ∈ U := by
    have hle : U ≤ U.comap S := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hT x]
      exact Submodule.subset_span ⟨T x, rfl⟩
    intro u hu
    exact hle hu
  have hinj : ∀ v : V, j v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have hli : LinearIndependent K (fun _ : Fin 1 => v) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [Fin.sum_univ_one] at hg
      exact (smul_eq_zero.mp hg).resolve_right hne
    have h1 := hlin 1 (fun _ => v) hli
    exact h1.ne_zero 0 (by simpa using hv)
  have htr : ∀ (p : Polynomial K) (x : V),
      j (Polynomial.aeval T p x) = Polynomial.aeval S (p.map φ) (j x) := by
    intro p
    refine Polynomial.induction_on p ?_ ?_ ?_
    · intro a x
      simp [Module.algebraMap_end_apply]
    · intro p r hp hr x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hr]
    · intro n a ih x
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e]
      generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
      rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, Polynomial.map_mul,
        Polynomial.map_X, map_mul, Polynomial.aeval_X, Module.End.mul_apply, hT]
  have hsq : Squarefree (minpoly K T) := by
    intro q hq
    obtain ⟨r, hr⟩ := hq
    have hp0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hann : Polynomial.aeval T (q * r) = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.zero_apply]
      apply hinj
      have e1 : Polynomial.aeval T (q * r) x = Polynomial.aeval T q (Polynomial.aeval T r x) := by
        rw [map_mul, Module.End.mul_apply]
      rw [e1, htr]
      have h0 : Polynomial.aeval T q (Polynomial.aeval T q (Polynomial.aeval T r x)) = 0 := by
        have h4 : Polynomial.aeval T (q * q * r) x = 0 := by
          rw [← hr, minpoly.aeval, LinearMap.zero_apply]
        simpa only [map_mul, Module.End.mul_apply] using h4
      have h0' : Polynomial.aeval S (q.map φ)
          (Polynomial.aeval S (q.map φ) (j (Polynomial.aeval T r x))) = 0 := by
        rw [← htr, ← htr, h0, map_zero]
      have hcomm1 : ∀ u ∈ U, Polynomial.aeval S (q.map φ) (S' u)
          = S' (Polynomial.aeval S (q.map φ) u) :=
        GlobalTheory.NormalSeparable.aeval_comm U S S' hSU hc (q.map φ)
      have hcomm2 := GlobalTheory.NormalSeparable.aeval_comm U S' (Polynomial.aeval S (q.map φ)) hS'
        (fun u hu => (hcomm1 u hu).symm) ((q.map φ).map (starRingEnd ℂ))
      exact GlobalTheory.NormalSeparable.normal_sq_zero U (Polynomial.aeval S (q.map φ))
        (Polynomial.aeval S' ((q.map φ).map (starRingEnd ℂ)))
        (GlobalTheory.NormalSeparable.aeval_mem U S hSU _) (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _)
        (GlobalTheory.NormalSeparable.aeval_adj U S S' hSU hadj hS' _) (fun u hu => (hcomm2 u hu).symm)
        (j (Polynomial.aeval T r x)) (hjU _) h0'
    have hdvd : minpoly K T ∣ q * r := minpoly.dvd K T hann
    rw [hr] at hdvd
    have hqr : q * r ≠ 0 := by
      intro h
      apply hp0
      rw [hr, mul_assoc, h, mul_zero]
    have h5 : q * (q * r) ∣ 1 * (q * r) := by rwa [one_mul, ← mul_assoc]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hqr).mp h5)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory.NormalSeparable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulLtFinrankCyclotomicAtQAndD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CycDegRam

open _root_.Formalism Formalism.BasicNotions NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid

theorem sub_one_le_two_mul_finrank (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2) :
    l - 1 ≤ 2 * Module.finrank E (CyclotomicField l E) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  set L := CyclotomicField l E
  set k := Module.finrank E L with hk
  have hkpos : 0 < k := Module.finrank_pos
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l E L) l := IsCyclotomicExtension.zeta_spec l E L
  let z : 𝓞 L := ⟨IsCyclotomicExtension.zeta l E L, hζ.isIntegral hl.pos⟩
  have hz : IsPrimitiveRoot z l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hprod : ∏ μ ∈ primitiveRoots l (𝓞 L), (1 - μ) = (l : 𝓞 L) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := l)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz, Polynomial.eval_prod] at h
    simpa using h
  have hassoc : ∀ μ ∈ primitiveRoots l (𝓞 L), Associated (1 - z) (1 - μ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ l := (mem_primitiveRoots hl.pos).1 hμ
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine associated_of_dvd_dvd ?_ ?_
    · rw [← ha]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) z a
    · rw [← hb]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) μ b
  have hA : Associated ((1 - z) ^ (l - 1)) (l : 𝓞 L) := by
    rw [← hprod]
    have := Associated.prod (primitiveRoots l (𝓞 L)) (fun _ => 1 - z) (fun μ => 1 - μ) hassoc
    rwa [Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hl] at this
  set n : 𝓞 E := NumberField.RingOfIntegers.norm E (1 - z)
  have hB : Associated (n ^ (l - 1)) ((l : 𝓞 E) ^ k) := by
    have := hA.map (NumberField.RingOfIntegers.norm E)
    rw [map_pow] at this
    have hl' : (l : 𝓞 L) = algebraMap (𝓞 E) (𝓞 L) (l : 𝓞 E) := (map_natCast _ _).symm
    rw [hl'] at this
    have hn : NumberField.RingOfIntegers.norm E (algebraMap (𝓞 E) (𝓞 L) (l : 𝓞 E)) = (l : 𝓞 E) ^ k := by
      simpa only [hk] using (NumberField.RingOfIntegers.norm_algebraMap (L := L) E (l : 𝓞 E))
    rw [hn] at this
    exact this
  have hI : (Ideal.span {n}) ^ (l - 1) = (Ideal.span {(l : 𝓞 E)}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.2 hB

  have hmaxZ : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlZ : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) := by
      change (l : ℤ) ∈ Ideal.under ℤ _
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast] at h1
    exact hl.ne_zero (by exact_mod_cast h1)
  let v : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, hQ0⟩
  have hv : v ∈ placesOver E l := by
    show (l : 𝓞 E) ∈ Q
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) Q := by
      change (l : ℤ) ∈ Ideal.under ℤ _
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rwa [Ideal.mem_comap, map_natCast] at h1
  have hram2 : Q.ramificationIdx ℤ = 2 := hram v hv
  haveI : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQ.symm⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
  have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) Q (by rw [hmap]; exact hne)
  rw [hram2, hmap] at hc
  have h1 := congrArg (fun I => Multiset.count Q (normalizedFactors I)) hI
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at h1
  rw [← hc] at h1
  rcases Nat.eq_zero_or_pos (Multiset.count Q (normalizedFactors (Ideal.span {n}))) with h0 | hpos
  · rw [h0] at h1; omega
  · calc l - 1 ≤ (l - 1) * Multiset.count Q (normalizedFactors (Ideal.span {n})) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = 2 * k := by rw [h1, mul_comm]

end GlobalTheory.CycDegRam

namespace GlobalTheory.CycDegRam

theorem tr_lt_finrank_cyclotomic : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  intro D h1 i hi
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  have hprime : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hbig : 4 * D.R.t * D.R.r + 1 < D.nd.l i := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.qd_big.1
    · exact D.host.qd_big.2
  have key := sub_one_le_two_mul_finrank D.host.E (D.nd.l i) hprime
    (fun v hv => ((h1 _ hmem).2 v hv).1)
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  omega

end GlobalTheory.CycDegRam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
section
noncomputable section

namespace GlobalTheory.InvJump

section Generic

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem eq_zero_of_mem_Fil_one (c : K) (h : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this
  exact PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h1 PD.mem_filtration_one)

theorem isJumpV_zero_of_invariant [CharZero Qp] (ρ : Representation LL G V) (x : V) (hx : x ≠ 0)
    (hinv : ∀ g, ρ g x = x) (τ : K →ₐ[Qp] LL) : IsJumpV PD ρ τ 0 := by
  classical
  haveI := PD.finK
  let b := Module.finBasis Qp K
  let b' := b.traceDual
  let y : V ⊗[Qp] BdR := ∑ i, (τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b i)
  have e1 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b' j) • b j := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_repr z, Finset.sum_mul, map_sum]
    simp only [b', smul_mul_assoc, map_smul, Module.Basis.trace_mul_traceDual]
    simp
  have e2 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b j) • b' j := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b'.sum_repr z]
    simp [b', Finset.sum_mul, Module.Basis.trace_traceDual_mul]
  have h0 : y ∈ FildR PD ρ τ 0 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp [y, actVdR, map_sum, hinv]
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
      intro c
      have l : mulVdR (LL := LL) (V := V) c y =
          ∑ i, ∑ j, Algebra.trace Qp K (c * b i * b' j) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [y, map_sum, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          LinearMap.mulLeft_apply, ← map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          conv_lhs => rw [e1 (c * b i), map_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← tmul_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      have r : τ c • y =
          ∑ j, ∑ i, Algebra.trace Qp K (c * b' j * b i) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, Finset.smul_sum, smul_tmul', smul_smul, ← map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          conv_lhs => rw [e2 (c * b' j), map_sum, Finset.sum_smul, sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_assoc]
      rw [l, r, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm]
    · refine Submodule.sum_mem _ fun i _ => ⟨(τ (b' i) • x) ⊗ₜ ⟨algebraMap K BdR (b i), ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  intro h
  rw [← h] at h0
  obtain ⟨w, hw⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[LL] LL, f x = 1 := Module.Projective.exists_dual_eq_one LL hx
  let m : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (φ ∘ₗ f.restrictScalars Qp).rTensor BdR
  have hm : ∀ w, m (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype w) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ (f v)) c.2
    | add a b ha hb => simpa only [map_add (f := _)] using Submodule.add_mem _ ha hb
  have h1 := hm w
  rw [hw] at h1
  have h2 : m y = algebraMap K BdR (∑ i, φ (τ (b' i)) • b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [m, hf, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [h2] at h1
  have h3 := eq_zero_of_mem_Fil_one PD _ (by rw [zero_add] at h1; exact h1)
  have h4 : ∀ i, φ (τ (b' i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
  have h5 : φ ∘ₗ τ.toLinearMap = 0 := b'.ext fun i => by simpa using h4 i
  have := LinearMap.congr_fun h5 1
  simp [hφ] at this

end Generic

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial


open scoped Pointwise in
theorem noInv_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  intro D bkP i s hJ v hv A hA x hx
  by_contra hx0
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) (D.nd.plOm.2 v) hA
  let Bw := bkP.br i v hv
  have inj : Function.Injective Bw.toLL := Subtype.val_injective.comp Bw.eO.injective
  let ψ : FractionRing (D.ntw.O0 i) →+* ↥Bw.LL.1 := IsFractionRing.lift inj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap inj a
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) ↥Bw.LL.1 := fun g => (Tmat i s g).map Bw.toLL
  have hM : ∀ g g', M (g * g') = M g * M g' := fun g g' => by
    simp only [M, ← Tgl_coe, map_mul, Units.val_mul, Matrix.map_mul]
  have hM1 : M 1 = 1 := by
    simp only [M, ← Tgl_coe, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let z : Fin D.R.r → ↥Bw.LL.1 := fun a => ψ (x a)
  have hz : ∀ g ∈ Dec (F := D.host.E) A, (M g).mulVec z = z := fun g hg => by
    funext a
    have := congrArg ψ (congrFun (hx g hg) a)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, hψ, M, z] using this
  have hz0 : (M k⁻¹).mulVec z ≠ 0 := fun h => hx0 (by
    have h1 := congrArg (M k).mulVec h
    rw [Matrix.mulVec_mulVec, ← hM, mul_inv_cancel, hM1, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    funext a
    exact ψ.injective (by simpa [z] using congrFun h1 a))
  let τ : EmbV bkP i v hv := Bw.Kw.1.val.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split Bw.Kw.1.val)
  have hj := isJumpV_zero_of_invariant (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) _ hz0 (fun g => by
    have hg : k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹ ∈ Dec (F := D.host.E) A := by
      have h : (Bw.e.symm g : Gen.GE D.nd) • D.nd.plOm.1 v = D.nd.plOm.1 v := (Bw.e.symm g).2
      show (k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹) • A = A
      rw [← hk, mul_smul, inv_smul_smul, mul_smul, h]
    have e : repV bkP i v hv (Tgl i s) g ((M k⁻¹).mulVec z) =
        (M (Bw.e.symm g : Gen.GE D.nd)).mulVec ((M k⁻¹).mulVec z) := by
      simp only [M, ← Tgl_coe]
      rfl
    rw [e]
    conv_rhs => rw [← hz _ hg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ← hM, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel, one_mul]) τ
  have := hJ v hv τ 0 hj
  omega

end GlobalTheory.InvJump

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfComm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_of_comm : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e v hcomm hv hord σ hσ

  let f : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φ : M ≃ₐ[F] f.fieldRange := f.equivFieldRange
  haveI : FiniteDimensional F f.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : IsMulCommutative (M ≃ₐ[F] M) := ⟨⟨hcomm⟩⟩
  haveI : IsAbelianGalois F M := IsAbelianGalois.mk
  haveI : IsAbelianGalois F f.fieldRange := IsAbelianGalois.of_algHom φ.symm.toAlgHom

  have h1 : φ.autCongr σ ∈ upperRamificationGroup F f.fieldRange v := by
    rw [← map_upperRamificationGroup_autCongr φ v]
    exact ⟨σ, hσ, rfl⟩
  have h2 := _root_.GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real F f.fieldRange p e v hv hord _ h1
  rw [← map_upperRamificationGroup_autCongr φ] at h2
  obtain ⟨τ, hτ, hτσ⟩ := h2
  have hτ' : τ = σ ^ p := φ.autCongr.injective (by simpa [map_pow] using hτσ)
  exact hτ' ▸ hτ

end GlobalTheory.PMon.Ram
end

