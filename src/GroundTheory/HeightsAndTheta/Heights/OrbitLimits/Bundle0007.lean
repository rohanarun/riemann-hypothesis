module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageCoord.mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h

theorem ImageCoord.proof : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PBlockTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal

namespace BlockTrdeg

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open scoped Classical

section Denominators

variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]

theorem exists_nat_mul_mem_range (ψ : MvPolynomial σ ℤ →+* L) {y : L}
    (hy : y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : L) * y ∈ ψ.range := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, one_ne_zero, ⟨X p, by rw [Nat.cast_one, one_mul]⟩⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ⟨(q.num : MvPolynomial σ ℤ), ?_⟩⟩
    rw [map_intCast, ← map_natCast (algebraMap ℚ L), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x + y) = m * (n * x) + n * (m * y) := by push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hnx) (mul_mem (natCast_mem _ _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x * y) = (n * x) * (m * y) := by push_cast; ring
    rw [e]
    exact mul_mem hnx hmy

theorem exists_nat_mul_mem_range_finset (ψ : MvPolynomial σ ℤ →+* L) (s : Finset L)
    (hs : ∀ y ∈ s, y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ y ∈ s, (n : L) * y ∈ ψ.range := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨n, hn, hns⟩ := ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨m, hm, hma⟩ := exists_nat_mul_mem_range ψ (hs a (Finset.mem_insert_self a s))
    refine ⟨n * m, mul_ne_zero hn hm, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) hma
    · rw [Nat.cast_mul, mul_comm (n : L), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hns y hy)

end Denominators

section Grading

variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

abbrev Forgotten (κ : K → K') : Type := {k' : K' // k' ∉ Set.range κ}

def forgetWeight (κ : K → K') : (Σ k', ι' k') → (Forgotten κ → ℕ) :=
  fun q k ↦ if q.1 = k.1 then 1 else 0

theorem weight_forgetWeight (κ : K → K') (m : (Σ k', ι' k') →₀ ℕ) (k : Forgotten κ) :
    Finsupp.weight (forgetWeight (ι' := ι') κ) m k = ∑ i, m ⟨k.1, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k.1]
  · simp [forgetWeight]
  · intro b _ hb
    simp [forgetWeight, hb]
  · simp

theorem isHomogeneous_forgetWeight (κ : K → K') {P : Ideal (MRing ι')} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (forgetWeight (ι' := ι') κ)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := hS x hx
  refine ⟨fun k ↦ a k.1, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_⟩
  intro d hd
  funext k
  rw [weight_forgetWeight]
  exact ha d (mem_support_iff.mpr hd) k.1


omit [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isWeightedHomogeneous_rename (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : ∀ p, (v p).1 ∈ Set.range κ) (g : MvPolynomial (Σ k, ι k) ℤ) :
    IsWeightedHomogeneous (forgetWeight κ) (rename v g) 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact isWeightedHomogeneous_C _ _
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add hq
  | mul_X p q hp =>
    rw [map_mul, rename_X]
    have h0 : forgetWeight κ (v q) = 0 := by
      funext k
      simp only [forgetWeight, Pi.zero_apply]
      rw [if_neg]
      intro h
      exact k.2 (h ▸ hv q)
    have := hp.mul (isWeightedHomogeneous_X ℤ (forgetWeight κ) (v q))
    rwa [h0, add_zero] at this

def forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1) (a : Forgotten κ →₀ ℕ) : MRing ι' :=
  ∏ k, X ⟨k.1, i k⟩ ^ a k


omit [∀ k, Fintype (ι' k)] in
theorem isWeightedHomogeneous_forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1)
    (a : Forgotten κ →₀ ℕ) :
    IsWeightedHomogeneous (forgetWeight κ) (forgetMonomial κ i a) ⇑a := by
  have := IsWeightedHomogeneous.prod Finset.univ (fun k ↦ (X ⟨k.1, i k⟩ : MRing ι') ^ a k)
    (fun k ↦ a k • forgetWeight κ ⟨k.1, i k⟩)
    fun k _ ↦ (isWeightedHomogeneous_X ℤ (forgetWeight κ) _).pow (a k)
  unfold forgetMonomial
  convert this using 1
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [forgetWeight]
  · intro b _ hb
    rw [Pi.smul_apply, forgetWeight, if_neg (fun h ↦ hb (Subtype.ext h)), smul_zero]
  · simp

end Grading

section Independence

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem algebraicIndependent_forgotten (hv : ∀ p, (v p).1 = κ p.1) (hP : IsMultiHomogIdeal P')
    (hprime : P'.IsPrime) (hker : RingHom.ker φ = P') (i : ∀ k : Forgotten κ, ι' k.1)
    (hi : ∀ k, (X ⟨k.1, i k⟩ : MRing ι') ∉ P') (S : Subalgebra ℚ L)
    (hS : S ≤ adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) :
    AlgebraicIndependent S (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) := by
  rw [algebraicIndependent_iff]
  intro p hp
  set ψ : MvPolynomial (Σ k, ι k) ℤ →+* L := φ.comp (rename v).toRingHom with hψ
  have hA : adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) = adjoin ℚ (Set.range fun p ↦ ψ (X p)) := by
    simp [ψ]
  obtain ⟨N, hN, hNs⟩ := exists_nat_mul_mem_range_finset ψ (p.support.image fun a ↦ ((AddMonoidAlgebra.coeff p a : S) : L)) (by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hA]
    exact hS (AddMonoidAlgebra.coeff p a).2)
  choose g hg using fun a : p.support ↦ RingHom.mem_range.mp (hNs _ (Finset.mem_image_of_mem _ a.2))
  set H : MRing ι' := ∑ a : p.support, rename v (g a) * forgetMonomial κ i a.1 with hHdef
  have hH : H ∈ P' := by
    rw [← hker, RingHom.mem_ker]
    have e1 : φ H = (N : L) * aeval (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) p := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hHdef, map_sum, aeval_def, eval₂_eq', Finset.mul_sum, ← Finset.sum_coe_sort p.support]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [map_mul, show φ (rename v (g a)) = ψ (g a) from rfl, hg a, forgetMonomial, map_prod]
      simp only [map_pow, mul_assoc]
      rfl
    rw [e1, hp, mul_zero]
  refine MvPolynomial.ext _ _ fun a ↦ ?_
  rw [AddMonoidAlgebra.coeff_zero]
  by_cases ha : a ∈ p.support
  swap
  · exact notMem_support_iff.mp ha
  have hhom : ∀ b : p.support, IsWeightedHomogeneous (forgetWeight κ)
      (rename v (g b) * forgetMonomial κ i b.1) ⇑b.1 := by
    intro b
    have := (isWeightedHomogeneous_rename κ (fun p ↦ ⟨p.1, (hv p).symm⟩) (g b)).mul
      (isWeightedHomogeneous_forgetMonomial κ i b.1)
    rwa [zero_add] at this
  have hcomp := weightedHomogeneousComponent_mem_of_mem ℤ (forgetWeight κ)
    (isHomogeneous_forgetWeight κ hP) hH (⇑a)
  have e2 : weightedHomogeneousComponent (forgetWeight κ) (⇑a) H =
      rename v (g ⟨a, ha⟩) * forgetMonomial κ i a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHdef, map_sum, Finset.sum_eq_single ⟨a, ha⟩]
    · exact (hhom ⟨a, ha⟩).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (hhom b).weightedHomogeneousComponent_ne _
        (fun h ↦ hb (Subtype.ext (DFunLike.coe_injective h).symm))
    · simp
  rw [e2] at hcomp
  rcases hprime.mem_or_mem hcomp with h1 | h1
  · rw [← hker, RingHom.mem_ker] at h1
    have h2 : (N : L) * ((AddMonoidAlgebra.coeff p a : S) : L) = 0 := by
      rw [← hg ⟨a, ha⟩]
      exact h1
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    have h3 := (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hN)
    exact_mod_cast h3
  · exfalso
    have := hprime
    rw [forgetMonomial] at h1
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
    exact hi k (hprime.mem_of_pow_mem _ hk)

end Independence

theorem proof : Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' L _ _ φ hκv hP hker
  obtain ⟨hκ, -, hv, -⟩ := hκv
  choose i hi using fun k : Forgotten κ ↦ hP.2.2 k.1
  set A := adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) with hAdef
  set B := adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)) with hBdef
  have : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  obtain ⟨τ, x, hx⟩ := exists_isTranscendenceBasis' ℚ A
  set b₀ : τ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent ℚ b₀ := hx.1.map' Subtype.val_injective
  have hSA : adjoin ℚ (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr fun j ↦ (x j).2)
  have he := algebraicIndependent_forgotten hv hP.2.1 hP.1 hker i hi _ hSA
  have hind : AlgebraicIndependent ℚ (Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀) :=
    hb₀.sumElim he
  have hAB : A ≤ B := adjoin_mono (Set.range_subset_iff.mpr fun p ↦ ⟨v p, rfl⟩)
  have hmem : ∀ j, Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀ j ∈ B := by
    rintro (k | j)
    · exact subset_adjoin ⟨_, rfl⟩
    · exact hAB (x j).2
  have hy : AlgebraicIndependent ℚ (fun j ↦ (⟨_, hmem j⟩ : B)) := AlgebraicIndependent.of_comp B.val hind
  have hle := hy.cardinalMk_le_trdeg
  have hcard : ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) = #(Forgotten κ) := by
    rw [Cardinal.mk_fintype, Fintype.card_subtype_compl, Set.card_range_of_injective hκ]
  rw [← hx.cardinalMk_eq_trdeg, hcard, add_comm, ← lift_id #(Forgotten κ), ← lift_id #τ, ← mk_sum]
  exact hle

end BlockTrdeg

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalMultComap
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

theorem LocalMultComap.proof : LocalMultComap.Statement := by
  intro R S _ _ σ I W hσ hW
  set P := W.comap σ with hPdef
  have hPW : P = W.comap σ := rfl
  unfold localMult
  rw [dite_eq_left hW, dite_eq_left (Ideal.comap_isPrime σ W)]

  have hM : P.primeCompl.map σ = W.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hσ y
      exact ⟨x, hy, rfl⟩
  have : IsLocalization (P.primeCompl.map σ) (Localization.AtPrime W) := by
    rw [hM]; infer_instance
  let φ : Localization.AtPrime P →+* Localization.AtPrime W := Localization.localRingHom P W σ hPW
  have hφ : Function.Surjective φ := IsLocalization.map_surjective_of_surjective _ _ _ hσ
  let _ : Algebra (Localization.AtPrime P) (Localization.AtPrime W) := φ.toAlgebra
  set J : Ideal (Localization.AtPrime P) := (I.comap σ).map (algebraMap R (Localization.AtPrime P))
  set I' : Ideal (Localization.AtPrime W) := I.map (algebraMap S (Localization.AtPrime W))
  have hcomp : φ.comp (algebraMap R (Localization.AtPrime P)) =
      (algebraMap S (Localization.AtPrime W)).comp σ :=
    RingHom.ext fun x => Localization.localRingHom_to_map P W σ hPW x
  have hJ : J.map φ = I' := by
    simp only [J, I', Ideal.map_map, hcomp]
    rw [← Ideal.map_map, Ideal.map_comap_of_surjective σ hσ]
  have hker : RingHom.ker φ ≤ J := by
    intro x hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have h0 : φ (IsLocalization.mk' _ r s) = 0 := hx
    simp only [φ, Localization.localRingHom, IsLocalization.map_mk'] at h0
    obtain ⟨⟨t, ht⟩, htr⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
    obtain ⟨t', rfl⟩ := hσ t
    have hmem : t' * r ∈ I.comap σ := by
      simp only [Ideal.mem_comap, map_mul]
      rw [htr]; exact I.zero_mem
    have ht' : t' ∈ P.primeCompl := ht
    rw [IsLocalization.mk'_mem_iff]
    have h1 : algebraMap R (Localization.AtPrime P) (t' * r) ∈ J := Ideal.mem_map_of_mem _ hmem
    rw [map_mul] at h1
    have hu : IsUnit (algebraMap R (Localization.AtPrime P) t') :=
      IsLocalization.map_units _ (⟨t', ht'⟩ : P.primeCompl)
    exact (Submodule.smul_mem_iff_of_isUnit J hu).mp h1

  let ψ : Localization.AtPrime P →ₐ[Localization.AtPrime P] Localization.AtPrime W ⧸ I' :=
    (Ideal.Quotient.mkₐ _ I').comp (Algebra.ofId (Localization.AtPrime P) (Localization.AtPrime W))
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective (Localization.AtPrime P) I').comp hφ
  have hkerψ : RingHom.ker ψ = J := by
    have : RingHom.ker ψ = I'.comap φ := by
      ext x
      simp only [ψ, RingHom.mem_ker, Ideal.mem_comap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.ofId_apply]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [this, ← hJ, Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hker]
  have e := (Submodule.quotEquivOfEq J (RingHom.ker ψ) hkerψ.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hψ).toLinearEquiv
  rw [e.length_eq, Module.length_eq_of_surjective hφ]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraphInt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartAbsDens)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)

def VarIntGraphInt.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
    (∀ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B →
      Integrable (chartAbsDens (graphIdeal J p) B F Φ)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartDimBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I1
open ReciprocityTheory.ChartRestriction.G.Geo hiding IsMultiHomog

universe u v w

def ChartDimBound.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k), IsMultiProjPrime V → IsChart V i →
    ringKrullDim (MRingOver F ι ⧸ V) ≤
      ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) + (Fintype.card K : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartFiniteIrrel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def ChartFiniteIrrel.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) (i : ∀ k, ι k),
    IsMultiHomogIdeal V → _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) →
    (∀ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes, ¬ _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) →
    Module.Finite F (MRingOver F ι ⧸ chartIdeal V i)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def SegreComponent.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (n : ℕ) (f : MRingOver F ι), IsProjVarF V (n + 1) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) → (divSupp V f).Nonempty

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def SegreDivisor.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (n : ℕ), IsProjVarF V (n + 1) →
    ∃ f : MRingOver F ι, _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => 1) ∧ f ∉ V ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f ≠ 0

end GroundTheory.Heights₂.Heights.Targets
end

