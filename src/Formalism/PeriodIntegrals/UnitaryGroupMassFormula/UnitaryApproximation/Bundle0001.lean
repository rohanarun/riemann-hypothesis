module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.Development
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

def TopStep : Prop := CayleyFin → EigAvoid → PI.UnitaryApproxFin.UnitaryApproxFin
def CayleyStep : Prop := ApproxE → BddR → UnitS → CayleyFin
def ApproxEStep : Prop := WeakApproxF → ApproxE

theorem unitaryApproxFin_of (h1 : TopStep) (h2 : CayleyStep) (h3 : ApproxEStep)
    (hW : WeakApproxF) (hB : BddR) (hU : UnitS) (hE : EigAvoid) :
    PI.UnitaryApproxFin.UnitaryApproxFin :=
  h1 (h2 (h3 hW) hB hU) hE

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.EigenvalueAvoidance
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

theorem ea_finite_bad {E R : Type*} [Field E] [CommRing R] (ι : E →+* R)
    {n : Type*} [Fintype n] [DecidableEq n] (g : Matrix n n R) (m : Ideal R) [m.IsMaximal] :
    {μ : E | (1 + ι μ • g).det ∈ m}.Finite := by
  classical
  let f : E →+* (R ⧸ m) := (Ideal.Quotient.mk m).comp ι
  let gb : Matrix n n (R ⧸ m) := g.map (Ideal.Quotient.mk m)
  let P : Polynomial (R ⧸ m) :=
    ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C).det
  have hev : ∀ c : R ⧸ m, P.eval c = (1 + c • gb).det := by
    intro c
    have h := (Polynomial.evalRingHom c).map_det
      ((1 : Matrix n n (Polynomial (R ⧸ m))) + (Polynomial.X : Polynomial (R ⧸ m)) • gb.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at h
    show Polynomial.eval c (Matrix.det _) = _
    rw [h]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hP0 : P ≠ 0 := by
    intro h
    have h0 := hev 0
    rw [h] at h0
    simp at h0
  have hfin : {c : R ⧸ m | P.eval c = 0}.Finite := by
    apply (P.roots.toFinset.finite_toSet).subset
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    simp [Polynomial.mem_roots hP0, hc]
  apply (hfin.preimage (fun _ _ _ _ h => f.injective h)).subset
  intro μ hμ
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hμ ⊢
  rw [hev]
  have h1 : Ideal.Quotient.mk m (1 + ι μ • g).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hμ
  rw [RingHom.map_det] at h1
  convert h1 using 2
  ext i j
  by_cases hij : i = j <;> simp [f, gb, Matrix.one_apply, hij]

theorem ea_artinian {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : IsArtinianRing (E ⊗[F] v.adicCompletion F) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (v.adicCompletion F ⊗[F] E) := IsArtinianRing.of_finite (v.adicCompletion F) _
  have hs : Function.Surjective (Algebra.TensorProduct.comm F (v.adicCompletion F) E) :=
    (Algebra.TensorProduct.comm F (v.adicCompletion F) E).surjective
  first
    | exact hs.isArtinianRing
    | exact IsArtinianRing.of_surjective _ hs
    | exact Function.Surjective.isArtinianRing hs

theorem eigenvalue_avoidance : EigAvoid := by
  intro F E _ _ _ _ _ n _ _ σ hσ hθ T g
  classical
  obtain ⟨θ, hθ⟩ := hθ
  let bad : Set E := ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
    ⋃ m ∈ {m : Ideal (E ⊗[F] v.adicCompletion F) | m.IsMaximal},
      {μ : E | (1 + PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) μ • g v).det ∈ m}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
    haveI : IsArtinianRing (E ⊗[F] v.adicCompletion F) := ea_artinian v
    refine Set.Finite.biUnion (IsArtinianRing.setOfPred_isMaximal_finite _) fun m hm => ?_
    haveI : m.IsMaximal := hm
    exact ea_finite_bad _ (g v) m
  have hnz1 : ∀ t : ℕ, (t : E) + θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : θ = -(t : E) := by linear_combination h
    rw [h', map_neg, map_natCast]
  have hnz2 : ∀ t : ℕ, (t : E) + σ θ ≠ 0 := by
    intro t h
    apply hθ
    have h' : σ θ = -(t : E) := by linear_combination h
    have h'' : θ = -(t : E) := by rw [← hσ θ, h', map_neg, map_natCast]
    rw [h', h'']
  let f : ℕ → E := fun t => ((t : E) + θ) / ((t : E) + σ θ)
  have hinj : Function.Injective f := by
    intro s t hst
    have hst' : ((s : E) + θ) / ((s : E) + σ θ) = ((t : E) + θ) / ((t : E) + σ θ) := hst
    rw [div_eq_div_iff (hnz2 s) (hnz2 t)] at hst'
    have h2 : ((s : E) - t) * (σ θ - θ) = 0 := by linear_combination hst'
    rcases mul_eq_zero.mp h2 with h | h
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd (sub_eq_zero.mp h) hθ
  have hrange : ¬ Set.range f ⊆ bad := fun h =>
    Set.infinite_range_of_injective hinj (hbad.subset h)
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := Set.not_subset.mp hrange
  refine ⟨f t, ?_, ?_⟩
  · show σ (((t : E) + θ) / ((t : E) + σ θ)) * (((t : E) + θ) / ((t : E) + σ θ)) = 1
    rw [map_div₀, map_add (f := _), map_add (f := _), map_natCast, hσ]
    have h1 := hnz1 t
    have h2 := hnz2 t
    field_simp
  · intro v hv
    by_contra hu
    obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
    exact ht (Set.mem_iUnion₂.mpr ⟨v, Finset.mem_coe.mpr hv, Set.mem_iUnion₂.mpr ⟨m, hm, hmem⟩⟩)

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.MemIntOEOfIsIntegral
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_smul_one {A : Type} [CommRing A] (ρ : A →+* A) (a : A) :
    PI.UnitaryApproxDefs.cT ρ (a • (1 : Matrix n n A)) = ρ a • 1 := by
  ext i j
  simp only [PI.UnitaryApproxDefs.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

def scU {A : Type} [CommRing A] (a b : A) (h : a * b = 1) : GL n A :=
  ⟨a • 1, b • 1, by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, h, one_smul],
    by rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_comm, h, one_smul]⟩

theorem scU_val {A : Type} [CommRing A] (a b : A) (h : a * b = 1) :
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = a • 1 := rfl

theorem scU_mem_UJ {A : Type} [CommRing A] (ρ : A →+* A) (J : Matrix n n A) (a b : A) (h : a * b = 1)
    (hρ : ρ a * a = 1) : scU (n := n) a b h ∈ PI.UnitaryApproxDefs.UJ ρ J := by
  show PI.UnitaryApproxDefs.cT ρ ((scU (n := n) a b h : GL n A) : Matrix n n A) * J *
    ((scU (n := n) a b h : GL n A) : Matrix n n A) = J
  rw [scU_val, cT_smul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_comm, hρ, one_smul]

end General

section Tensor

variable {F E : Type} [Field F] [CommRing E] [Algebra F E]

theorem sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    PI.UnitaryApproxDefs.sigR σ R (PI.UnitaryApproxDefs.inclE (F := F) R e) = PI.UnitaryApproxDefs.inclE (F := F) R (σ e) := by
  first
  | rfl
  | simp [PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]

end Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_intOE_of_isIntegral {x : E} (h : IsIntegral ℤ x) : x ∈ PI.UnitaryApproxDefs.intOE E := RingHom.mem_range.2 ⟨⟨x, h⟩, rfl⟩

theorem algebraMap_mem_intOE (a : 𝓞 F) : algebraMap F E (a : F) ∈ PI.UnitaryApproxDefs.intOE E := mem_intOE_of_isIntegral (IsIntegral.algebraMap (NumberField.RingOfIntegers.isIntegral_coe a))

theorem exists_nat_mul (x : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  rw [zsmul_eq_mul] at hyint
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, mem_intOE_of_isIntegral ?_⟩
  rw [Nat.cast_natAbs]
  rcases abs_choice y with h | h
  · rw [h]
    exact hyint
  · rw [h]
    push_cast
    rw [neg_mul]
    exact hyint.neg

theorem exists_int_mul (x : E) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ algebraMap F E (c : F) * x ∈ PI.UnitaryApproxDefs.intOE E := by
  obtain ⟨m, hm, hx⟩ := exists_nat_mul x
  refine ⟨(m : 𝓞 F), by exact_mod_cast hm.ne', ?_⟩
  simpa using hx

theorem inclE_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {x : E} (hx : x ∈ PI.UnitaryApproxDefs.intOE E) :
    PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) x ∈ Sv E v := Subring.subset_closure (Set.mem_union_left _ ⟨⟨x, hx⟩, rfl⟩)

theorem one_tmul_mem_Sv (v : HeightOneSpectrum (𝓞 F)) {t : v.adicCompletion F}
    (ht : t ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] t ∈ Sv E v := Subring.subset_closure (Set.mem_union_right _ ⟨⟨t, ht⟩, rfl⟩)

theorem dv_mem_Sv (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) : dv E v d ∈ Sv E v := inclE_mem_Sv v (algebraMap_mem_intOE d)

theorem dv_mul (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F) : dv E v (a * b) = dv E v a * dv E v b := by
  unfold dv
  rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul]

end PI.UnitaryApproxFinWork

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproximationFiniteUnitary
section
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace PI.UnitaryApproxFinWork

variable {F : Type} [Field F] [NumberField F]

theorem wa_isOpen_lt_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    IsOpen {y : v.adicCompletion F | Valued.v (y - x) < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [Valued.mem_nhds]
  refine ⟨1, fun z hz => ?_⟩
  have hz' : Valued.v (z - y) < 1 := by
    first
      | simpa using hz
      | exact_mod_cast hz
      | (simp only [Set.mem_setOf_eq, Units.val_one] at hz
         first
           | exact (Valuation.restrict_lt_iff _ _ _).mp hz
           | exact (Valuation.restrict_lt_one_iff _ _).mp hz
           | exact_mod_cast hz)
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hzx : z - x = (z - y) + (y - x) := by abel
  rw [hzx]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hz' hy)

theorem wa_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem wa_exists_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ b : F, Valued.v (x - algebraMap F (v.adicCompletion F) b) < 1 := by
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := by
    first
      | exact denseRange_algebraMap F v
      | exact UniformSpace.Completion.denseRange_coe
      | exact (UniformSpace.Completion.denseRange_coe).comp (WithVal.equiv (v.valuation F)).symm.surjective.denseRange
          (UniformSpace.Completion.continuous_coe _)
      | exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap_adicCompletion v
  obtain ⟨b, hb⟩ := hd.exists_mem_open (wa_isOpen_lt_one v x) ⟨x, by simp⟩
  refine ⟨b, ?_⟩
  rw [Valuation.map_sub_swap]
  exact hb

theorem wa_exists_int_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → F) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - b v) ≤ 1 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image b)
  have hd0 : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdF : algebraMap (𝓞 F) F (d : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hint : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F (d : 𝓞 F) * b v := by
    intro v hv
    obtain ⟨n, hn⟩ := hd (b v) (Finset.mem_image_of_mem b hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hint
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation (d : 𝓞 F) ≠ 0 := by
    intro v
    first
      | exact v.intValuation_ne_zero _ hd0
      | exact (v.intValuation).ne_zero_iff.mpr hd0
      | (intro h0
         have h1 := v.valuation_of_algebraMap (K := F) (d : 𝓞 F)
         rw [h0] at h1
         exact hdF ((Valuation.zero_iff _).mp h1))
  have hexp : ∀ v : HeightOneSpectrum (𝓞 F), ∃ e : ℕ,
      WithZero.exp (-(e : ℤ)) ≤ v.intValuation (d : 𝓞 F) := by
    intro v
    obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (d : 𝓞 F) = WithZero.exp k := by
      first
        | exact ⟨_, (WithZero.exp_log (hne v)).symm⟩
        | (obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp (hne v)
           exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩)
    refine ⟨k.natAbs, ?_⟩
    rw [hk, WithZero.exp_le_exp]
    first
      | omega
      | (rw [Int.natCast_natAbs]; exact neg_abs_le k)
  choose e he using hexp
  obtain ⟨m, hm⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) e
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => n v.1)
  refine ⟨algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F), fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ (e v)).mpr (hm v hv)
  have hkey : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F (d : 𝓞 F) - b v =
      algebraMap (𝓞 F) F (m - n v) / algebraMap (𝓞 F) F (d : 𝓞 F) := by
    rw [eq_div_iff hdF, sub_mul, div_mul_cancel₀ _ hdF, map_sub, hn v hv]
    ring
  rw [hkey, map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
  have hlt : (0 : WithZero (Multiplicative ℤ)) < v.intValuation (d : 𝓞 F) := zero_lt_iff.mpr (hne v)
  first
    | exact (div_le_one₀ hlt).mpr (h1.trans (he v))
    | exact div_le_one_of_le₀ (h1.trans (he v)) hlt.le

theorem weak_approximation_finite_unitary : WeakApproxF := by
  intro F _ _ T c D hD
  have hDF : ((D : 𝓞 F) : F) ≠ 0 := by
    first
      | exact_mod_cast hD
      | exact (RingOfIntegers.coe_ne_zero_iff).mpr hD
      | (intro h; exact hD (Subtype.ext h))
  choose b hb using fun v : HeightOneSpectrum (𝓞 F) =>
    wa_exists_close v (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹)
  obtain ⟨a', ha'⟩ := wa_exists_int_approx T b
  refine ⟨(D : F) * a', fun v hv => ?_⟩
  have hdv0 : algebraMap F (v.adicCompletion F) (D : F) ≠ 0 := (map_ne_zero _).mpr hDF
  refine ⟨c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a', ?_, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a' =
        (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) (b v)) +
          algebraMap F (v.adicCompletion F) (b v - a') := by
      rw [map_sub]
      ring
    rw [e1]
    refine le_trans (Valuation.map_add _ _ _) (max_le (hb v).le ?_)
    rw [wa_valued_algebraMap, Valuation.map_sub_swap]
    exact ha' v hv
  · rw [map_mul, mul_sub, mul_comm (algebraMap F (v.adicCompletion F) (D : F)) (c v * _), mul_assoc,
      inv_mul_cancel₀ hdv0, mul_one]

end PI.UnitaryApproxFinWork

end
end

