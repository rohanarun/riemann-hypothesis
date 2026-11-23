module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockSectionsRank

section Forms

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

def blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : (Σ k, ι k) → MvPolynomial (Ix (Fin r)) ℤ :=
  fun p => if h : p.1 = k₀ then ∑ j, C (N (h ▸ p.2) j) * X j else 0

theorem blockSubst_block (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (i : ι k₀) :
    blockSubst k₀ N ⟨k₀, i⟩ = ∑ j, C (N i j) * X j := by
  simp [blockSubst]

theorem isHomogeneous_blockSubst (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (p : Σ k, ι k) :
    (blockSubst k₀ N p).IsHomogeneous 1 := by
  unfold blockSubst
  split_ifs
  · exact IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X ℤ j).C_mul _
  · exact isHomogeneous_zero _ _ _

def fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) : MRing ι →ₐ[ℤ] MvPolynomial (Ix (Fin r)) ℤ :=
  bind₁ (blockSubst k₀ N)

def blockLin (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) : Ix (Fin r) → MRing ι :=
  fun j => ∑ i, C (M j i) * X ⟨k₀, i⟩

def back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) : MvPolynomial (Ix (Fin r)) ℤ →ₐ[ℤ] MRing ι :=
  bind₁ (blockLin k₀ M)

theorem fst_eq_of_mem_support {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n))
    {c : (Σ k, ι k) →₀ ℕ} (hc : AddMonoidAlgebra.coeff f c ≠ 0) {p : Σ k, ι k} (hp : p ∈ c.support) : p.1 = k₀ := by
  by_contra hne
  have h := hf c (mem_support_iff.mpr hc) p.1
  rw [blockDeg, if_neg hne, Finset.sum_eq_zero_iff] at h
  exact (Finsupp.mem_support_iff.mp hp) (h p.2 (Finset.mem_univ _))

theorem isHomogeneous_of_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    f.IsHomogeneous n := by
  intro c hc
  have h := hf c (mem_support_iff.mpr hc)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma]
  simp only [Pi.one_apply, smul_eq_mul, mul_one, h, blockDeg, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem isHomogeneous_fwd (k₀ : K) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) {f : MRing ι} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) : (fwd k₀ N f).IsHomogeneous n := by
  have := (isHomogeneous_of_blockDeg hf).aeval (blockSubst k₀ N) (isHomogeneous_blockSubst k₀ N)
  rw [one_mul, aeval_eq_bind₁] at this
  exact this

def wB : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_wB (c : (Σ k, ι k) →₀ ℕ) : Finsupp.weight wB c = fun k => ∑ i, c ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k (fun k' _ hk' => ?_) (by simp)]
  · simp [wB]
  · simp [wB, Ne.symm hk']

theorem isMultiHomog_iff_wB (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous wB f a := by
  constructor
  · intro h c hc
    rw [weight_wB]
    funext k
    exact h c (mem_support_iff.mpr hc) k
  · intro h c hc k
    have := h (mem_support_iff.mp hc)
    rw [weight_wB] at this
    exact congrFun this k

theorem isMultiHomog_back (k₀ : K) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) {g : MvPolynomial (Ix (Fin r)) ℤ} {n : ℕ}
    (hg : g.IsHomogeneous n) : IsMultiHomog (back k₀ M g) (blockDeg k₀ n) := by
  have hbf : ∀ j, IsWeightedHomogeneous wB (blockLin k₀ M j) (Pi.single k₀ 1) := fun j =>
    IsWeightedHomogeneous.sum _ _ _ fun i _ => (isWeightedHomogeneous_X ℤ wB (⟨k₀, i⟩ : Σ k, ι k)).C_mul _
  rw [isMultiHomog_iff_wB, show blockDeg k₀ n = n • Pi.single k₀ 1 by
    funext k; by_cases hk : k = k₀ <;> simp [blockDeg, hk]]
  rw [back, ← aeval_eq_bind₁, aeval_def]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [← zero_add (n • Pi.single k₀ 1)]
  apply IsWeightedHomogeneous.mul (by rw [MvPolynomial.algebraMap_eq]; exact isWeightedHomogeneous_C _ _)
  rw [Finsupp.mem_support_iff] at hd
  have hn : ∑ j ∈ d.support, d j = n := by
    have := hg hd
    rw [Finsupp.weight_apply] at this
    simpa [Finsupp.sum] using this
  have hp := IsWeightedHomogeneous.prod d.support (fun j => blockLin k₀ M j ^ d j)
    (fun j => d j • Pi.single k₀ 1) fun j _ => (hbf j).pow (d j)
  rw [← Finset.sum_smul, hn] at hp
  exact hp

end Forms

section Values

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}
  {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {M : Matrix (Ix (Fin r)) (ι k₀) ℤ}
  {N : Matrix (ι k₀) (Ix (Fin r)) ℤ} {x : Ix (Fin r) → Ω}

theorem aeval_back (h : IsBlockImage y k₀ M N x) (g : MvPolynomial (Ix (Fin r)) ℤ) :
    aeval y (back k₀ M g) = aeval x g := by
  have hx : (fun j => aeval y (blockLin k₀ M j)) = x := funext fun j => by simp [blockLin, h.1 j]
  rw [back, aeval_bind₁, hx]

theorem aeval_fwd (h : IsBlockImage y k₀ M N x) {f : MRing ι} {n : ℕ} (hf : IsMultiHomog f (blockDeg k₀ n)) :
    aeval x (fwd k₀ N f) = aeval y f := by
  rw [fwd, aeval_bind₁, aeval_def, aeval_def]
  refine eval₂_congr _ _ _ fun {p} {c} hp hc => ?_
  obtain ⟨k, i⟩ := p
  have hk : k = k₀ := fst_eq_of_mem_support hf hc hp
  subst hk
  rw [blockSubst_block, h.2 i]
  simp

theorem secM_eq (h : IsBlockImage y k₀ M N x) (n : ℕ) :
    secM y (blockDeg k₀ n) = (sec ℤ x n).toAddSubgroup := by
  unfold secM
  congr 1
  have hset : {s | ∃ g : MRing ι, IsMultiHomog g (blockDeg k₀ n) ∧ aeval y g = s} =
      ((sec ℤ x n : Submodule ℤ Ω) : Set Ω) := by
    ext s
    simp only [Set.mem_ofPred_eq, sec, Submodule.map_coe, Set.mem_image, SetLike.mem_coe,
      mem_homogeneousSubmodule, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨fwd k₀ N g, isHomogeneous_fwd k₀ N hg, aeval_fwd h hg⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨back k₀ M g, isMultiHomog_back k₀ M hg, aeval_back h g⟩
  rw [hset, Submodule.span_eq]

end Values

theorem exists_blockBasis {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) :
    ∃ (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
      IsBlockImage y k₀ M N x ∧ LinearIndependent ℤ x := by
  set W : Submodule ℤ Ω := Submodule.span ℤ (Set.range fun i : ι k₀ => y ⟨k₀, i⟩) with hW
  have : Module.Finite ℤ W := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  set b := (Module.Free.chooseBasis ℤ W).reindex (Fintype.equivFin _) with hb
  have hc : ∀ j, ∃ c : ι k₀ → ℤ, ∑ i, c i • y ⟨k₀, i⟩ = (b j : Ω) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).2
  choose c hc using hc
  refine ⟨_, fun j i => c j.2 i, fun i j => b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2,
    fun j => (b j.2 : Ω), ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · show (b j.2 : Ω) = ∑ i, (c j.2 i : Ω) * y ⟨k₀, i⟩
    rw [← hc j.2]
    simp [zsmul_eq_mul]
  · have h2 := congrArg Subtype.val (b.sum_repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show y ⟨k₀, i⟩ = ∑ j : Ix (Fin _),
      ((b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2 : ℤ) : Ω) * (b j.2 : Ω)
    conv_lhs => rw [← h2]
    simp [Fintype.sum_sigma, zsmul_eq_mul]
  · have h1 := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    refine h1.comp (fun j : Ix (Fin _) => j.2) ?_
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, a'⟩ h
    cases h
    rfl

end BlockSectionsRank


open BlockSectionsRank in
theorem BlockSectionsRank.proof (hRank : RankOfSections.Statement) (hGF : GenericFibre.Statement)
    (hSR : SectionsRank.Statement) (hArith : BlockImageArith.Statement) (hDeg : BlockImageGenDeg.Statement) :
    BlockSectionsRank.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ hD hY hB
  obtain ⟨r, M, N, x, hx, hind⟩ := exists_blockBasis y k₀
  have hX : IsArithVar (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x) (D + 1) := hArith D K ι Ω y k₀ r M N x hY hB hx hind
  obtain ⟨hprime, hdim⟩ := hGF Ω (Fin r) x D hX
  obtain ⟨C, hC⟩ := hRank (Fin r) _ D hprime hdim
  have hdeg := hDeg D K ι Ω (Fin r) y k₀ M N x hY hB hx
  refine ⟨C, fun n => ?_⟩
  have hrank : (Module.finrank ℤ (secM y (blockDeg k₀ n)) : ℝ) =
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Fin r))
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) : ℝ) := by
    rw [hSR Ω (Fin r) x n, secM_eq hx n]
    rfl
  have hpow : ((n : ℝ) + 1) ^ ((D : ℝ) - 1) = ((n : ℝ) + 1) ^ (D - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub hD, Nat.cast_one]
  have hgd : (genDeg (mCoordIdeal y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀) : ℝ) =
      (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)))
        (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) := by
    rw [← hdeg]
    unfold genDeg
    congr!
  have := hC n
  rw [hpow] at this
  rw [hrank, hgd]
  exact this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

namespace ChartConstantsDetermined

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_chart_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = eval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y f) := by
  have h := MvPolynomial.ringHom_ext
    (f := (aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω).toRingHom)
    (g := (eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp (mConeMap y).toRingHom)
    (fun r => by simp) (fun p => by simp [mConeMap, div_eq_mul_inv])
  exact RingHom.congr_fun h f

theorem aeval_chart_of_isMultiHomog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = aeval y f * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k := by
  rw [aeval_chart_eq, ProjLine.mConeMap_eq_of_isMultiHomog y hf]
  simp only [map_mul, eval_C, map_prod, map_pow, eval_X]

theorem aeval_chart_eq_zero (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  rw [aeval_chart_eq, show mConeMap y f = 0 from RingHom.mem_ker.mp hf, map_zero]

variable (F : Type) [Field F] [NumberField F] [Algebra F Ω]

def chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) : ↥(chartRingZ y c ⊔ intsIn F Ω) :=
  ⟨y p / y ⟨p.1, c p.1⟩, le_sup_left (a := chartRingZ y c) (Algebra.subset_adjoin (Set.mem_range_self p))⟩

variable {F}

def pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : (Σ k, ι k) → ℂ :=
  fun p => w (chartCoord F y c p)

theorem coe_aeval_chartCoord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (f : MRing ι) :
    ((aeval (chartCoord F y c) f : ↥(chartRingZ y c ⊔ intsIn F Ω)) : Ω) =
      aeval (fun p => y p / y ⟨p.1, c p.1⟩) f := by
  show (Subalgebra.val _) (aeval (chartCoord F y c) f) = _
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

theorem eval_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ)
    (f : MRing ι) :
    eval (pointOf y c w) (map (Int.castRingHom ℂ) f) = w (aeval (chartCoord F y c) f) := by
  rw [eval_map]
  have h := MvPolynomial.ringHom_ext (f := eval₂Hom (Int.castRingHom ℂ) (pointOf y c w))
    (g := w.comp (aeval (chartCoord F y c) : MRing ι →ₐ[ℤ] _).toRingHom)
    (fun r => by simp) (fun p => by simp [pointOf])
  exact RingHom.congr_fun h f

theorem pointOf_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : pointOf y c w ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : chartCoord F y c ⟨k, c k⟩ = 1 := Subtype.ext (by simp [chartCoord, hc k])
    simp [pointOf, h1]
  · rw [eval_pointOf]
    have h0 : aeval (chartCoord F y c) f = 0 :=
      Subtype.ext (by rw [coe_aeval_chartCoord]; simpa using aeval_chart_eq_zero y c hf)
    simp [h0]

def intsMap {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) : 𝓞 F →+* ℂ :=
  w.comp ((Subalgebra.inclusion (le_sup_right : intsIn F Ω ≤ chartRingZ y c ⊔ intsIn F Ω)).toRingHom.comp
    (((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict).toRingHom)

theorem intsMap_apply {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) (a : 𝓞 F) :
    intsMap w a = w ⟨algebraMap F Ω (algebraMap (𝓞 F) F a),
      le_sup_right (a := chartRingZ y c) (AlgHom.mem_range_self _ a)⟩ := rfl

theorem intsMap_injective {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    Function.Injective (intsMap w) := by
  refine (RingHom.injective_iff_ker_eq_bot _).mpr (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  refine eq_bot_iff.2 fun n hn => ?_
  rw [Ideal.mem_bot]
  simpa [Ideal.mem_comap, RingHom.mem_ker] using hn

theorem liesOver_pointOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : ↥(chartRingZ y c ⊔ intsIn F Ω) →+* ℂ) :
    LiesOver y (IsFractionRing.lift (K := F) (intsMap_injective w)) (pointOf y c w) := by
  intro d g h θ hg hh hrel
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) θ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hψb : intsMap w b ≠ 0 := (map_ne_zero_iff _ (intsMap_injective w)).mpr hb0
  have hB : algebraMap F Ω (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb0
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap, eval_pointOf, eval_pointOf,
    div_mul_eq_mul_div, eq_div_iff hψb, intsMap_apply, intsMap_apply, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, coe_aeval_chartCoord]
  rw [aeval_chart_of_isMultiHomog y c hg, aeval_chart_of_isMultiHomog y c hh, hrel, map_div₀]
  field_simp

theorem proof : Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hU c hc w w' hw
  have hz : pointOf y c w = pointOf y c w' := funext fun p =>
    RingHom.congr_fun hw ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin (Set.mem_range_self p)⟩
  obtain ⟨sg, -, huniq⟩ := hU _ (pointOf_mem y c hc w)
  have e1 := huniq _ (liesOver_pointOf y c w)
  have e2 := huniq (IsFractionRing.lift (K := F) (intsMap_injective w'))
    (by rw [hz]; exact liesOver_pointOf y c w')
  ext x
  rcases x with ⟨_, a, rfl⟩
  show intsMap w a = intsMap w' a
  rw [← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w) a,
    ← IsFractionRing.lift_algebraMap (K := F) (intsMap_injective w') a, e1, e2]

end ChartConstantsDetermined

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology MeasureTheory

noncomputable section

namespace ConstantShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact hc _ hy'.2.1
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_const P h]
  · rfl


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (r : ℝ) :
    ptsIntegral P φ (fun _ => r) = r * ptsIntegral P φ (fun _ => 1) := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun _ => r) y w = r * sheetDensity P Ψ φ (fun _ => 1) y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, hs]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
  · simp

theorem proof : ConstantShift.Statement := by
  intro K _ ι _ I P D A η hI hP hA
  have hS : IsSmoothHerm (HermLine.constShift A η) := isSmoothHerm_constShift hA η
  set g := geomDeg P A D with hg
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun n i =>
    if (i : ℕ) < n then HermLine.constShift A η else A
  have hLs : ∀ n i, IsSmoothHerm (L n i) := by
    intro n i
    dsimp only [L]
    split_ifs
    exacts [hS, hA]
  have hLpot : ∀ n i, ∃ c : ℝ, ∀ z ∈ mcPts P, Real.log ((L n i).h z) = Real.log (A.h z) + c := by
    intro n i
    dsimp only [L]
    split_ifs
    · refine ⟨-η, fun z hz => ?_⟩
      rw [constShift_h, Real.log_mul (A.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    · exact ⟨0, fun z _ => by rw [add_zero]⟩
  have step : ∀ n, n < D + 1 → I P (D + 1) (L (n + 1)) = I P (D + 1) (L n) - η * g := by
    intro n hn
    set j : Fin (D + 1) := ⟨n, hn⟩ with hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := Fin.init (L n ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (n + 1) ∘ σ) = M := by
      funext i
      have hv : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) ≠ n := fun h' => hne i (Fin.ext h')
      have hiff : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n + 1 ↔
          ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n := by omega
      simp only [hMdef, Fin.init, Function.comp, L, hiff]
    have e0 : L n ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L n ∘ σ)
      have hl : (L n ∘ σ) (Fin.last D) = A := by
        simp only [Function.comp, hσl, hj, L, lt_irrefl, if_false]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (n + 1) ∘ σ = Fin.snoc M (HermLine.constShift A η) := by
      have h0 := Fin.snoc_init_self (q := L (n + 1) ∘ σ)
      have hl : (L (n + 1) ∘ σ) (Fin.last D) = HermLine.constShift A η := by
        simp only [Function.comp, hσl, hj, L, lt_add_one, if_true]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs n _
    have hmc : I P (D + 1) (Fin.snoc M (HermLine.constShift A η)) =
        I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => η) :=
      metricChange K ι I hI P D M A (fun _ => η) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
    have hint : ptsIntegral P (pot M) (fun _ => η) = η * g := by
      rw [ptsIntegral_const, hg, geomDeg]
      congr 1
      exact ptsIntegral_add_const P (fun i => hLpot n _) _
    rw [← hI.1 P (D + 1) (L (n + 1)) σ hP (hLs (n + 1)), ← hI.1 P (D + 1) (L n) σ hP (hLs n), e0, e1,
      hmc, hint]
  have hall : ∀ n, n ≤ D + 1 → I P (D + 1) (L n) = I P (D + 1) (L 0) - n * η * g := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [step n (by omega), ih (by omega)]
      push_cast
      ring
  have hL0 : L 0 = fun _ => A := by
    funext i
    simp [L]
  have hLD : L (D + 1) = fun _ => HermLine.constShift A η := by
    funext i
    simp [L, i.isLt]
  have := hall (D + 1) le_rfl
  rw [hL0, hLD] at this
  rw [this]
  push_cast
  ring

end ConstantShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

