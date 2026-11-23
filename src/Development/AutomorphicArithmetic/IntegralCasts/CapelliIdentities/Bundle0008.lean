module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoerciveOfPositiveDefinite
section
open scoped ComplexOrder in
theorem UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] {P : Matrix ι ι ℂ},
      P.PosDef → ∃ (c : ℝ), 0 < c ∧
        ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
  intro ι _ P hP
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun _ j => (hι.false j).elim⟩
  have hcont : Continuous fun z : ι → ℂ => (star z ⬝ᵥ P.mulVec z).re := by
    unfold dotProduct Matrix.mulVec dotProduct
    fun_prop
  have hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hc : 0 < (star u ⬝ᵥ P.mulVec u).re := hP.re_dotProduct_pos hu0
  refine ⟨_, hc, fun z j => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hw : (‖z‖⁻¹ • z) ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have h1 : (star u ⬝ᵥ P.mulVec u).re ≤ (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re := hmin hw
  have h2 : (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re
      = ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) := by
    rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  have h3 : (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
    rw [h2] at h1
    calc (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2
        ≤ ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (star z ⬝ᵥ P.mulVec z).re := by field_simp
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) 2) hc.le).trans h3
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue
section
theorem UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig :
    ∀ {k : Type} [inst : Field k] [IsAlgClosed k]
    {V : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V] [FiniteDimensional k V] (S : Set (Module.End k V)),
    (∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) →
      ∀ (d : ℕ) (W : Submodule k V),
        Module.finrank k ↥W = d →
          W ≠ ⊥ →
            (∀ f ∈ S, ∀ x ∈ W, (f : V → V) x ∈ W) → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ f ∈ S, ∃ (c : k), (f : V → V) v = c • v := by
  intro k _ _ V _ _ _ S hS d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W hd hW hinv
    by_cases h : ∀ f ∈ S, ∀ x ∈ W, ∃ c : k, f x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨v, hv, hv0, fun f hf => h f hf v hv⟩
    · push Not at h
      obtain ⟨f, hf, x, hx, hfx⟩ := h
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict (hinv f hf) : Module.End k W)
      obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
      have hwe : f (w : V) = μ • (w : V) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : W ⊓ f.eigenspace μ < W := by
        refine lt_of_le_of_ne inf_le_left fun he => ?_
        have hx' : x ∈ W ⊓ f.eigenspace μ := he.symm ▸ hx
        exact hfx μ (Module.End.mem_eigenspace_iff.mp hx'.2)
      have hne : W ⊓ f.eigenspace μ ≠ ⊥ := by
        intro hb
        have hm : (w : V) ∈ W ⊓ f.eigenspace μ :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hwe⟩
        rw [hb] at hm
        exact hw0 ((Submodule.mem_bot k).mp hm)
      have hinv' : ∀ g ∈ S, ∀ y ∈ W ⊓ f.eigenspace μ, g y ∈ W ⊓ f.eigenspace μ := by
        intro g hg y hy
        refine ⟨hinv g hg y hy.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 : f y = μ • y := Module.End.mem_eigenspace_iff.mp hy.2
        have h2 : f (g y) = g (f y) := LinearMap.congr_fun (hS f hf g hg) y
        rw [h2, h1, map_smul]
      obtain ⟨v, hv, hv0, hv'⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hinv'
      exact ⟨v, hv.1, hv0, hv'⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonField
section
open TensorProduct in
private theorem UpperTheory.Reformulated.B.Qe15.compositum (K κ₁ κ₂ : Type) [Field K] [Field κ₁] [Field κ₂]
    [Algebra K κ₁] [Algebra K κ₂] :
    ∃ (κ : Type) (_ : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ),
      ∀ x : K, j₁ (algebraMap K κ₁ x) = j₂ (algebraMap K κ₂ x) := by
  haveI : Nontrivial (κ₁ ⊗[K] κ₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (κ₁ ⊗[K] κ₂)
  refine ⟨(κ₁ ⊗[K] κ₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom,
    (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂).toRingHom, fun x => ?_⟩
  change Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeLeft : κ₁ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₁ x)) =
    Ideal.Quotient.mk m
      ((Algebra.TensorProduct.includeRight : κ₂ →ₐ[K] κ₁ ⊗[K] κ₂) (algebraMap K κ₂ x))
  rw [AlgHom.commutes, AlgHom.commutes]

theorem UpperTheory.Reformulated.B.Qe15.common_field :
    ∀ (B κ₁ κ₂ : Type) [inst : CommRing B] [inst_1 : Field κ₁] [inst_2 : Field κ₂]
    (f₁ : B →+* κ₁) (f₂ : B →+* κ₂),
    RingHom.ker f₁ = RingHom.ker f₂ →
      ∃ (κ : Type) (x : Field κ) (j₁ : κ₁ →+* κ) (j₂ : κ₂ →+* κ), j₁.comp f₁ = j₂.comp f₂ := by
  intro B κ₁ κ₂ _ _ _ f₁ f₂ h
  let D := B ⧸ RingHom.ker f₁
  haveI : (RingHom.ker f₁).IsPrime := RingHom.ker_isPrime f₁
  haveI : IsDomain D := Ideal.Quotient.isDomain _
  let g₁ : D →+* κ₁ := RingHom.kerLift f₁
  have hg₁ : Function.Injective g₁ := RingHom.kerLift_injective f₁
  let g₂ : D →+* κ₂ := (RingHom.kerLift f₂).comp (Ideal.quotEquivOfEq h).toRingHom
  have hg₂ : Function.Injective g₂ :=
    (RingHom.kerLift_injective f₂).comp (Ideal.quotEquivOfEq h).injective
  let K := FractionRing D
  letI : Algebra K κ₁ := (IsFractionRing.lift (K := K) hg₁).toAlgebra
  letI : Algebra K κ₂ := (IsFractionRing.lift (K := K) hg₂).toAlgebra
  have e₁ : ∀ b : B, algebraMap K κ₁ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₁ b := fun b =>
    (IsFractionRing.lift_algebraMap hg₁ _).trans (RingHom.kerLift_mk f₁ b)
  have e₂ : ∀ b : B, algebraMap K κ₂ (algebraMap D K (Ideal.Quotient.mk _ b)) = f₂ b := fun b =>
    (IsFractionRing.lift_algebraMap hg₂ _).trans (RingHom.kerLift_mk f₂ b)
  obtain ⟨κ, _, j₁, j₂, hj⟩ := UpperTheory.Reformulated.B.Qe15.compositum K κ₁ κ₂
  refine ⟨κ, inferInstance, j₁, j₂, RingHom.ext fun b => ?_⟩
  rw [RingHom.comp_apply, RingHom.comp_apply, ← e₁, ← e₂]
  exact hj _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CompactQuotientSubmodule
section
theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ComplementSubspace
section
noncomputable def UpperTheory.Reformulated.B.ComplementSubspace.IsCompl :
    {K : Type} → [Field K] → {n r : ℕ} → Matrix (Fin r) (Fin n) K → Matrix (Fin n) (Fin n) K → Prop :=
    fun {K : Type} [Field K] {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) ↦
      IsUnit a.det ∧ ∀ (i : Fin n) (hi : (↑i : ℕ) < r), a i = c (⟨(↑i : ℕ), hi⟩ : Fin r)

namespace ComplementBasis

private lemma basis_sub {K : Type} [Field K] {n : ℕ} (U : Submodule K (Fin n → K)) :
    ∃ c : Fin (Module.finrank K U) → (Fin n → K),
      LinearIndependent K c ∧ Submodule.span K (Set.range c) = U := by
  let b := Module.finBasis K U
  refine ⟨fun i => (b i : Fin n → K), ?_, ?_⟩
  · exact b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · have : Set.range (fun i => (b i : Fin n → K)) = U.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

end ComplementBasis

open ComplementBasis in
theorem UpperTheory.Reformulated.B.ComplementSubspace.main :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (U : Submodule K (Fin n → K)),
      ∃ (c : Matrix (Fin (Module.finrank K ↥U)) (Fin n) K) (a : Matrix (Fin n) (Fin n) K),
        (LinearIndependent K c ∧ Submodule.span K (Set.range c) = U) ∧ UpperTheory.Reformulated.B.ComplementSubspace.IsCompl c a := by
  intro K _ n U
  obtain ⟨c, hcli, hcsp⟩ := basis_sub U
  obtain ⟨W, hUW⟩ := Submodule.exists_isCompl U
  obtain ⟨w, hwli, hwsp⟩ := basis_sub W
  have hrm : Module.finrank K U + Module.finrank K W = n := by
    have := Submodule.finrank_add_eq_of_isCompl hUW
    rw [Module.finrank_fin_fun] at this
    omega
  let a : Matrix (Fin n) (Fin n) K := fun i =>
    if h : (i : ℕ) < Module.finrank K U then c ⟨i, h⟩ else w ⟨(i : ℕ) - Module.finrank K U, by have := i.2; omega⟩
  refine ⟨c, a, ⟨hcli, hcsp⟩, ?_, ?_⟩
  · let e : Fin (Module.finrank K U) ⊕ Fin (Module.finrank K W) ≃ Fin n := finSumFinEquiv.trans (finCongr hrm)
    have hg : LinearIndependent K (Sum.elim c w) := by
      apply LinearIndependent.sum_type hcli hwli
      rw [hcsp, hwsp]; exact hUW.disjoint
    have hae : (fun i => a i) ∘ e = Sum.elim c w := by
      funext x
      rcases x with j | k
      · simp [e, a]
      · simp [e, a]
    have hla : LinearIndependent K (fun i => a i) := by
      rw [← linearIndependent_equiv e, hae]; exact hg
    rw [← Matrix.isUnit_iff_isUnit_det]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp hla
  · intro i hi
    simp [a, hi]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceMulOfUnitFactor
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yza4.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.Yza4.Cg :
    {l : ℕ} → [inst : Fact (Nat.Prime l)] → ℕ → UpperTheory.Reformulated.B.Yza4.Qbar l → UpperTheory.Reformulated.B.Yza4.Qbar l → Prop :=
    fun {l : ℕ} [Fact (Nat.Prime l)] (n : ℕ) (a b : UpperTheory.Reformulated.B.Yza4.Qbar l) ↦
      ‖a - b‖ ≤ ‖(↑l : UpperTheory.Reformulated.B.Yza4.Qbar l) ^ n‖

theorem UpperTheory.Reformulated.B.Yza4.congruence_mul_of_unit_factor :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {n : ℕ} {P h un D : UpperTheory.Reformulated.B.Yza4.Qbar l},
      UpperTheory.Reformulated.B.Yza4.Cg n (P * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) →
        UpperTheory.Reformulated.B.Yza4.Cg n P (un * D) →
          ‖un‖ = (1 : ℝ) → ‖h‖ ≤ (1 : ℝ) → UpperTheory.Reformulated.B.Yza4.Cg n (D * h) (0 : UpperTheory.Reformulated.B.Yza4.Qbar l) := by
  intro l _ n P h un D h1 h2 hu hh
  unfold UpperTheory.Reformulated.B.Yza4.Cg at *
  rw [sub_zero] at h1 ⊢
  set c : ℝ := ‖(↑l : PadicAlgCl l) ^ n‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hmul : ∀ a b : PadicAlgCl l, ‖a * b‖ = ‖a‖ * ‖b‖ := fun a b => norm_mul a b
  have key : un * (D * h) = P * h + (un * D - P) * h := by ring
  have h3 : ‖(un * D - P) * h‖ ≤ c := by
    rw [hmul, norm_sub_rev]
    calc ‖P - un * D‖ * ‖h‖ ≤ c * 1 := mul_le_mul h2 hh (norm_nonneg _) hc0
      _ = c := mul_one c
  have h4 : ‖un * (D * h)‖ ≤ c := by
    rw [key]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans (max_le h1 h3)
  rw [hmul, hu, one_mul] at h4
  exact h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CongruenceSubgroupEventually
section
open Filter Topology ValuativeRel

private theorem small_powers {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (V : Set k) (hV : V ∈ nhds (0 : k)) :
    ∀ᶠ c : ℕ in atTop, ∀ x ∈ IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c,
      (x : k) ∈ V := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hV
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(valuation k).integer
  have hlt : valuation k (π : k) < 1 := by
    refine lt_of_le_of_ne π.2 fun h => hπ.not_isUnit ?_
    exact (Valuation.integer.integers (valuation k)).isUnit_of_one' h
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop N] with c hc x hx
  have hx' := Ideal.pow_le_pow_right hc hx
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx'
  obtain ⟨a, rfl⟩ := hx'
  apply hs
  have ha : valuation k (a : k) ≤ 1 := a.2
  change valuation k ((a : k) * (π : k) ^ N) < γ
  rw [map_mul, map_pow]
  calc _ ≤ 1 * valuation k (π : k) ^ N := by gcongr
    _ < γ := by simpa using hN

private theorem entry_mem {k : Type} [Field k] [ValuativeRel k] {n : ℕ}
    (I : Ideal ↥(valuation k).integer) (g : GL (Fin n) k)
    (hg : g ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker) (i j : Fin n) :
    ∃ x ∈ I, (x : k) = (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I) h = 1 := hh
  have h2 : Ideal.Quotient.mk I ((h : Matrix (Fin n) (Fin n) _) i j)
      = (1 : Matrix (Fin n) (Fin n) (_ ⧸ I)) i j :=
    by
      have h4 := Units.ext_iff.mp h1
      exact congrFun (congrFun h4 i) j
  refine ⟨(h : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) _) i j, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · have h3 : ((Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k) h :
        GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        = (((h : Matrix (Fin n) (Fin n) ↥(valuation k).integer) i j : _) : k) := rfl
    rw [h3]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private theorem tendsto_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {α : Type} (L : Filter α) (c : α → ℕ)
    (hc : Tendsto c L atTop) (g : α → GL (Fin n) k)
    (hg : ∀ᶠ a in L, g a ∈ Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c a))).ker) :
    Tendsto (fun a => (g a : Matrix (Fin n) (Fin n) k)) L (nhds 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [← tendsto_sub_nhds_zero_iff]
  refine tendsto_def.mpr fun V hV => ?_
  filter_upwards [hg, hc.eventually (small_powers V hV)] with a ha hs
  obtain ⟨x, hx, e⟩ := entry_mem _ _ ha i j
  have := hs x hx
  rwa [e] at this

theorem UpperTheory.congruence_subgroup_eventually :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) →
        ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∀ g : GL (Fin n) k, g ∈ Subgroup.map (Matrix.GeneralLinearGroup.map (algebraMap (↥(ValuativeRel.valuation k).integer) k))
          (Matrix.GeneralLinearGroup.map (n := Fin n)
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation k).integer ^ c))).ker → g ∈ U := by
  intro k _ _ _ _ n U hU
  let K : ℕ → Subgroup (GL (Fin n) k) := fun c => Subgroup.map
      (Matrix.GeneralLinearGroup.map (algebraMap (↥(valuation k).integer) k))
      (Matrix.GeneralLinearGroup.map (n := Fin n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(valuation k).integer ^ c))).ker
  let L : Filter (ℕ × GL (Fin n) k) := comap Prod.fst atTop ⊓ 𝓟 {p | p.2 ∈ K p.1}
  have hc : Tendsto Prod.fst L atTop := tendsto_comap.mono_left inf_le_left
  have hK : ∀ᶠ p in L, p.2 ∈ K p.1 := mem_inf_of_right (mem_principal_self _)
  have h1 := tendsto_val L Prod.fst hc Prod.snd hK
  have h2 := tendsto_val L Prod.fst hc (fun p => p.2⁻¹) (hK.mono fun p hp => (K p.1).inv_mem hp)
  have h : Tendsto Prod.snd L (nhds (1 : GL (Fin n) k)) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds h1 ?_
    exact (MulOpposite.continuous_op.tendsto _).comp h2
  have h3 : ∀ᶠ p in L, p.2 ∈ U := h hU
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at h3
  obtain ⟨c₀, h₀⟩ := h3
  exact ⟨c₀, fun c hc g hg => h₀ c hc (c, g) rfl hg⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSquare
section
theorem UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq :
    ∀ {d : ℕ},
    (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith [mul_comm z.im z.re]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso
      rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSq
section
theorem UpperTheory.Reformulated.B.Qh56.conj_of_sq :
    ∀ {w : ℂ} {q : ℕ},
    (0 : ℕ) < q → w ^ (2 : ℕ) = (↑q : ℂ) → (starRingEnd ℂ : ℂ → ℂ) w = w := by
  intro w q _ h
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hs.symm) with hw | hw
  · rw [hw, Complex.conj_ofReal]
  · rw [hw, map_neg, Complex.conj_ofReal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSqNeg
section
theorem UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg :
    ∀ {t : ℂ} {r : ℝ},
    r < (0 : ℝ) → t ^ (2 : ℕ) = (↑r : ℂ) → (starRingEnd ℂ : ℂ → ℂ) t = -t := by
  intro t r hr h
  have h1 : t.re * t.re - t.im * t.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : t.re * t.im + t.im * t.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : t.re = 0 := by
    have hm : t.re * t.im = 0 := by linarith [mul_comm t.im t.re]
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at h1
      nlinarith [mul_self_nonneg t.re]
  apply Complex.ext
  · simp [h3]
  · simp
end

