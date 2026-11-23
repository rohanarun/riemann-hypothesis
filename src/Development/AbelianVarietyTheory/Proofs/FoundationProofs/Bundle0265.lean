module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TransLattice

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem_of_mem_span (T : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (T : Set V)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ T := by
  first
  | exact @_root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanScalarMembership.exists_smul_mem_of_mem_span ..)

theorem exists_smul_mem_of_fg (T A : Submodule (𝓞 K) V) (hA : A.FG)
    (hx : ∀ x ∈ A, x ∈ Submodule.span K (T : Set V)) :
    ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ T := by
  classical
  obtain ⟨G, rfl⟩ := hA
  have h1 : ∀ x : G, ∃ s : 𝓞 K, s ≠ 0 ∧ s • (x : V) ∈ T := fun x =>
    exists_smul_mem_of_mem_span T (hx x (Submodule.subset_span x.2))
  choose s hs hsT using h1
  refine ⟨∏ x, s x, Finset.prod_ne_zero_iff.mpr fun x _ => hs x, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx⟩ : G)), mul_smul]
    exact T.smul_mem _ (hsT ⟨x, hx⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact T.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact T.smul_mem _ hx


omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem mem_of_forall_mem_locP (T : Submodule (𝓞 K) V) {x : V}
    (hx : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : x ∈ T := by
  let I : Ideal (𝓞 K) := T.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    obtain ⟨s, hs, hsx⟩ := hx ⟨m, hm.isPrime, hm0⟩
    exact hs (hIm (show s ∈ I from hsx))
  have : (1 : 𝓞 K) ∈ I := by rw [hI]; trivial
  simpa [I] using this

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem locP_le_of_smul_mem (w : HeightOneSpectrum (𝓞 K)) {A B : Submodule (𝓞 K) V} {t : 𝓞 K}
    (ht : t ∉ w.asIdeal) (h : ∀ x ∈ A, t • x ∈ B) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B := by
  rintro x ⟨s, hs, hx⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [mul_smul]
  exact h _ hx

omit [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem mul_smul_mem (A : Submodule (𝓞 K) V) (a : 𝓞 K) {b : 𝓞 K} {x : V} (h : b • x ∈ A) : (a * b) • x ∈ A := by
  rw [mul_smul]; exact A.smul_mem _ h

omit [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem smul_smul_mem_comm (A : Submodule (𝓞 K) V) {a b : 𝓞 K} {x : V} (h : a • b • x ∈ A) : b • a • x ∈ A := by
  rwa [smul_comm]

end General

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem colLat_one_fg : (colLat (1 : GL (Fin n) K)).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat_one : Submodule.span K (colLat (1 : GL (Fin n) K) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨j, ?_⟩
  funext a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_isBasisAt_one (M : ι → Submodule (𝓞 K) (Fin n → K))
    (hM : ∀ τ, Submodule.IsFullLattice K (M τ)) :
    ∃ t : 𝓞 K, t ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), t ∉ w.asIdeal → ∀ τ, IsBasisAt w (M τ) 1 := by
  classical
  have h1 : ∀ τ, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ M τ, s • x ∈ colLat (1 : GL (Fin n) K) := fun τ =>
    exists_smul_mem_of_fg _ _ (hM τ).toIsLattice.fg fun x _ => by rw [span_colLat_one]; trivial
  have h2 : ∀ τ, ∃ s : 𝓞 K, s ≠ 0 ∧ ∀ x ∈ colLat (1 : GL (Fin n) K), s • x ∈ M τ := fun τ =>
    exists_smul_mem_of_fg _ _ colLat_one_fg fun x _ => by rw [(hM τ).span_eq_top]; trivial
  choose s hs hsM using h1
  choose s' hs' hsM' using h2
  refine ⟨∏ τ, (s τ * s' τ), Finset.prod_ne_zero_iff.mpr fun τ _ => mul_ne_zero (hs τ) (hs' τ), ?_⟩
  intro w hw τ
  have hd : s τ * s' τ ∉ w.asIdeal := fun h =>
    hw (w.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) h)
  exact le_antisymm
    (locP_le_of_smul_mem w (fun h => hd (w.asIdeal.mul_mem_right _ h)) (hsM τ))
    (locP_le_of_smul_mem w (fun h => hd (w.asIdeal.mul_mem_left _ h)) (hsM' τ))

theorem transLat_fg (hB : BasisAtEx) (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (hT : T.FG)
    (hsp : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsFullLattice K (M τ)) :
    (transLat lam T M).FG := by
  classical
  obtain ⟨t, ht, htw⟩ := exists_isBasisAt_one M hM
  have hmem : ∀ F ∈ transLat lam T M, ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K),
      (∀ τ, IsBasisAt w (M τ) (B τ)) → actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
    intro F hF w B hB
    simp only [transLat, Submodule.mem_iInf] at hF
    exact hF w B hB
  have hloc : ∀ w : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ≠ 0 ∧
      ∀ F ∈ transLat lam T M, s • F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
    intro w
    choose B hBw using fun τ => hB K n (M τ) (hM τ) w
    obtain ⟨s, hs, hsT⟩ := exists_smul_mem_of_fg T (T.map ((actP lam B).restrictScalars (𝓞 K))) (hT.map _) (by
      rintro _ ⟨x, hx, rfl⟩
      rw [hsp]
      exact polyAction_mem_VV lam B (hsp ▸ Submodule.subset_span hx))
    refine ⟨s, hs, fun F hF => ?_⟩
    obtain ⟨u, hu, huF⟩ := hmem F hF w B hBw
    refine ⟨u, hu, ?_⟩
    have h := hsT _ ⟨_, huF, rfl⟩
    rw [map_smul, LinearMap.restrictScalars_apply, ← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h
    exact smul_smul_mem_comm T h
  choose s hs hsF using hloc
  have hfin : {w : HeightOneSpectrum (𝓞 K) | w.asIdeal ∣ Ideal.span {t}}.Finite :=
    Ideal.finite_factors (by simpa using ht)
  set c : 𝓞 K := ∏ w ∈ hfin.toFinset, s w with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hs w
  have hcT : ∀ F ∈ transLat lam T M, c • F ∈ T := by
    intro F hF
    refine mem_of_forall_mem_locP T fun w => ?_
    by_cases hw : t ∈ w.asIdeal
    · have hw' : w ∈ hfin.toFinset := by
        simpa [Ideal.dvd_span_singleton] using hw
      rw [hc, ← Finset.prod_erase_mul _ _ hw']
      exact mul_smul_mem _ _ (hsF w F hF)
    · have h := hmem F hF w 1 (htw w hw)
      rw [inv_one, polyAction_one₂] at h
      exact Submodule.smul_mem _ _ h
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) (Pol K ι n) c) := by
    intro x y hxy
    have h : algebraMap (𝓞 K) K c • x = algebraMap (𝓞 K) K c • y := by
      rw [algebraMap_smul, algebraMap_smul]; exact hxy
    refine smul_right_injective _ ?_ h
    intro h0
    exact hc0 ((IsFractionRing.injective (𝓞 K) K) (by rw [h0, map_zero]))
  refine Submodule.fg_of_fg_map_injective _ hinj (hT.of_le ?_)
  rintro _ ⟨F, hF, rfl⟩
  exact hcT F hF

theorem transLat_isLattice (hB : BasisAtEx) (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (hT : T.FG)
    (hsp : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsFullLattice K (M τ))
    (hloc : ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K))) :
    Submodule.IsFullLattice K ((transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))) := by
  classical
  let L := (transLat lam T M).comap ((VV K lam).subtype.restrictScalars (𝓞 K))
  have hL : Submodule.IsLattice K L := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective ((VV K lam).subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    exact (transLat_fg hB lam T hT hsp M hM).of_le (Submodule.map_comap_le _ _)
  refine { toIsLattice := hL, span_eq_top := ?_ }
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩
  choose B hBw using fun τ => hB K n (M τ) (hM τ) w
  let Q := (Submodule.span K (L : Set (VV K lam))).map (VV K lam).subtype
  have hTQ : ∀ y ∈ T, actP lam B y ∈ Q := by
    intro y hy
    have hyV : y ∈ VV K lam := hsp ▸ Submodule.subset_span hy
    have hyLoc : actP lam B y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) := by
      rw [hloc w B hBw]
      exact ⟨y, ⟨1, by simp, by simpa using hy⟩, rfl⟩
    obtain ⟨s, hs, hsY⟩ := hyLoc
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro hzero
      have hs0 : s = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using hzero)
      exact hs (hs0 ▸ w.asIdeal.zero_mem)
    have hyBV := polyAction_mem_VV lam B hyV
    have hsQ : algebraMap (𝓞 K) K s • actP lam B y ∈ Q := by
      rw [algebraMap_smul]
      exact ⟨⟨s • actP lam B y, (VV K lam).smul_mem _ hyBV⟩,
        Submodule.subset_span hsY, rfl⟩
    exact (Q.smul_mem_iff hs0).mp hsQ
  have hspan : VV K lam ≤ Q.comap (actP lam B) := by
    rw [← hsp, Submodule.span_le]
    exact hTQ
  apply eq_top_iff.mpr
  intro x _
  have hx : actP lam B⁻¹ (x : Pol K ι n) ∈ VV K lam := polyAction_mem_VV lam B⁻¹ x.2
  have h := hspan hx
  change actP lam B (actP lam B⁻¹ (x : Pol K ι n)) ∈ Q at h
  rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h
  obtain ⟨z, hz, heq⟩ := h
  have : z = x := Subtype.ext heq
  change x ∈ Submodule.span K (L : Set (VV K lam))
  simpa [this] using hz

theorem nabDelLattice : NabDelLattice := by
  intro K _ _ ι _ n lam M hM
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.stdWeylLattices_fg_and_span_coeffSpace K ι n lam
  exact ⟨transLat_isLattice GlobalTheory.T.lattice_has_basis_at_every_finite_place lam _ h1 h3 M hM
      fun w B hB => (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB).1,
    transLat_isLattice GlobalTheory.T.lattice_has_basis_at_every_finite_place lam _ h2 h4 M hM
      fun w B hB => (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB).2⟩

end GlobalTheory.TransLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RelIndexImageOneSubComplexLinearEquiv
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.ThetaCovIndex

open GlobalTheory.ThetaInter Module

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]


omit [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in
theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ W) {L₁ L₂ : AddSubgroup W}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem exists_basis_finrank {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ b : Basis (Fin (finrank ℝ W)) ℝ W, (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology A.toIntSubmodule := hA
  have : IsZLattice ℝ A.toIntSubmodule := ⟨hsp⟩
  let b₀ := Module.finBasisOfFinrankEq ℤ A.toIntSubmodule (ZLattice.rank ℝ A.toIntSubmodule)
  refine ⟨b₀.ofZLatticeBasis ℝ A.toIntSubmodule, ?_⟩
  rw [Basis.ofZLatticeBasis_span]
  rfl

theorem relIndex_map {A B : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (f : W ≃ₗ[ℝ] W) (hB : B ≤ A)
    (hf : B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ≤ A) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ B, m • x = f y) :
    B.relIndex A ≠ 0 ∧ ((B.map (f : W →ₗ[ℝ] W).toAddMonoidHom).relIndex A : ℝ) =
      B.relIndex A * |LinearMap.det (f : W →ₗ[ℝ] W)| := by
  have hBd : DiscreteTopology B := DiscreteTopology.of_subset hA hB
  have hBs : Submodule.span ℝ (B : Set W) = ⊤ := by
    have h1 : (Submodule.span ℝ (B : Set W)).map (f : W →ₗ[ℝ] W) = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      intro x hxA
      obtain ⟨y, hy, e⟩ := hx x hxA
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      refine ⟨(m : ℝ)⁻¹ • y, Submodule.smul_mem _ _ (Submodule.subset_span hy), ?_⟩
      simp only [LinearEquiv.coe_coe, map_smul]
      rw [← e, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, e⟩ := (h1.ge (Submodule.mem_top (x := f x)))
    exact f.injective e ▸ hy
  obtain ⟨a, ha⟩ := exists_basis_finrank hA hsp
  obtain ⟨b, hb⟩ := exists_basis_finrank hBd hBs
  have hb₁ : (Submodule.span ℤ (Set.range (b.map f))).toAddSubgroup =
      B.map (f : W →ₗ[ℝ] W).toAddMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    have : f x ∈ B.map (f : W →ₗ[ℝ] W).toAddMonoidHom ↔ x ∈ B :=
      AddSubgroup.mem_map_iff_mem (f := (f : W →ₗ[ℝ] W).toAddMonoidHom) f.injective
    rw [this, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  have e1 := relIndex_eq_abs_det b a hb ha hB
  generalize B.map (f : W →ₗ[ℝ] W).toAddMonoidHom = C at hf hb₁ ⊢
  have e2 := relIndex_eq_abs_det (b.map f) a hb₁ ha hf
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at e1
    exact IsUnit.ne_zero (a.isUnit_det b) e1
  · rw [e2, e1, ← abs_mul, mul_comm, ← a.det_comp (f : W →ₗ[ℝ] W) b, Basis.coe_map]
    rfl

end General

theorem relIndex_image_one_sub_complexLinearEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {A A₁ : AddSubgroup W} (t₁ : DiscreteTopology A) (s₁ : Submodule.span ℝ (A : Set W) = ⊤)
    (u : W ≃ₗ[ℂ] W) (hA : ∀ x, x ∈ A ↔ u x ∈ A₁)
    (hdet : LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W)) ≠ 0) {m : ℕ} (hm : 0 < m)
    (hx : ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) :
    A₁.relIndex A ≠ 0 ∧
      (((A.map (LinearMap.id - (u.symm : W →ₗ[ℂ] W)).toAddMonoidHom).relIndex A : ℕ) : ℝ) =
        (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : W →ₗ[ℂ] W))‖ ^ 2 := by
  set g : W →ₗ[ℂ] W := LinearMap.id - (u.symm : W →ₗ[ℂ] W) with hg
  have hgy : ∀ y, g y = y - u.symm y := fun y => rfl
  let f : W ≃ₗ[ℝ] W := (LinearMap.equivOfDetNeZero g hdet).restrictScalars ℝ
  have hfg : (f : W →ₗ[ℝ] W) = g.restrictScalars ℝ := by
    ext1 y; simp [f]
  have hfy : ∀ y, f y = y - u.symm y := fun y => congrArg (fun φ => φ y) hfg
  have hA' : ∀ y, u.symm y ∈ A ↔ y ∈ A₁ := fun y => by rw [hA, u.apply_symm_apply]
  have hinf : (A₁ ⊓ A).map (f : W →ₗ[ℝ] W).toAddMonoidHom = A.map g.toAddMonoidHom ⊓ A := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy₁, hy⟩, rfl⟩
      refine ⟨⟨y, hy, (hfy y).symm⟩, ?_⟩
      change f y ∈ A
      rw [hfy]
      exact A.sub_mem hy ((hA' y).2 hy₁)
    · rintro ⟨⟨y, hy, rfl⟩, h2⟩
      refine ⟨y, ⟨(hA' y).1 ?_, hy⟩, hfy y⟩
      have h3 : y - u.symm y ∈ A := h2
      simpa using A.sub_mem hy h3
  have key := relIndex_map (B := A₁ ⊓ A) t₁ s₁ f inf_le_right (hinf.le.trans inf_le_right) hm
    fun x hxA => by
      obtain ⟨y, hy, hy', e⟩ := hx x hxA
      exact ⟨y, ⟨(hA' y).1 hy', hy⟩, e.trans (hfy y).symm⟩
  rw [hinf, AddSubgroup.inf_relIndex_right, AddSubgroup.inf_relIndex_right, hfg,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity)] at key
  exact key

theorem relIndex_one_sub : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → A₁.relIndex A ≠ 0 ∧ ((((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A : ℕ) : ℝ)) = (A₁.relIndex A : ℝ) * ‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ ^ 2 := by
  intro D cc δ hc N N' A A₁ h₁ _ u _ hA hdet ⟨m, hm, hx⟩
  obtain ⟨f₁, s₁, d₁, -⟩ := klat_facts hc h₁
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  exact relIndex_image_one_sub_complexLinearEquiv t₁ s₁ u hA hdet hm hx

end GlobalTheory.ThetaCovIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTransport
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaIso

open MeasureTheory GlobalTheory.ThetaInter

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

theorem mean_transport {A A₁ : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (e : W ≃ₗ[ℝ] W) (he : ∀ x, x ∈ A ↔ e x ∈ A₁)
    {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A₁ (fun z => f (e.symm z)) = mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  have hb₁ : (Submodule.span ℤ (Set.range (b.map e))).toAddSubgroup = A₁ := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  rw [mean_eq μ b hb hf, mean_eq μ (b.map e) hb₁ fun x hx z => by
    rw [map_add (f := _), hf _ ((he _).2 (by simpa using hx))]]
  let ec : W ≃L[ℝ] W := e.toContinuousLinearEquiv
  let em : W ≃ᵐ W := ec.toHomeomorph.toMeasurableEquiv
  have hpre : ZSpan.fundamentalDomain b = em ⁻¹' ZSpan.fundamentalDomain (b.map e) := by
    ext x
    change _ ↔ e x ∈ ZSpan.fundamentalDomain (b.map e)
    simp [ZSpan.mem_fundamentalDomain]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) μ
  have hc0 : Measure.addHaarScalarFactor (μ.map em) μ ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' ZSpan.fundamentalDomain (b.map e), f z ∂μ
      = ⨍ z in ZSpan.fundamentalDomain (b.map e), f (e.symm z) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    congr 2
    funext z
    exact congrArg f (e.symm_apply_apply z).symm
  rw [hpre, h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) μ : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

theorem mean_pos {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) {f : W → ℝ} (hc : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) {z₀ : W} (hz : f z₀ ≠ 0) : 0 < mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  rw [mean_eq μ b hb hf, setAverage_eq, smul_eq_mul]
  have hbd := ZSpan.fundamentalDomain_isBounded b
  have hI : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
    (hc.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure
  have hsupp : 0 < μ (Function.support f ∩ ZSpan.fundamentalDomain b) := by
    rw [pos_iff_ne_zero]
    intro h
    have hfd := ZSpan.isAddFundamentalDomain' b μ
    have hz0 := hfd.measure_zero_of_invariant (Function.support f) (fun g => ?_) h
    · exact (hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' hz0
    · ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f (-(g : W) + y) ≠ 0 ↔ f y ≠ 0
      rw [add_comm, hf _ (A.neg_mem (hb.le g.2))]
  refine mul_pos (inv_pos.2 ?_) ?_
  · exact ENNReal.toReal_pos (hsupp.trans_le (measure_mono Set.inter_subset_right)).ne' hbd.measure_lt_top.ne
  · exact (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI).2 hsupp

end General

theorem theta_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) ∈ ThSp D (tor0 D cc δ) A₁ ∧ normSq D (tor0 D cc δ) A₁ (fun z => th (u.symm z)) = normSq D (tor0 D cc δ) A th ∧ (th ≠ 0 → 0 < normSq D (tor0 D cc δ) A th) := by
  intro D cc δ hc N N' A A₁ h₁ _ u hu hA th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A := hth.2
  have hper := fun x hx z => rho_add_of_fixed hH c₁ hF (x := x) hx z
  refine ⟨⟨hth.1.comp u.symm.toContinuousLinearEquiv.differentiable, fun x hx z => ?_⟩, ?_, fun hne => ?_⟩
  · obtain ⟨x, rfl⟩ := u.surjective x
    obtain ⟨z, rfl⟩ := u.surjective z
    have := hth.2 x ((hA x).2 hx) z
    simp only [al, U, hu, ← map_add (f := _), LinearEquiv.symm_apply_apply] at this ⊢
    exact this
  · have := mean_transport volume t₁ s₁ (u.restrictScalars ℝ) hA hper
    refine Eq.trans ?_ this
    change mean volume A₁ (rho (sesqOf D (tor0 D cc δ) N N') fun z => th (u.symm z)) = _
    congr 1
    funext z
    obtain ⟨z, rfl⟩ := u.surjective z
    change ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u z) (u z)).re) =
      ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u.symm (u z)) (u.symm (u z))).re)
    rw [hu, u.symm_apply_apply]
  · obtain ⟨z₀, hz⟩ := Function.ne_iff.1 hne
    refine mean_pos (f := rho (sesqOf D (tor0 D cc δ) N N') th) volume t₁ s₁ (continuous_rho hH hth.1.continuous) (fun z => by unfold rho; positivity) hper
      (z₀ := z₀) ?_
    have : 0 < ‖th z₀‖ := norm_pos_iff.2 hz
    unfold rho
    positivity

end GlobalTheory.ThetaIso
end

