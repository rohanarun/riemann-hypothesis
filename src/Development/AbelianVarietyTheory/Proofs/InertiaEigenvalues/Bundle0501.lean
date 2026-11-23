module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem (h i) (h' i)
  | smul o w _ h =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add (f := _)]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_uniformizer_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨?_, ?_⟩
  · unfold BK.ρ₀
    exact NNReal.rpow_pos (by positivity)
  · unfold BK.ρ₀
    exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
      have : (0:ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith)

theorem linDisjoint_disc (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (sA : bk.S →+* A) (ι : Type) (TB : TopBasis sA bk.J ι) (j : bk.DS bk.ρ₀ →+* Disc l (sA X) bk.ρ₀)
    (hj : IsDiscMap (l := _) (u := _) (ρ := _) sA j) (x y : A) (f g : bk.DS bk.ρ₀) (hg : g ≠ 0) (hy : y ≠ 0)
    (h : toDisc l (sA X) bk.ρ₀ x * j g = toDisc l (sA X) bk.ρ₀ y * j f) :
    ∃ δ a : bk.S, δ ≠ 0 ∧ sA δ * x = sA a * y := by
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_uniformizer_radius_pos_lt_one bk
  obtain ⟨cD, hc1, hc2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A sA ι TB bk.ρ₀ hρ0 hρ1 j hj
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hH : IsHausdorff bk.J bk.S := inferInstance
  obtain ⟨hz, -⟩ := GlobalTheory.BSP.TopBasis.basic_facts bk.S A sA bk.J ι TB hH
  have hinj : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) :=
    (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) bk.ρ₀ hρ0 hρ1).1
  have hmul := _root_.GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ hρ0 hρ1

  have key : ∀ i, g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i x) = f * toDisc l (X : bk.S) bk.ρ₀ (TB.c i y) := by
    intro i
    have e := congrArg (cD i) h
    rw [mul_comm, mul_comm (toDisc l (sA X) bk.ρ₀ y), hc2, hc2, hc1, hc1] at e
    exact e
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, TB.c i₀ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy (hz y hc)
  refine ⟨TB.c i₀ y, TB.c i₀ x, hi₀, ?_⟩
  rw [← sub_eq_zero]
  apply hz
  intro i
  rw [map_sub, TB.c_mul, TB.c_mul]
  apply hinj
  rw [map_zero]
  have h0 : g * toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y * TB.c i x - TB.c i₀ x * TB.c i y) = 0 := by
    rw [map_sub, map_mul, map_mul, mul_sub]
    have e1 := key i
    have e2 := key i₀
    linear_combination (toDisc l (X : bk.S) bk.ρ₀ (TB.c i₀ y)) * e1 - (toDisc l (X : bk.S) bk.ρ₀ (TB.c i y)) * e2
  have hn := congrArg norm h0
  rw [hmul, norm_zero, mul_eq_zero] at hn
  rcases hn with hn | hn
  · exact absurd (norm_eq_zero.1 hn) hg
  · exact norm_eq_zero.1 hn

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecomposition
section
noncomputable section

namespace GlobalTheory.AmbBlockDecomp

open NumberField IsDedekindDomain _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem sum_ind_block (t : ℕ) (a : ℤ) :
    (∑ c ∈ Finset.Icc 1 t, (if a = (c : ℤ) - 1 then (1 : ℤ) else 0)) =
      if 0 ≤ a ∧ a < t then 1 else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.toNat, (Int.toNat_of_nonneg h.1).symm⟩
    rw [Finset.sum_eq_single (n + 1)]
    · simp
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_Icc]
      omega
  · apply Finset.sum_eq_zero
    intro c hc
    rw [Finset.mem_Icc] at hc
    rw [if_neg]
    omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  intro D i r ρ π hD _ _ _ w hw C τ
  have hB : GlobalTheory.PtCore.BlockE D i r ρ π :=
    GlobalTheory.BlockEnl.blockE_of_isBlockSum D i r ρ π (by
      obtain ⟨e, he⟩ := hD
      exact ⟨e, fun g u => he g u⟩)
  obtain ⟨h1, h2⟩ := hB w hw C.LL C.le τ
  have hl : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)),
      TruncatedSeriesCountingIdentities.locC C M = GlobalTheory.PtCore.locE D i w hw C.LL C.le M := fun _ => rfl
  simp only [hl]
  refine ⟨fun a => ?_, fun c hc a => h2 c hc a⟩
  rw [h1 a]
  congr 1
  rw [Finset.sum_congr rfl (fun c hc => h2 c hc a)]
  exact (sum_ind_block D.R.t a).symm

end GlobalTheory.AmbBlockDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisCoboundaryEventuallyMemPrimePowLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleCont

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]

theorem twact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem twact_incl (T : LocLat G ℚ_[l] K O) (h : GQ l) (g : G) (z : TW (OCr l O) T) :
    TWact (galOB O h) T g (TWincl (toOB l O) T z) = TWincl (toOB l O) T (TWact (galOCr O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TWincl, TensorProduct.map_tmul, galOB_toOB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem natCast_pow_smul {O K : Type} [CommRing O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K]
    (T : LocLat G ℚ_[l] K O) (k : ℕ) (v : T.V) : ((l : O) ^ k) • v = ((l : K) ^ k) • v := by
  rw [← algebraMap_smul K, map_pow, map_natCast]

theorem main_gen {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (s : G →* GQ l) (hs : Continuous s) (T : LocLat G ℚ_[l] K O) (hK : (l : K) ≠ 0)
    (hcont : ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ)
    (hden : ∀ v : T.V, ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : O) ^ n) • v)
    (hmem : ∀ (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) →
      ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y)
    (b : TW (OB l O) T) (c : G → T.V) (hc : IsCobOf s T b c) (m : ℕ) :
    ∀ᶠ g in nhds (1 : G), ∃ x ∈ T.L.T, c g = ((l : O) ^ m) • x := by
  obtain ⟨s0, hs0, β, hβ⟩ := _root_.GlobalTheory.DenomCris.exists_smul_eq_TWincl T b
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.AcrisMonBound.main l (s0 * s0) (by rw [map_mul]; exact mul_ne_zero hs0 hs0)
  set a : Per.Acris l := ainfToAcris l s0 with ha
  set m' := m + C + 1 with hm'
  have h2 : ∀ᶠ g in nhds (1 : G), (l : Per.Acris l) ^ m' ∣ galC (s g) a - a := by
    have h := GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m'
    rw [← map_one s] at h
    exact hs.continuousAt.preimage_mem_nhds h
  filter_upwards [hcont β m', h2] with g ⟨γ, hγ⟩ ⟨w, hw⟩
  obtain ⟨n, x, hxT, hx⟩ := hden (c g)
  have hcob := hc g n ⟨x, hxT⟩ (by show x = _; rw [hx, ← algebraMap_smul K, map_pow, map_natCast])
  have hconv : ∀ (k : ℕ) (v : T.V), ((l : O) ^ k) • v = ((l : K) ^ k) • v := fun k v => by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  set x' : ↥T.L.T := ⟨x, hxT⟩ with hx'
  set ga : Per.Acris l := galC (s g) a with hga
  set σA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] a with hσA
  set gσA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] ga with hgσA
  have hgσA' : galOCr O (s g) σA = gσA := rfl
  set σ : OB l O := toOB l O σA with hσ
  set gσ : OB l O := toOB l O gσA with hgσ
  have hgσ' : galOB O (s g) σ = gσ := by rw [hσ, galOB_toOB, hgσA']
  have hβ' : σ • b = TWincl (toOB l O) T β := hβ
  set gβ := TWact (galOCr O (s g)) T g β with hgβ
  have key1 : gσ • actB s T g b = TWincl (toOB l O) T gβ := by
    rw [actB, ← hgσ', ← twact_smul, hβ', twact_incl]
  have key : (σ * gσ) • ((1 : OB l O) ⊗ₜ[O] x') = TWincl (toOB l O) T (((l : O) ^ n) • (σA • gβ - gσA • β)) := by
    rw [hcob, smul_comm, map_smul, map_sub, twincl_smul, twincl_smul, ← hσ, ← hgσ, smul_sub, mul_smul, key1,
      mul_comm, mul_smul, hβ']
  have hfin : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ X : Per.Acris l, a * a * algebraMap ℤ_[l] (Per.Acris l) (φ x') =
      (l : Per.Acris l) ^ (n + m') * X - (l : Per.Acris l) ^ m' * (a * w * algebraMap ℤ_[l] (Per.Acris l) (φ x')) := by
    intro φ hφ
    obtain ⟨ΦA, ΦB, hA, hB, h1, hN, hI⟩ := _root_.GlobalTheory.exists_coord_acris_bcris T φ hφ
    have hσσ : σ * gσ = (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l a * acrisToBcris l ga) := by
      rw [hσ, hgσ, hσA, hgσA]
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e1 := congrArg ΦB key
    rw [hσσ, hB, h1, hI, hN, map_sub, hA, hA] at e1
    have hΦ : ΦA gβ - ΦA β = (l : Per.Acris l) ^ m' * ΦA γ := by rw [← map_sub, hγ, hN]
    have heq : a * ga * algebraMap ℤ_[l] (Per.Acris l) (φ x') = (l : Per.Acris l) ^ n * (a * ΦA gβ - ga * ΦA β) := by
      have hinj : Function.Injective (acrisToBcris l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
      apply hinj
      have := e1
      simp only [map_mul, AlgHom.commutes] at this ⊢
      exact this
    refine ⟨a * ΦA γ - w * ΦA β, ?_⟩
    linear_combination heq - (a * algebraMap ℤ_[l] (Per.Acris l) (φ x')) * hw + ((l : Per.Acris l) ^ n * a) * hΦ - ((l : Per.Acris l) ^ n * ΦA β) * hw
  have hdiv : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ (n + m) ∣ φ x' := by
    intro φ hφ
    by_cases hz : φ x' = 0
    · rw [hz]; exact dvd_zero _
    have hspec := PadicInt.unitCoeff_spec hz
    suffices hv : n + m ≤ (φ x').valuation by
      rw [hspec]
      exact Dvd.dvd.mul_left (pow_dvd_pow _ hv) _
    by_contra hlt
    push_neg at hlt
    obtain ⟨X, hX⟩ := hfin φ hφ
    set v := (φ x').valuation
    have hzA : algebraMap ℤ_[l] (Per.Acris l) (φ x') =
        algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]) * (l : Per.Acris l) ^ v := by
      conv_lhs => rw [hspec]
      rw [map_mul, map_pow, map_natCast]
    have hd : (l : Per.Acris l) ^ (min (n + m') (m' + v)) ∣ ainfToAcris l (s0 * s0) * algebraMap ℤ_[l] (Per.Acris l) (φ x') := by
      rw [map_mul, ← ha, hX]
      refine Dvd.dvd.sub (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _) ?_
      refine (pow_dvd_pow _ (min_le_right _ _)).trans ?_
      rw [hzA, pow_add]
      exact ⟨a * w * algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]), by ring⟩
    have := hC (φ x') _ hz hd
    omega
  obtain ⟨y, hyT, hy⟩ := hmem x' (n + m) hdiv
  refine ⟨y, hyT, ?_⟩
  have h3 : ((l : K) ^ n) • c g = ((l : K) ^ n) • (((l : O) ^ m) • y) := by
    rw [← hconv, ← hconv, ← mul_smul, ← pow_add]
    exact hx.symm.trans hy
  exact smul_right_injective T.V (pow_ne_zero n hK) h3


set_option maxHeartbeats 800000 in
theorem cont_at_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  intro l _ _ LL T b c hc m
  have hK : (l : ↥LL.1) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] ↥LL.1)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine (main_gen (sQ l) continuous_subtype_val T hK (_root_.GlobalTheory.OCrCont.twact_sub_smul_eventually (sQ l) continuous_subtype_val T ?hT) ?hD
    (_root_.GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd T) b c hc m).mono ?fin
  case fin =>
    rintro g ⟨x, hx, e⟩
    exact ⟨x, hx, e.trans (natCast_pow_smul T m x)⟩
  case hT =>
    intro t ht k
    filter_upwards [_root_.GlobalTheory.BKGal.ContNear.sub_mem_pow_smul_lattice_eventually l LL T t ht k] with g ⟨t', ht', e⟩
    exact ⟨t', ht', e.trans (natCast_pow_smul T k t').symm⟩
  case hD =>
    intro v
    obtain ⟨n, x, hx, e⟩ := _root_.GlobalTheory.TContMul.main l LL T v
    exact ⟨n, x, hx, e.trans (natCast_pow_smul T n v).symm⟩

end GlobalTheory.CocycleCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeToDeRhamEquivariantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.bcrisTensorLattice_to_deRham_equivariant : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (LL : FinExt l) (T : QLat LL) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (g : Gl l) (b : TW (OB l ↥(OL LL)) T), X (actB (sQ l) T g b) = actVdR (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (X b) := by
  exact @GlobalTheory.BKGal.JumpDR.X_equivariant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoQuotientOfDivisibleImageMemStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_quotient_of_divisible_image_mem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  first | exact @GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | exact GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD | (intros; apply GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoReductionsOrthogonalModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  first | exact @GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | exact GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA | (intros; apply GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockAndTorsionExponentBoundsCanonicalHubData
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominatorsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_bounded_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  first | (exact @GlobalTheory.BKLim.beta_bdd_denominators) | (exact GlobalTheory.BKLim.beta_bdd_denominators) | (intros; apply GlobalTheory.BKLim.beta_bdd_denominators  <;> assumption)
end

