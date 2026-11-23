module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0053

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsEigvec
section
open Matrix IsLocalRing Polynomial

private theorem UpperTheory.Reformulated.B.Qf19.exists_eigvec {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (X : Matrix (Fin 3) (Fin 3) R)
    (hu : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b))
    (hm : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R) (a : Fin 3) :
    ∃ (l : R) (v : Fin 3 → R), v a = 1 ∧ (∀ b, b ≠ a → v b ∈ maximalIdeal R) ∧ X *ᵥ v = l • v := by
  have hd : X.map (residue R) = diagonal fun b => residue R (X b b) := by
    ext b c
    by_cases h : b = c
    · subst h; simp
    · rw [diagonal_apply_ne _ h, map_apply, residue_eq_zero_iff]; exact hm b c h
  have hne : ∀ b, b ≠ a → residue R (X a a) - residue R (X b b) ≠ 0 := fun b hb => by
    rw [← map_sub]; exact ((hu a b hb.symm).map (residue R)).ne_zero
  have hP : (∏ b ∈ Finset.univ.erase a, (residue R (X a a) - residue R (X b b))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b hb => hne b (Finset.ne_of_mem_erase hb)
  have hc : X.charpoly.map (residue R) =
      (Polynomial.X - C (residue R (X a a))) *
        ∏ b ∈ Finset.univ.erase a, (Polynomial.X - C (residue R (X b b))) := by
    rw [← Matrix.charpoly_map, hd, Matrix.charpoly_diagonal,
      Finset.mul_prod_erase Finset.univ (fun b => Polynomial.X - C (residue R (X b b))) (Finset.mem_univ a)]
  obtain ⟨l, hl, hla⟩ := HenselianRing.is_henselian (I := maximalIdeal R) X.charpoly X.charpoly_monic (X a a)
    (by
      rw [← residue_eq_zero_iff, ← eval₂_hom, ← eval_map, hc]
      simp)
    (by
      change IsUnit (residue R _)
      rw [← eval₂_hom, ← eval_map, ← derivative_map, hc, isUnit_iff_ne_zero]
      simpa [eval_prod] using hP)
  have hla' : residue R l = residue R (X a a) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hla
  set M : Matrix (Fin 3) (Fin 3) R := scalar (Fin 3) l - X with hM
  have hdet : M.det = 0 := by rw [hM, ← Matrix.eval_charpoly]; exact hl
  have hMd : M.map (residue R) = diagonal fun b => residue R (X a a) - residue R (X b b) := by
    ext b c
    have := congrFun (congrFun hd b) c
    by_cases h : b = c
    · subst h; simp [hM, hla']
    · rw [diagonal_apply_ne _ h] at this ⊢
      simpa [hM, diagonal_apply_ne _ h] using this
  have hadj : ∀ b, residue R (M.adjugate b a) = (diagonal fun i => ∏ j ∈ Finset.univ.erase i,
      (residue R (X a a) - residue R (X j j))) b a := fun b => by
    have := (residue R).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hMd, adjugate_diagonal] at this
    exact congrFun (congrFun this b) a
  have hun : IsUnit (M.adjugate a a) := by
    rw [← residue_ne_zero_iff_isUnit, hadj, diagonal_apply_eq]; exact hP
  obtain ⟨u, hu'⟩ := hun
  have hker : M *ᵥ (fun b => M.adjugate b a) = 0 := by
    ext b
    have := congrFun (congrFun (mul_adjugate M) b) a
    rw [hdet, zero_smul] at this
    exact this
  refine ⟨l, (↑u⁻¹ : R) • fun b => M.adjugate b a, ?_, fun b hb => ?_, ?_⟩
  · simp [← hu']
  · refine Ideal.mul_mem_left _ _ ?_
    rw [← residue_eq_zero_iff, hadj, diagonal_apply_ne _ hb]
  · rw [hM, sub_mulVec, sub_eq_zero] at hker
    rw [mulVec_smul, ← hker, smul_comm l]
    congr 1
    ext b
    simp [mulVec_diagonal, hM]

theorem UpperTheory.Reformulated.B.Qf19.exists_canon :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (X : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) R),
      (∀ (a b : Fin (3 : ℕ)), a ≠ b → IsUnit (X a a - X b b)) →
        (∀ (a b : Fin (3 : ℕ)), a ≠ b → X a b ∈ IsLocalRing.maximalIdeal R) →
          ∃ (h : GL (Fin (3 : ℕ)) R), UpperTheory.V.UnitaryThreeInertia.Canon X h := by
  intro R _ _ _ X hu hm
  choose l v h1 h2 h3 using UpperTheory.Reformulated.B.Qf19.exists_eigvec X hu hm
  set H : Matrix (Fin 3) (Fin 3) R := Matrix.of fun b a => v a b with hH
  have hhat : ∀ a b, (H - 1) a b ∈ maximalIdeal R := fun a b => by
    by_cases h : a = b
    · subst h; simp [hH, h1]
    · simpa [hH, one_apply_ne h] using h2 b a h
  have hmap : (residue R).mapMatrix H = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hhat a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [RingHom.mapMatrix_apply, map_apply, this]
    by_cases h : a = b
    · subst h; simp
    · simp [one_apply_ne h]
  have hdet : IsUnit H.det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, hmap]; simp
  obtain ⟨h, hh⟩ := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hXH : X * H = H * diagonal l := by
    ext b a
    have := congrFun (h3 a) b
    rw [mul_diagonal, mul_comm]
    exact this
  refine ⟨h, ?_, fun a => ?_, ?_⟩
  · intro a b; rw [hh]; exact hhat a b
  · rw [hh]; exact h1 a
  · have : ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal l := by
      rw [Matrix.mul_assoc, hh, hXH, ← hh, ← Matrix.mul_assoc]
      simp
    rw [this]; exact isDiag_diagonal l
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInfiniteAdelicCharNeOne
section
theorem UpperTheory.Reformulated.B.Rd3.exists_infiniteAdelicChar_ne_one :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F]
    (w : NumberField.InfinitePlace F),
    ∃ (z : w.Completion),
      (GroundTheory.Global.infiniteAdelicChar F w : w.Completion → Circle) z ≠
        (1 : Circle) := by
  intro F _ _ w
  refine ⟨((2 * w.mult : ℕ) : w.Completion)⁻¹, fun h => ?_⟩
  have hm : (w.mult : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr NumberField.InfinitePlace.mult_pos.ne'
  have hx : 2 * Real.pi * -((w.mult : ℝ) * (((2 * w.mult : ℕ) : ℝ))⁻¹) = -Real.pi := by
    push_cast
    field_simp
  rw [GroundTheory.Global.infiniteAdelicChar_apply, map_inv₀, map_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.ofReal_re] at h
  have h2 := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [Real.fourierChar_apply, hx, Circle.coe_one] at h2
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
  norm_num at h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthogonalUnitVector
section
noncomputable def UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit :
    {K V : Type} →
      [inst : Field K] →
        [inst_1 : StarRing K] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module K V] → Subring K → (V →ₗ⋆[K] V →ₗ[K] K) → Prop :=
    fun {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) ↦
      ∀ (w y : V),
        ((h : V → V →ₗ[K] K) y : V → K) w = (1 : K) →
          ((h : V → V →ₗ[K] K) w : V → K) w ∈ S →
            ((h : V → V →ₗ[K] K) y : V → K) y ∈ S →
              ∃ c ∈ S,
                ∃ d ∈ S, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (c • w + d • y) : V → K) (c • w + d • y))


open Formalism.HermitianLattices.Ext.L3.WA in
private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S)
    (hn : h.Nondegenerate) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) {v : V} (hv : v ≠ 0) :
    ∃ a : K, a • v ∈ L ∧ ∃ w ∈ L, h w (a • v) = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ L, h m v = a}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', L.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, L.neg_mem hm, by simp⟩ }
  have hmul : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨star s • m, hL.smul_mem _ (hS.star_mem s hs) _ hm, by
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]⟩
  have hne : ∃ a ∈ A, a ≠ 0 := by
    have hu : ∃ u, h u v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (hn.2 v hc)
    obtain ⟨u, hu⟩ := hu
    obtain ⟨t, ht, htu⟩ := hL.span u
    refine ⟨_, ⟨t • u, htu, rfl⟩, ?_⟩
    simp [map_smulₛₗ, ht, hu]
  have hbd : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htv⟩ := hL.span v
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hL.int m hm _ htv
  obtain ⟨α, ⟨w, hw, hα⟩, hα0, hdiv⟩ := hS.principal A hmul hne hbd
  refine ⟨α⁻¹, hL.dual _ fun m hm => ?_, w, hw, ?_⟩
  · simpa [mul_comm] using hdiv _ ⟨m, hm, rfl⟩
  · rw [map_smul, hα, smul_eq_mul, inv_mul_cancel₀ hα0]


open Formalism.HermitianLattices.Ext.L3.WA in
private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hS : IsHermSemilocal S) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hp : UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L)
    {k : ℕ} (hk : k < Module.finrank K V) (x : Fin k → V) (hxL : ∀ i, x i ∈ L)
    (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ z ∈ L, (∀ i, h (x i) z = 0) ∧ IsUnitIn S (h z z) := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let φ : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (x i)
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxv : ∀ i, h (x i) v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hvk) i
  obtain ⟨a, hyL, w₀, hw₀, hwy⟩ := UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive hS hn hL hv0
  have hxy : ∀ i, h (x i) (a • v) = 0 := fun i => by rw [map_smul, hxv, smul_zero]
  generalize a • v = y at hyL hwy hxy
  have hyx : ∀ i, h y (x i) = 0 := fun i => by rw [← hsym, hxy, star_zero]
  have hyw₀ : h y w₀ = 1 := by rw [← hsym, hwy, star_one]
  let w : V := w₀ - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) w₀) • x i
  have hwL : w ∈ L :=
    L.sub_mem hw₀ (L.sum_mem fun i _ =>
      hL.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hw₀)) _ (hxL i))
  have hyw : h y w = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [w, map_sub, map_sum, hyx, hyw₀]
  have hxw : ∀ j, h (x j) w = 0 := by
    intro j
    have hj := (hxu j).1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [w, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · field_simp
      ring
    · intro i _ hij
      rw [hxo j i hij.symm, mul_zero]
    · simp
  obtain ⟨c, hc, d, hd, hu⟩ := hp w y hyw (hL.int _ hwL _ hwL) (hL.int _ hyL _ hyL)
  refine ⟨c • w + d • y, L.add_mem (hL.smul_mem _ hc _ hwL) (hL.smul_mem _ hd _ hyL), fun i => ?_, hu⟩
  rw [map_add (f := _), map_smul, map_smul, hxw, hxy, smul_zero, smul_zero, add_zero]

theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit :
    ∀ {K V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} [FiniteDimensional K V],
      Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal S →
        h.IsSymm →
          h.Nondegenerate →
            UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h →
              ∀ {L : AddSubgroup V},
                Formalism.HermitianLattices.Ext.L3.WA.IsSelfDualMod S h L →
                  ∃ (x : Fin (Module.finrank K V) → V),
                    (∀ (i : Fin (Module.finrank K V)), x i ∈ L) ∧
                      (∀ (i j : Fin (Module.finrank K V)), i ≠ j → ((h : V → V →ₗ[K] K) (x i) : V → K) (x j) = (0 : K)) ∧
                        ∀ (i : Fin (Module.finrank K V)),
                          Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (x i) : V → K) (x i)) := by
  intro K V _ _ _ _ S h _ hS hs hn hp L hL
  have key : ∀ k : ℕ, k ≤ Module.finrank K V → ∃ x : Fin k → V, (∀ i, x i ∈ L) ∧
      (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
        ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxL, hxo, hxu⟩ := ih (by omega)
      obtain ⟨z, hzL, hxz, hzu⟩ :=
        UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend hS hs hn hp hL (by omega) x hxL hxo hxu
      have hzx : ∀ i, h z (x i) = 0 := fun i => by
        rw [← hs.eq, hxz, map_zero]
      refine ⟨Fin.cons z x, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzL
        · simpa using hxL i
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hzx j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hxz i
          | succ j => simpa using hxo i j fun e => hij (by rw [e])
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzu
        · simpa using hxu i
  exact key _ le_rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSmulMemBis
section
private lemma exists_ne_zero_smul_mem_of_span_eq_top_alt {O LL V : Type} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) (h : Submodule.span LL (T : Set V) = ⊤) (v : V) :
    ∃ a : O, a ≠ 0 ∧ a • v ∈ T := by
  have hv : v ∈ Submodule.span LL (T : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.smul_mem _ hax
    · rw [mul_smul]; exact T.smul_mem _ hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hd : (d : O) ≠ 0 := nonZeroDivisors.ne_zero d.2
    refine ⟨(d : O) * a, mul_ne_zero hd ha, ?_⟩
    have key : ((d : O) * a) • c • x = n • a • x := by
      have e : ∀ (r : O) (y : V), r • y = (algebraMap O LL r) • y :=
        fun r y => (algebraMap_smul LL r y).symm
      have hnd' : c * algebraMap O LL (d : O) = algebraMap O LL n := hnd
      rw [e ((d : O) * a), e n, e a, smul_smul, smul_smul, map_mul, ← hnd']
      congr 1
      ring
    rw [key]
    exact T.smul_mem _ hax

open Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.ExistsSmulMemBis.exists_smul_mem
    {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    {Qp LL O : Type} [inst_2 : Field Qp] [inst_3 : Field LL] [inst_4 : Algebra Qp LL]
    [inst_5 : CommRing O] [inst_6 : Algebra O LL] [inst_7 : TopologicalSpace LL]
    (A : GRep G Qp LL O) (LA : @Lattice G inst LL inst_3 O inst_5 A.V A.acg A.modLL A.modO A.ρ)
    [IsDomain O] [IsFractionRing O LL] (v : A.V) :
    letI := A.acg
    letI := A.modO
    ∃ a : O, a ≠ 0 ∧ a • v ∈ LA.T := by
  let _ := A.acg
  let _ := A.modLL
  let _ := A.modO
  have _ := A.towO
  obtain ⟨T, _, _, _, hs⟩ := LA
  exact exists_ne_zero_smul_mem_of_span_eq_top_alt T hs v
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HaarConstOfHaarExists
section
theorem UpperTheory.Reformulated.B.Gla1.haar_const_of_haar_exists :
    UpperTheory.ConvolutionTheory.T4.HaarEx → UpperTheory.ConvolutionTheory.T4.HaarConst := by
  intro H V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  have hm1 := fun v => (hm v).1
  choose a ha0 ha using H V G Gi Gv q p K hRP μ μi m hμ hμi hm1
  obtain ⟨hq, hp, hK, -⟩ := hRP
  obtain ⟨A⟩ : Nonempty (TopologicalSpace.PositiveCompacts Gi) := inferInstance
  refine ⟨a ∅, ha0 ∅, fun S => ?_⟩
  have h : a ∅ = a S :=
    UpperTheory.restricted_product_measure V G Gi Gv q (fun v => p v) (fun v => K v) μ μi m hq.measurable
      (fun v => (hp v).measurable) (fun v => (hK v).measurableSet) (fun v => (hm v).2)
      ⟨A, A.isCompact.measurableSet,
        (MeasureTheory.Measure.measure_pos_of_nonempty_interior μi A.interior_nonempty).ne',
        A.isCompact.measure_lt_top.ne⟩ ∅ S (a ∅) (a S) (ha ∅) (ha S)
  exact h ▸ ha S
end

