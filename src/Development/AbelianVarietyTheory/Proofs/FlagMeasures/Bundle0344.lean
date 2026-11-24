module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommutantScalar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinors
section
open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.ReducedGram

open NumberField Module Matrix in
open scoped Classical in
private lemma upperUnitriangular_mul_apply_of_le {R : Type} [CommRing R] {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) R) (hA0 : ∀ i j, j < i → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB0 : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) {i j : Fin N} (h : j ≤ i) :
    (A * B) i j = if i = j then 1 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · split_ifs with hij
    · subst hij
      rw [hA1, hB1, one_mul]
    · rw [hA1, one_mul]
      exact hB0 i j (lt_of_le_of_ne h (fun e => hij e.symm))
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hki | hik
    · rw [hA0 i k hki, zero_mul]
    · rw [hB0 k j (lt_of_le_of_lt h hik), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

open NumberField Module Matrix in
open scoped Classical in
private lemma exists_integral_unitriangular_reduction {K : Type} [Field K] [NumberField K]
    (hK : ∀ w : InfinitePlace K, w.IsComplex) {N : ℕ} (V : Matrix (Fin N) (Fin N) K)
    (hV0 : ∀ i j, j < i → V i j = 0) (hV1 : ∀ i, V i i = 1) :
    ∃ m : Matrix (Fin N) (Fin N) (𝓞 K), (∀ i j, j < i → m i j = 0) ∧ (∀ i, m i i = 1) ∧
      ∀ (τ : K →+* ℂ) (i j : Fin N), ‖τ ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤
        max 1 (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) := by
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  let φ : K →+* (InfinitePlace K → ℂ) := Pi.ringHom fun w => w.embedding
  let O : Subring (InfinitePlace K → ℂ) := (φ.comp (algebraMap (𝓞 K) K)).range
  let FF : Set (InfinitePlace K → ℂ) := {x | ∀ w, ‖x w‖ ≤ c}
  have hφ : ∀ (x : K) (w : InfinitePlace K), φ x w = w.embedding x := fun _ _ => rfl
  have hcov : ∀ x : InfinitePlace K → ℂ, ∃ a ∈ O, x + a ∈ FF := by
    intro x
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.coveringO_holds K hK (fun w => -x w)
    refine ⟨φ (a : K), ⟨a, rfl⟩, fun w => ?_⟩
    have e : (x + φ (a : K)) w = -(-x w - w.embedding (a : K)) := by
      rw [Pi.add_apply, hφ]
      ring
    rw [e, norm_neg]
    exact ha w
  obtain ⟨n, hn1, hn0, hnO, hnF⟩ := _root_.Formalism.HermitianLatticeCounting.P.unitriangularReduction (InfinitePlace K → ℂ) O FF N (V.map φ) hcov
    (fun i => by simp [hV1]) (fun i j h => by simp [hV0 i j h])
  have hlift : ∀ i j, ∃ a : 𝓞 K, φ (a : K) = n i j := by
    intro i j
    obtain ⟨a, ha⟩ := hnO i j
    exact ⟨a, ha⟩
  choose m₀ hm₀ using hlift
  let m : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of m₀
  have hm : ∀ i j, φ (m i j : K) = n i j := hm₀
  have hinj : ∀ a b : 𝓞 K, φ (a : K) = φ (b : K) → a = b := fun a b h =>
    RingOfIntegers.coe_injective (φ.injective h)
  have hm0 : ∀ i j, j < i → m i j = 0 := fun i j h =>
    hinj _ _ (by rw [hm, hn0 i j h]; simp)
  have hm1 : ∀ i, m i i = 1 := fun i => hinj _ _ (by rw [hm, hn1]; simp)
  refine ⟨m, hm0, hm1, ?_⟩
  have hn : n = (m.map (fun x : 𝓞 K => (x : K))).map φ := by
    exact Matrix.ext fun i j => (hm i j).symm
  have hprod : V.map φ * n = (V * m.map (fun x : 𝓞 K => (x : K))).map φ := by
    rw [hn, Matrix.map_mul]
  have key : ∀ (i j : Fin N) (w : InfinitePlace K),
      ‖w.embedding ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤ max 1 c := by
    intro i j w
    rcases lt_or_ge i j with hij | hji
    · have h := hnF i j hij w
      rw [hprod, Matrix.map_apply, hφ] at h
      exact le_max_of_le_right h
    · rw [upperUnitriangular_mul_apply_of_le V _ hV0 hV1
        (fun a b h => by simp [hm0 a b h]) (fun a => by simp [hm1 a]) hji]
      split_ifs <;> simp
  intro τ i j
  rw [← InfinitePlace.apply, ← InfinitePlace.norm_embedding_eq]
  exact key i j _

open NumberField Module Matrix in
open scoped Classical in
private lemma det_submatrix_mul_diagonal {R : Type} [CommRing R] {N t : ℕ}
    (X : Matrix (Fin N) (Fin N) R) (s : Fin N → R) (I J : Fin t → Fin N) :
    ((X * diagonal s).submatrix I J).det = (X.submatrix I J).det * ∏ k, s (J k) := by
  have hsub : (X * diagonal s).submatrix I J = X.submatrix I J * diagonal (fun k => s (J k)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  rw [hsub, det_mul, det_diagonal]


open NumberField Module Matrix in
open scoped Classical in
theorem _root_.GlobalTheory.ReducedGram.exists_reduced : ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (p : _root_.Formalism.MainNotions.S.Point K (r + 1)), _root_.Formalism.MainNotions.S.IsInCell (_root_.Formalism.MainNotions.S.ZhatOM Z) p →
    ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, _root_.Formalism.MainNotions.S.Lat.ZEquiv Z Z₂ ∧
      ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)),
        ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 *
          (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) *
          ∏ l ∈ Finset.Icc 1 (r + 1),
            (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
  intro K _ _ hK r Z p hcell
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  have hc : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (finrank ℚ K) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast Module.finrank_pos
    have h2 : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) := by
      apply Real.one_le_rpow
      · have hd : discr K ≠ 0 := discr_ne_zero K
        have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs hd
        exact_mod_cast this
      · positivity
    nlinarith
  have hmax : max 1 c = c := max_eq_right hc
  unfold _root_.Formalism.MainNotions.S.IsInCell at hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  unfold _root_.Formalism.MainNotions.S.IsLoUni at hL
  unfold _root_.Formalism.MainNotions.S.IsUpUni at hU
  set P := _root_.Formalism.MainNotions.S.ptMat p with hP
  let s : Fin (r + 1) → K := fun b => (-1) ^ (r - (b : ℕ))
  have hss : ∀ b, s b * s b = 1 := by
    intro b
    simp only [s, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hDD : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hss]
    exact diagonal_one
  have hZD : Z = _root_.Formalism.MainNotions.S.ZhatOM Z * diagonal s := by
    ext a b
    simp only [_root_.Formalism.MainNotions.S.ZhatOM, mul_diagonal, s]
    linear_combination (-Z a b) * hss b
  have hZD' : Z = L * P * U * diagonal s := by
    rw [← hZ]
    exact hZD
  let V := diagonal s * U * diagonal s
  have hVapp : ∀ i j, V i j = s i * U i j * s j := by
    intro i j
    simp [V, mul_diagonal, diagonal_mul]
  have hV0 : ∀ i j, j < i → V i j = 0 := fun i j h => by rw [hVapp, (hU i j).1 h]; ring
  have hV1 : ∀ i, V i i = 1 := fun i => by
    rw [hVapp, (hU i i).2 rfl, mul_one, hss]
  have hZeq : Z = L * (P * diagonal s) * V := by
    rw [hZD']
    calc L * P * U * diagonal s = L * P * (diagonal s * diagonal s) * U * diagonal s := by
          rw [hDD, Matrix.mul_one]
      _ = L * (P * diagonal s) * V := by simp only [V, Matrix.mul_assoc]
  obtain ⟨m, hm0, hm1, hmb⟩ := exists_integral_unitriangular_reduction hK V hV0 hV1
  obtain ⟨m', hm'0, hm'1, hm'b⟩ := exists_integral_unitriangular_reduction hK Lᵀ
    (fun i j h => by rw [transpose_apply]; exact (hL j i).1 h)
    (fun i => by rw [transpose_apply]; exact (hL i i).2 rfl)
  rw [hmax] at hmb hm'b
  let A := m'ᵀ.map (fun x : 𝓞 K => (x : K)) * L
  let B := V * m.map (fun x : 𝓞 K => (x : K))
  let W := P * diagonal s
  refine ⟨A * W * B, ⟨m'ᵀ, m, fun a b h => hm'0 b a h, fun a => hm'1 a, hm0, hm1, ?_⟩, ?_⟩
  · simp only [A, B, W]
    rw [hZeq]
    simp only [Matrix.mul_assoc, transpose_map]
  intro τ t I J
  have hmin : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : ℕ) (I J : Fin t → Fin (r + 1)),
      ((X.map τ).submatrix I J).det = τ ((X.submatrix I J).det) := by
    intro X t I J
    rw [RingHom.map_det]
    rfl
  have hsign : ∀ (t : ℕ) (J : Fin t → Fin (r + 1)), ‖τ (∏ k, s (J k))‖ = 1 := by
    intro t J
    rw [map_prod, norm_prod]
    simp [s]
  have hA : ∀ i j, ‖(A.map τ) i j‖ ≤ c := by
    intro i j
    have hAt : A = (Lᵀ * m'.map (fun x : 𝓞 K => (x : K)))ᵀ := by
      simp only [A, transpose_mul, transpose_transpose, transpose_map]
    rw [Matrix.map_apply, hAt, transpose_apply]
    exact hm'b τ j i
  have hB : ∀ i j, ‖(B.map τ) i j‖ ≤ c := fun i j => hmb τ i j
  set Pb := ∏ l ∈ Finset.range (r + 1), _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P (l + 1))‖ with hPb
  have hW : ∀ (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖((W.map τ).submatrix I J).det‖ ≤ Pb := by
    intro t I J
    rw [hmin, det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one, ← hmin]
    exact _root_.GlobalTheory.LoopC.CovTerm.minor_pt_le τ p t I J
  have hbound := _root_.Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.minorBound (r + 1) (A.map τ) (W.map τ) (B.map τ) c Pb hc hA hB hW t I J
  have hlead : ∀ l, ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ = ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖ := by
    intro l
    unfold _root_.Formalism.MainNotions.S.leadMinorE
    split_ifs with hl
    · rw [hZD', det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one,
        _root_.Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant K (r + 1) l hl L P U (fun i => (hL i i).2 rfl) (fun i j h => (hL i j).1 h)
          (fun i => (hU i i).2 rfl) (fun i j h => (hU i j).1 h)]
    · rfl
  have hPbeq : Pb = ∏ l ∈ Finset.Icc 1 (r + 1),
      (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
    rw [hPb, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun l => _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖) 0 (r + 1) 1,
      zero_add, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [hlead]
    rfl
  rw [← hmin, Matrix.map_mul, Matrix.map_mul, ← hPbeq]
  exact hbound

end GlobalTheory.ReducedGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdempotentIntertwinerImagesCuspidalOfLevel
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspAllKType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  simp only [AutInst.Kg, AutInst.Kset, Set.mem_setOf_eq]
  refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
  · simp
  · simp [AutInst.fmat]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨h1, hm, hn, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hbi, -⟩ := B.e_adm

  set π : B.I.Gf → (B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) := fun a => B.R (1, a) with hπ
  have hπ1 : π 1 = 1 := h1
  have hπm : ∀ a b, π (a * b) = π a * π b := fun a b => by
    simp only [hπ]
    rw [← hm]
    congr 1
    ext <;> simp
  have hπn : ∀ a v, ‖π a v‖ = ‖v‖ := fun a v => hn _ v

  have hek : ∀ x, B.e (k * x) = B.e x := fun x => by
    simpa using hbi x k hk 1 (one_mem_Kg B.I B.g)
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  change ⟪x, π k (B.Re y)⟫_ℂ = _
  rw [GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (B.Re y), B.Re_spec.2 (π k⁻¹ x) y, B.Re_spec.2 x y]
  have hinner : ∀ a, ⟪π k⁻¹ x, B.R (1, a) y⟫_ℂ = ⟪x, B.R (1, k * a) y⟫_ℂ := fun a => by
    have := (GlobalTheory.IdemProj.inner_rep π hπ1 hπm hπn k x (π a y)).symm
    change ⟪π k⁻¹ x, π a y⟫_ℂ = ⟪x, π (k * a) y⟫_ℂ
    rw [this, hπm, ContinuousLinearMap.mul_apply]
  simp_rw [hinner]
  calc ∫ a, B.e a * ⟪x, B.R (1, k * a) y⟫_ℂ ∂B.μf
      = ∫ a, (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) (k * a) ∂B.μf := by
        congr 1
        ext a
        simp only [hek]
    _ = ∫ a, B.e a * ⟪x, B.R (1, a) y⟫_ℂ ∂B.μf := by
        exact integral_mul_left_eq_self (μ := B.μf) (fun b => B.e b * ⟪x, B.R (1, b) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have hmaj := hint 0 le_rfl (fun v => by
    by_cases hq : rkR (B.I.ε v) = 0
    · exact Or.inl hq
    right

    have hqn : rkR (B.I.ε v) ≤ B.I.n := by
      unfold rkR
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    have hq1 : (1 : ℝ) ≤ (rkR (B.I.ε v) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
    have hqn' : (rkR (B.I.ε v) : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hqn
    have hs : 0 < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hn : 0 < (B.I.n : ℝ) := by linarith
    have hns : 0 < (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := mul_pos hn hs
    have h1 : (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (rkR (B.I.ε v) : ℝ)
        ≤ (B.I.n : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) * (B.I.n : ℝ) :=
      mul_le_mul_of_nonneg_left hqn' hns.le
    have h2 := hb v
    nlinarith)
  simp only [zero_mul, Real.exp_zero, mul_one] at hmaj
  exact hmaj.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)

theorem cusp_all : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, A ∈ B.I.HomS B.σs B.μf B.fund B.R ∧ ∀ u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A u)) ∧ ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A u) = A u := by
  intro B d h hd hK hg hh hl hb A hA

  obtain ⟨T0, hT0, hA'⟩ := Submodule.mem_map.1 hA
  have hAe : A = B.Re.comp T0 := by rw [← hA']; rfl
  subst hAe
  have hT0' : ∀ g : B.I.Ginf, T0.comp (B.σs g) = (B.R (g, 1)).comp T0 := hT0
  have hint := integrable_ph B d h hd hl hb
  obtain ⟨-, hcomm, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd hint
  have hHom : ∀ g : B.I.Ginf, (B.Re.comp T0).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp T0) := fun g => by
    rw [ContinuousLinearMap.comp_assoc, hT0' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  refine ⟨hHom, fun u => ?_⟩

  obtain ⟨S, hSmem, hScl, hSinv, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, hirr, -, hnorm, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hw := _root_.GlobalTheory.RowCuspKType.row_isCuspFn B d h hd hK hg hh hl hb T hT (B.Re.comp T0) hA
  let S' : Submodule ℂ B.Hs := S.comap ((B.Re.comp T0 : B.Hs →L[ℂ] B.I.L2 B.μf B.fund) : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund)
  have hS'cl : IsClosed (S' : Set B.Hs) := hScl.preimage (B.Re.comp T0).continuous
  have hS'inv : ∀ g, ∀ v ∈ S', B.σs g v ∈ S' := fun g v hv => by
    have hv' : (B.Re.comp T0) v ∈ S := hv
    show (B.Re.comp T0) (B.σs g v) ∈ S
    have := congrArg (fun F : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => F v) (hHom g)
    simp only [ContinuousLinearMap.comp_apply] at this
    simp only [ContinuousLinearMap.comp_apply]
    rw [this]
    exact hSinv _ _ hv'
  have hwS : B.tens B.w ∈ S' := (hSmem _).2 hw
  rcases hirr S' hS'cl hS'inv with h0 | htop
  · exfalso
    rw [h0, Submodule.mem_bot] at hwS
    rw [hwS, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · have hu : u ∈ S' := htop ▸ Submodule.mem_top
    refine ⟨(hSmem _).1 hu, fun k hk => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply (B.R (1, k)) B.Re, re_fixed B k hk]

end GlobalTheory.Dec.CuspAllKType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateFamilyIsKFiniteHermitian
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat in
theorem integrable_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hf : Continuous f) (v : H) :
    Integrable (fun g => f g • σ g v) μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K _ =>
    (measure_mono (Set.subset_univ K)).trans_lt (hμ.1.measure_univ.symm ▸ ENNReal.one_lt_top)⟩
  have hK := isCompact_KH k r
  have hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r) := fun g hg => hg.1
  have hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) :=
    hf.continuousOn.smul ((hσ.2.2 v).mono hsub)
  have hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ := hc.integrableOn_compact hK
  have hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  rw [IntegrableOn, hr] at hI
  exact hI

attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat in
theorem integral_sum_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {N : ℕ} {b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hb : ∀ j, Continuous (b j))
    (c : Fin N → ℂ) (v : H) :
    ∫ g, (∑ j, c j * b j g) • σ g v ∂μ = ∑ j, c j • ∫ g, b j g • σ g v ∂μ := by
  simp_rw [Finset.sum_smul, mul_smul]
  rw [integral_finsetSum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) :
      Integrable (fun g => c j • (b j g • σ g v)) μ))]
  simp_rw [integral_smul]

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg

attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat in
theorem isKFinHpk_integral_translates : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  intro k r H _ _ _ σ μ hσ hμ N b hb hinv c v
  obtain ⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ := ⟨_, fun _ => rfl⟩
  have key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j := by
    intro c'
    rw [integral_sum_smul_orbit hσ hμ hb c' v]
    simp_rw [hw]
  have hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w) := fun c' =>
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩
  · rw [key]; exact hmem c
  · intro a ha x hx
    have hu : star a * a = 1 := ha.2.1
    have haa : a⁻¹ * a = 1 := by rw [Matrix.inv_eq_left_inv hu]; exact hu
    have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := by rw [ae_iff]; exact hμ.2.1
    have hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w) := by
      intro j
      obtain ⟨d, hd⟩ := hinv a⁻¹ j
      have h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ := by
        rw [hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with g hg
        rw [map_smul, hσ.1.2 a ha.1 g hg.1]
        rfl
      have hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g) :=
        continuous_const.matrix_mul continuous_id
      have h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ := by
        have hmap : μ.map (fun g => a * g) = μ := hμ.2.2.1 a ha
        have hm : AEStronglyMeasurable (fun g => b j (a⁻¹ * g) • σ g v) (μ.map fun g => a * g) := by
          rw [hmap]
          exact (integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable
        calc
          _ = ∫ g, b j (a⁻¹ * (a * g)) • σ (a * g) v ∂μ := by
            simp only [← Matrix.mul_assoc, haa, Matrix.one_mul]
          _ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ.map (fun g => a * g) :=
            (MeasureTheory.integral_map (μ := μ) hcm.aemeasurable hm).symm
          _ = _ := by rw [hmap]
      rw [h1, h2]
      simp_rw [hd]
      rw [key]
      exact hmem d
    have hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    exact hle hx

end GlobalTheory.KFinAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCuspHomOfCuspLowest
section
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isCuspHom_of_cusp_lowest : ∀ (B : RowsAut), (∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) → (∀ v, ‖B.w v‖ = 1) → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) → IsCuspHom B.I A := by
  intro B hDS hw A hA hcusp
  obtain ⟨S, hS, hSc, hSR, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, -, -, -, hirr⟩ :=
    GlobalTheory.HilbTensorRep.tensor_rep_rows B fun v => ⟨(hDS v).2.2.1, (hDS v).2.2.2.1⟩
  obtain ⟨T₀, hT₀, rfl⟩ := Submodule.mem_map.mp hA
  have hT₀' : ∀ g : B.I.Ginf, T₀.comp (B.σs g) = (B.R (g, 1)).comp T₀ := hT₀
  have hRe := (GlobalTheory.IdemProj.re_orth_proj B).2.1

  have hint : ∀ (g : B.I.Ginf) (u : B.Hs),
      B.Re (T₀ (B.σs g u)) = B.R (g, 1) (B.Re (T₀ u)) := by
    intro g u
    have h1 := congrArg (fun L => L u) (hT₀' g)
    have h2 := congrArg (fun L => L (T₀ u)) (hRe g)
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]

  let P : Submodule ℂ B.Hs := S.comap (B.Re.comp T₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund).toLinearMap
  have hPc : IsClosed (P : Set B.Hs) :=
    hSc.preimage (B.Re.comp T₀).continuous
  have hPs : ∀ g, ∀ u ∈ P, B.σs g u ∈ P := by
    intro g u hu
    change B.Re (T₀ (B.σs g u)) ∈ S
    rw [hint]
    exact hSR _ _ hu
  have hw0 : B.tens B.w ∈ P := by
    change B.Re (T₀ (B.tens B.w)) ∈ S
    rw [hS]
    simpa [ContinuousLinearMap.compL_apply] using hcusp
  have hne : B.tens B.w ≠ 0 := by
    intro h0
    have hn := GlobalTheory.HilbTensorRep.norm_tens B.tens_spec.1 B.w
    rw [h0, norm_zero] at hn
    simp [hw] at hn
  rcases hirr P hPc hPs with hbot | htop
  · exact absurd ((Submodule.mem_bot ℂ).mp (hbot ▸ hw0)) hne
  · intro u
    have hu : u ∈ P := htop ▸ Submodule.mem_top
    have : B.Re (T₀ u) ∈ S := hu
    simpa [ContinuousLinearMap.compL_apply] using (hS _).mp this

end GlobalTheory.RowLev
end

