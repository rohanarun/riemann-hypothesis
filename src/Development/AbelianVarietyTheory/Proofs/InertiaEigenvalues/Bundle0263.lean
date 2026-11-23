module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmulMemFilV
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmbeddingJump

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (z : BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ[Qp] z) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * z) := by
  simp [mulVdR]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v z => simp [mulVdR, actVdR]

theorem mul_mem_DdR (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx g]

theorem tmul_mem_FilV (a : ℤ) (v : V) {z : BdR} (hz : z ∈ PD.Fil a) :
    v ⊗ₜ[Qp] z ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨z, hz⟩, by simp⟩

theorem mul_mem_FilV (a : ℤ) (c : K) {x : V ⊗[Qp] BdR} (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply]
    rw [mulVdR_tmul, ← Algebra.smul_def]
    exact tmul_mem_FilV PD a v ((PD.Fil a).smul_mem c z.2)

theorem mul_mul (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) c (mulVdR (K := K) (LL := LL) c' x) =
      mulVdR (K := K) (LL := LL) (c * c') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v z => simp only [mulVdR_tmul, map_mul, mul_assoc]

theorem mul_add' (c c' : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (c + c') x =
      mulVdR (K := K) (LL := LL) c x + mulVdR (K := K) (LL := LL) c' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  | tmul v z => simp only [mulVdR_tmul, map_add (f := _), add_mul, TensorProduct.tmul_add]

theorem mul_smul' (r : Qp) (c : K) (x : V ⊗[Qp] BdR) :
    mulVdR (K := K) (LL := LL) (r • c) x = r • mulVdR (K := K) (LL := LL) c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  | tmul v z =>
    simp only [mulVdR_tmul]
    rw [← TensorProduct.tmul_smul, ← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]

def projMap (τ : K →ₐ[Qp] LL) (x : V ⊗[Qp] BdR) : K ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun a c => τ a • mulVdR (K := K) (LL := LL) c x)
    (fun a a' c => by rw [map_add (f := _), add_smul])
    (fun r a c => by rw [map_smul, smul_assoc])
    (fun a c c' => by rw [mul_add', smul_add])
    (fun r a c => by rw [mul_smul', smul_comm]))

theorem proj_mem (τ : K →ₐ[Qp] LL) {n : ℕ} (α β : Fin n → K)
    (h : ∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[Qp] β j = ∑ j, α j ⊗ₜ[Qp] (κ * β j)) (u : ℤ)
    {x : V ⊗[Qp] BdR} (hx : x ∈ DdR PD ρ) (hu : x ∈ FilV PD (LL := LL) (V := V) u)
    (hj : ¬ IsJumpV PD ρ τ u) :
    ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FilV PD (LL := LL) (V := V) (u + 1) := by
  have he : FildR PD ρ τ (u + 1) = FildR PD ρ τ u := not_not.1 hj
  have : ∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) x ∈ FildR PD ρ τ u := by
    refine ⟨⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_DdR PD ρ _ hx), ?_⟩,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_FilV PD u _ hu)⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro c
    have := congrArg (projMap τ x) (h c)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, projMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, mul_mul, Finset.smul_sum, smul_smul, ← map_mul]
    exact this.symm
  rw [← he] at this
  exact this.2

def coordMap (f : V →ₗ[Qp] Qp) : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
  (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem coordMap_mem (f : V →ₗ[Qp] Qp) (a : ℤ) {x : V ⊗[Qp] BdR}
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : coordMap f x ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | tmul v z =>
    simp only [coordMap, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply,
      Submodule.subtype_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearEquiv.coe_coe, TensorProduct.lid_tmul]
    exact ((PD.Fil a).restrictScalars Qp).smul_mem _ z.2

theorem coord_proj (τ : K →ₐ[Qp] LL) {n d : ℕ} (α β : Fin n → K) (f : V →ₗ[Qp] Qp)
    (b : Fin d → V) (y : Fin d → BdR) (s : BdR) :
    coordMap f (∑ j, τ (α j) • mulVdR (K := K) (LL := LL) (β j) (∑ k, b k ⊗ₜ[Qp] (y k * s))) =
      (∑ j, ∑ k, (algebraMap K BdR (β j) * algebraMap Qp BdR (f (τ (α j) • b k))) * y k) * s := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, mulVdR_tmul, Finset.smul_sum, TensorProduct.smul_tmul', coordMap,
    LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    LinearMap.id_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def]
  ring

end General

open GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : ThetaL P AI)

theorem theta_sum {ι : Type} (s : Finset ι) (z : ι → P.R.BdR)
    (hz : ∀ i, z i ∈ (P.PD (botExt l)).Fil 0) : J.θ (∑ i ∈ s, z i) = ∑ i ∈ s, J.θ (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (J.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      J.θ_add _ (hz a) _ (Submodule.sum_mem _ fun i _ => hz i), ih]

theorem theta_lin {n d : ℕ} (c : Fin n → Fin d → Om l) (y : Fin d → P.R.BdR)
    (hy : ∀ k, y k ∈ (P.PD (botExt l)).Fil 0)
    (h : ∑ j, ∑ k, algebraMap (Om l) P.R.BdR (c j k) * y k ∈ (P.PD (botExt l)).Fil 1) :
    ∑ j, ∑ k, ((c j k : Om l) : PadicComplex l) * J.θ (y k) = 0 := by
  have hm : ∀ (c : Om l) (k : Fin d), algebraMap (Om l) P.R.BdR c * y k ∈
      (P.PD (botExt l)).Fil 0 := fun c k => by
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (om_mem c) (hy k)
    rwa [zero_add] at this
  have h3 := (J.θ_ker _ (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => hm _ k)).2 h
  rw [theta_sum J _ _ (fun j => Submodule.sum_mem _ fun k _ => hm _ k)] at h3
  rw [← h3]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [theta_sum J _ _ (fun k => hm _ k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [J.θ_mul _ (om_mem _) _ (hy k), J.θ_Om]

theorem mat_apply {n d : ℕ} (β : Fin n → Om l) (m : Fin n → Fin d → Fin d → ℚ_[l])
    (w : Fin d → PadicComplex l) (i : Fin d) :
    (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d =>
      algebraMap ℚ_[l] (PadicComplex l) (m j k i))).mulVec w i =
    ∑ k, ∑ j, ((β j * algebraMap ℚ_[l] (Om l) (m j k i) : Om l) : PadicComplex l) * w k := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [UniformSpace.Completion.coe_mul]
  rfl

theorem proj_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (θ : ThetaL P AI) (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V) (n : ℕ) (α β : Fin n → ↥K.1), (∀ κ : ↥K.1, ∑ j, (κ * α j) ⊗ₜ[ℚ_[l]] β j = ∑ j, α j ⊗ₜ[ℚ_[l]] (κ * β j)) → ∀ t : (P.R.BdR)ˣ, (t : P.R.BdR) = P.ιB P.tB → ∀ (u : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil 0) → ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((t ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈ DdR (P.PD K) T.ρ → ¬ IsJumpV (P.PD K) T.ρ τ u → (∑ j, ((β j : Om l) : PadicComplex l) • Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (τ (α j) • b k) i))).mulVec (fun i => θ.θ (y i)) = 0 := by
  intro l _ P AI θ K LL T τ d b n α β h t ht u y hy hD hj
  obtain rfl : t = tU P := Units.ext ht
  have hF : ∑ i, b i ⊗ₜ[ℚ_[l]] (y i * ((tU P ^ u : (P.R.BdR)ˣ) : P.R.BdR)) ∈
      FilV (P.PD K) (LL := ↥LL.1) (V := T.V) u := by
    refine Submodule.sum_mem _ fun i _ => tmul_mem_FilV _ _ _ ?_
    have := (P.PD K).Fil_mul _ _ _ _ (hy i) ((mem_iff K u _).2 (zpow_mem θ u))
    rwa [zero_add] at this
  have h1 := proj_mem (P.PD K) T.ρ τ α β h u hD hF hj
  funext i
  have h2 := coordMap_mem (P.PD K) (b.coord i) _ h1
  rw [coord_proj, mem_iff, ← shift_iff θ, mul_left_comm, ← Units.val_mul, ← zpow_add,
    neg_add_cancel, zpow_zero, Units.val_one, mul_one] at h2
  have e : ∀ (j : Fin n) (k : Fin d), algebraMap (↥K.1) P.R.BdR (β j) *
      algebraMap ℚ_[l] P.R.BdR (b.coord i (τ (α j) • b k)) =
      algebraMap (Om l) P.R.BdR ((β j : Om l) *
        algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) := by
    intro j k
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    rfl
  simp only [e] at h2
  have h3 := theta_lin θ (fun j k => (β j : Om l) *
    algebraMap ℚ_[l] (Om l) (b.repr (τ (α j) • b k) i)) y (fun k => (mem_iff K 0 _).1 (hy k)) h2
  rw [Finset.sum_comm] at h3
  exact (mat_apply (fun j => (β j : Om l)) (fun j k i => b.repr (τ (α j) • b k) i) _ i).trans h3

end GlobalTheory.EmbeddingJump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationPolynomialAtRootOfUnitySubOne
section
open IsDiscreteValuationRing

namespace GlobalTheory.PolyCycloValue

theorem card_double_min (S : Set ℕ) (a : ℕ → ℕ) (q : ℕ → ℝ) (w : ℕ) (hw : w ∈ S)
    (hq : ∀ k, 1 ≤ k → 0 < q k) (hqa : ∀ k k', 1 ≤ k → k < k' → q k' < q k) :
    ∃ BB : Finset ℕ, BB.card ≤ w + a w ∧ ∀ k, 1 ≤ k → k ∉ BB → ∀ i ∈ S, ∀ j ∈ S,
      (∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k) →
      (∀ m ∈ S, (a j : ℝ) + j * q k ≤ a m + m * q k) → i = j := by
  classical
  let M : ℕ → ℕ → Prop := fun k i => i ∈ S ∧ ∀ m ∈ S, (a i : ℝ) + i * q k ≤ a m + m * q k
  let B : Set ℕ := {k | 1 ≤ k ∧ ∃ i j, i < j ∧ M k i ∧ M k j}
  have hch : ∀ k, ∃ i j, k ∈ B → i < j ∧ M k i ∧ M k j := by
    intro k
    by_cases hk : k ∈ B
    · obtain ⟨-, i, j, h⟩ := hk
      exact ⟨i, j, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose I J hIJ using hch

  have hA : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m ≤ i → a i ≤ a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k ≤ i * q k :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmi) (hq k hk).le
    have : (a i : ℝ) ≤ a m := by linarith
    exact_mod_cast this
  have hA' : ∀ k, 1 ≤ k → ∀ i m, M k i → m ∈ S → m < i → a i < a m := by
    intro k hk i m hi hm hmi
    have h1 := hi.2 m hm
    have h2 : (m : ℝ) * q k < i * q k :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hmi) (hq k hk)
    have : (a i : ℝ) < a m := by linarith
    exact_mod_cast this
  have hB : ∀ k k', 1 ≤ k → k < k' → ∀ m m', M k m → M k' m' → m ≤ m' := by
    intro k k' hk hkk m m' hm hm'
    by_contra hlt
    have hlt' : (m' : ℝ) < m := by exact_mod_cast (not_le.mp hlt)
    have h1 := hm.2 m' hm'.1
    have h2 := hm'.2 m hm.1
    have h3 := hqa k k' hk hkk
    nlinarith [mul_pos (sub_pos.mpr hlt') (sub_pos.mpr h3)]
  let φ : ℕ → ℕ := fun k => if I k < w then I k else w + a (J k)
  have hmaps : Set.MapsTo φ B (Finset.range (w + a w) : Set ℕ) := by
    intro k hk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    split_ifs with h
    · omega
    · have := hA' k hk.1 (J k) w hj hw (by omega)
      omega
  have hne : ∀ k ∈ B, ∀ k' ∈ B, k < k' → φ k ≠ φ k' := by
    intro k hk k' hk' hkk
    obtain ⟨hlt, hi, hj⟩ := hIJ k hk
    obtain ⟨hlt', hi', hj'⟩ := hIJ k' hk'
    have h1 := hB k k' hk.1 hkk _ _ hj hi'
    have h2 := hA' k' hk'.1 (J k') (J k) hj' hj.1 (by omega)
    simp only [φ]
    split_ifs <;> omega
  have hinj : Set.InjOn φ B := by
    intro k hk k' hk' h
    rcases lt_trichotomy k k' with h1 | h1 | h1
    · exact absurd h (hne k hk k' hk' h1)
    · exact h1
    · exact absurd h.symm (hne k' hk' k hk h1)
  have hfin : B.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · have := Finset.card_le_card_of_injOn (s := hfin.toFinset) (t := Finset.range (w + a w)) φ
      (by simpa using hmaps) (by simpa using hinj)
    simpa using this
  · intro k hk hkB i hi j hj hmi hmj
    rw [Set.Finite.mem_toFinset] at hkB
    by_contra hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkB ⟨hk, i, j, h, ⟨hi, hmi⟩, ⟨hj, hmj⟩⟩
    · exact hkB ⟨hk, j, i, h, ⟨hj, hmj⟩, ⟨hi, hmi⟩⟩

section Val

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_ne_top {x : R} (hx : x ≠ 0) : addVal R x ≠ ⊤ := by
  rwa [Ne, addVal_eq_top_iff]

theorem toNat_addVal_pos {x : R} (hx : x ≠ 0) (hu : ¬ IsUnit x) : 0 < (addVal R x).toNat := by
  have h1 := addVal_ne_top hx
  have h2 : addVal R x ≠ 0 := by rwa [Ne, addVal_eq_zero_iff]
  exact Nat.pos_of_ne_zero (by simp [ENat.toNat_eq_zero, h1, h2])

theorem nval_mul_pow (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (x * y ^ n) =
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x + n * Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  have : addVal R (x * y ^ n) = ((s + n * t : ℕ) : ℕ∞) := by
    rw [(addVal R).map_mul, (addVal R).map_pow, ← hs, ← ht]; simp
  rw [this, ← hs, ← ht]
  simp only [ENat.toNat_coe]
  push_cast
  ring

theorem addVal_lt_of_nval_lt (l : ℕ) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Formalism.MainNotions.BlochKatoReduction.Gen.nval R l x < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l y) : addVal R x < addVal R y := by
  unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval at h
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hx)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp (addVal_ne_top hy)
  rw [← hs, ← ht] at h ⊢
  simp only [ENat.toNat_coe] at h
  have : (s : ℝ) < t := lt_of_not_ge fun hge =>
    absurd h (not_lt.mpr (div_le_div_of_nonneg_right hge (Nat.cast_nonneg _)))
  exact_mod_cast this

theorem sum_unique_min (l : ℕ) (S : Finset ℕ) (t : ℕ → R) (ht : ∀ i ∈ S, t i ≠ 0) (i₀ : ℕ)
    (hi₀ : i₀ ∈ S)
    (h : ∀ i ∈ S, i ≠ i₀ → Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) < Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i)) :
    ∑ i ∈ S, t i ≠ 0 ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (∑ i ∈ S, t i) = Formalism.MainNotions.BlochKatoReduction.Gen.nval R l (t i₀) := by
  have h0 := addVal_ne_top (ht i₀ hi₀)
  have h1 : addVal R (t i₀) < addVal R (∑ i ∈ S.erase i₀, t i) :=
    (addVal R).map_lt_sum h0 fun i hi =>
      addVal_lt_of_nval_lt l (ht i₀ hi₀) (ht i (Finset.mem_of_mem_erase hi))
        (h i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  have h2 : addVal R (∑ i ∈ S, t i) = addVal R (t i₀) := by
    rw [← Finset.add_sum_erase S t hi₀]
    exact (addVal R).map_add_eq_of_lt_left h1
  refine ⟨fun hz => h0 ?_, ?_⟩
  · rw [← h2, hz]; simp
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval; rw [h2]

end Val

theorem value_at_root_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  intro O _ _ _ l hl hl0 hlu h w hw
  set e : ℝ := ((addVal O (l : O)).toNat : ℝ) with he
  have hepos : 0 < e := by rw [he]; exact_mod_cast toNat_addVal_pos hl0 hlu
  have hphi : ∀ k, (0 : ℝ) < (Nat.totient (l ^ k) : ℝ) := fun k => by
    exact_mod_cast Nat.totient_pos.mpr (pow_pos hl.pos k)
  let a : ℕ → ℕ := fun i => (addVal O (h.coeff i)).toNat
  let q : ℕ → ℝ := fun k => e / (Nat.totient (l ^ k) : ℝ)
  have hwS : w ∈ h.support := Polynomial.mem_support_iff.mpr hw
  obtain ⟨BB, hcard, hBB⟩ := card_double_min (h.support : Set ℕ) a q w hwS
    (fun k _ => div_pos hepos (hphi k)) (by
      intro k k' hk hkk
      refine div_lt_div_of_pos_left hepos (hphi k) ?_
      rw [Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)]
      have h1 : l ^ (k - 1) < l ^ (k' - 1) := Nat.pow_lt_pow_right hl.one_lt (by omega)
      have h2 : 0 < l - 1 := by have := hl.one_lt; omega
      exact_mod_cast Nat.mul_lt_mul_of_pos_right h1 h2)
  have hmin : ∀ k, ∃ i ∈ h.support, ∀ m ∈ h.support, (a i : ℝ) + i * q k ≤ a m + m * q k :=
    fun k => Finset.exists_min_image h.support (fun i => (a i : ℝ) + i * q k) ⟨w, hwS⟩
  choose I hIS hI using hmin
  have hform : ∀ k i : ℕ, Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff i) + i / (Nat.totient (l ^ k) : ℝ)
      = ((a i : ℝ) + i * q k) / e := by
    intro k i
    have := hphi k
    simp only [Formalism.MainNotions.BlochKatoReduction.Gen.nval, a, q, ← he]
    field_simp
  refine ⟨BB, fun k => ((a (I k) : ℝ) + I k * q k) / e, hcard, fun k hk hkB => ⟨?_, ?_⟩⟩
  · rw [hform]
    exact div_le_div_of_nonneg_right (hI k w hwS) hepos.le
  · intro O' _ _ _ _ _ hinj ζ hζ
    have hl0' : (l : O') ≠ 0 := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hl0 (hinj (by rw [h0, map_zero]))
    have hlu' : ¬ IsUnit (l : O') := by
      rw [← map_natCast (algebraMap O O')]
      exact fun h0 => hlu (IsLocalHom.map_nonunit _ h0)
    obtain ⟨hz, hv⟩ := _root_.GlobalTheory.nval_primitiveRoot_prime_pow_sub_one O' l k hl hk hl0' hlu' ζ hζ
    have hc : ∀ i ∈ h.support, algebraMap O O' (h.coeff i) ≠ 0 := fun i hi h0 =>
      Polynomial.mem_support_iff.mp hi (hinj (by rw [h0, map_zero]))
    have hval : ∀ i ∈ h.support,
        Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
          = ((a i : ℝ) + i * q k) / e := by
      intro i hi
      rw [nval_mul_pow l (hc i hi) hz, hv, _root_.GlobalTheory.nval_algebraMap_eq O O' hinj, ← hform, mul_one_div]
    have key := sum_unique_min l h.support
      (fun i => algebraMap O O' (h.coeff i) * (ζ - 1) ^ i)
      (fun i hi => mul_ne_zero (hc i hi) (pow_ne_zero _ hz)) (I k) (hIS k) (by
        intro i hi hne
        rw [hval i hi, hval _ (hIS k)]
        refine div_lt_div_of_pos_right ?_ hepos
        refine lt_of_le_of_ne (hI k i hi) fun heq => hne ?_
        exact hBB k hk hkB i hi (I k) (hIS k) (fun m hm => heq ▸ hI k m hm) (hI k))
    rw [hval _ (hIS k)] at key
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact key

end GlobalTheory.PolyCycloValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfect
section
open scoped NNReal
open Ideal Finset GlobalTheory.Per.AinfComplete

namespace GlobalTheory.WittTeichComplete

open scoped NNReal in
open _root_.Ideal Finset in
private lemma tails_of_isAdicComplete_span {A : Type*} [CommRing A] (y : A)
    [IsAdicComplete (Ideal.span {y}) A] : _root_.GlobalTheory.Per.AinfComplete.Tails y := by
  have hsum := _root_.GlobalTheory.Per.AinfComplete.summ_of_precomplete y
  unfold _root_.GlobalTheory.Per.AinfComplete.Summ at hsum
  unfold _root_.GlobalTheory.Per.AinfComplete.Tails
  intro b
  choose L hL using fun n => hsum (fun k => b (n + k))
  refine ⟨L, fun n => ?_⟩
  have key : ∀ m, y ^ m ∣ L n - y * L (n + 1) - b n := by
    intro m
    have h₁ := Ideal.mem_span_singleton.1 (hL n (m + 1))
    have h₂ := Ideal.mem_span_singleton.1 (hL (n + 1) m)
    have hs : ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i) =
        b n + y * ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show n + (i + 1) = n + 1 + i by omega]
      ring
    have hd : L n - y * L (n + 1) - b n =
        (L n - ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i)) -
          y * (L (n + 1) - ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i)) := by
      rw [hs]; ring
    rw [hd]
    exact dvd_sub ((pow_dvd_pow y (Nat.le_succ m)).trans h₁) (dvd_mul_of_dvd_right h₂ y)
  have h0 := _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus y _ fun m => Ideal.mem_span_singleton.2 (key m)
  exact (sub_eq_zero.1 h0).symm


open scoped NNReal in
open _root_.Ideal Finset in
theorem _root_.GlobalTheory.WittTeichComplete.main : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
    [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O →
    IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧
      IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔
        Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  intro l _ O _ _ _ _ x _ hc
  haveI := hc
  have hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
    simp [WittVector.constantCoeff]
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.Per.AinfComplete.witt_complete (WittVector.teichmuller l x)
    (hcc ▸ tails_of_isAdicComplete_span x) (fun r hr => _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus x r
      fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))
  refine ⟨h₂, ?_⟩
  rwa [Ideal.span_insert] at h₁

end GlobalTheory.WittTeichComplete
end

