module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ExistsUnitVec
section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IntV_single (j : ι) {t : K} (ht : t ∈ S.O) : S.IntV (Pi.single j t) := by
  intro i
  rw [Pi.single_apply]
  split_ifs
  · exact ht
  · exact S.O.zero_mem

theorem IntV_add {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x + y) := fun i => S.O.add_mem (hx i) (hy i)

theorem IntV_sub {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) : S.IntV (x - y) := fun i => S.O.sub_mem (hx i) (hy i)

theorem IntV_smul {x : ι → K} {c : K} (hc : c ∈ S.O) (hx : S.IntV x) : S.IntV (c • x) := fun i => S.O.mul_mem hc (hx i)

theorem cv_add (x y : ι → K) : S.cv (x + y) = S.cv x + S.cv y := by
  funext k
  show S.σ (x k + y k) = S.σ (x k) + S.σ (y k)
  exact map_add _ _ _

theorem cv_sub (x y : ι → K) : S.cv (x - y) = S.cv x - S.cv y := by
  funext k
  show S.σ (x k - y k) = S.σ (x k) - S.σ (y k)
  exact map_sub _ _ _

theorem cv_smul (c : K) (x : ι → K) : S.cv (c • x) = S.σ c • S.cv x := by
  funext k
  show S.σ (c * x k) = S.σ c * S.σ (x k)
  exact map_mul _ _ _

theorem cv_single (j : ι) (t : K) : S.cv (Pi.single j t) = Pi.single j (S.σ t) := by
  funext k
  show S.σ ((Pi.single j t : ι → K) k) = (Pi.single j (S.σ t) : ι → K) k
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem hf_add_left (Γ : Matrix ι ι K) (x x' y : ι → K) : S.hf Γ (x + x') y = S.hf Γ x y + S.hf Γ x' y := by
  unfold hf
  rw [cv_add, add_dotProduct]

theorem hf_add_right (Γ : Matrix ι ι K) (x y y' : ι → K) : S.hf Γ x (y + y') = S.hf Γ x y + S.hf Γ x y' := by
  unfold hf
  rw [mulVec_add, dotProduct_add]

theorem hf_smul_left (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ (c • x) y = S.σ c * S.hf Γ x y := by
  unfold hf
  rw [cv_smul, smul_dotProduct, smul_eq_mul]

theorem hf_smul_right (Γ : Matrix ι ι K) (c : K) (x y : ι → K) : S.hf Γ x (c • y) = c * S.hf Γ x y := by
  unfold hf
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem mulVec_single_apply_hermitian_block_frames (Γ : Matrix ι ι K) (i j : ι) (t : K) :
    (Γ *ᵥ Pi.single j t) i = Γ i j * t := by
  show ∑ k, Γ i k * (Pi.single j t : ι → K) k = Γ i j * t
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem hf_single (Γ : Matrix ι ι K) (i j : ι) (s t : K) :
    S.hf Γ (Pi.single i s) (Pi.single j t) = S.σ s * (Γ i j * t) := by
  unfold hf
  rw [cv_single, ← mulVec_single_apply_hermitian_block_frames Γ i j t]
  show ∑ k, (Pi.single i (S.σ s) : ι → K) k * (Γ *ᵥ Pi.single j t) k = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem exists_not_NU {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ i j, ¬ S.NU (Γ i j) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, j, hij⟩ : ∃ i j, Γ i j ≠ 0 := by
    by_contra h
    push Not at h
    apply h0
    ext a b
    simp [h a b]
  have hdiv : ∀ x : ι → K, S.IntV x → ∀ k, S.NU ((Γ *ᵥ x) k) := by
    intro x hx k
    show S.NU (∑ l, Γ k l * x l)
    apply S.NU_sum
    intro l _
    rw [mul_comm]
    exact S.NU_mul (hx l) (hcon k l)
  have key : ∀ N : ℕ, ∃ x', S.IntV x' ∧
      Γ *ᵥ Pi.single j (1 : K) = S.p ^ N • (Γ *ᵥ x') := by
    intro N
    induction N with
    | zero => exact ⟨Pi.single j 1, S.IntV_single j S.O.one_mem, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      obtain ⟨x', hx', hx'eq⟩ := ih
      obtain ⟨x'', hx'', he⟩ := hU x' hx' (hdiv x' hx')
      refine ⟨x'', hx'', ?_⟩
      rw [hx'eq, he, smul_smul, pow_succ]
  obtain ⟨N, hN⟩ := S.hsep _ (hΓ i j) hij
  obtain ⟨x', hx', heq⟩ := key N
  apply hN
  refine ⟨(Γ *ᵥ x') i, S.IntV_mulVec hΓ hx' i, ?_⟩
  have h1 := congrFun heq i
  rw [Pi.smul_apply, smul_eq_mul, mulVec_single_apply_hermitian_block_frames, mul_one] at h1
  exact h1

theorem exists_unit_vec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) (hU : S.UM Γ) (h0 : Γ ≠ 0) :
    ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by

  have key : ∀ (v : ι → K) (k : ι), S.IntV v → v k = 1 → S.hf Γ v v ∈ S.O →
      S.σ (S.hf Γ v v) = S.hf Γ v v → ¬ S.NU (S.hf Γ v v) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro v k hv hk hO hσ hn
    have hu0 : S.hf Γ v v ≠ 0 := by
      intro hz
      apply hn
      unfold NU
      exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
    have hinvO : (S.hf Γ v v)⁻¹ ∈ S.O := S.hinv _ hO hn
    have hinvσ : S.σ (S.hf Γ v v)⁻¹ = (S.hf Γ v v)⁻¹ := by
      rw [map_inv₀, hσ]
    have hinvn : ¬ ∃ y ∈ S.O, (S.hf Γ v v)⁻¹ = S.p * y := by
      rintro ⟨y, hy, hyeq⟩
      apply S.hone
      refine ⟨y * S.hf Γ v v, S.O.mul_mem hy hO, ?_⟩
      rw [← mul_assoc, ← hyeq, inv_mul_cancel₀ hu0]
    obtain ⟨w, hwO, hw⟩ := S.hnorm _ hinvO hinvσ hinvn
    refine ⟨w • v, k, S.IntV_smul hwO hv, ?_, ?_⟩
    · rw [Pi.smul_apply, hk, smul_eq_mul, mul_one]
      intro hwn
      unfold NU at hwn
      obtain ⟨y, hy, hyeq⟩ := hwn
      apply hinvn
      refine ⟨S.σ w * y, S.O.mul_mem (S.hσO w hwO) hy, ?_⟩
      rw [← hw, hyeq]
      ring
    · rw [S.hf_smul_left, S.hf_smul_right, ← mul_assoc, hw, inv_mul_cancel₀ hu0]
  have hσ2 : S.σ 2 = 2 := by
    rw [← one_add_one_eq_two, map_add (f := _), map_one]
  have h2O : (2 : K) ∈ S.O := by
    have h11 := S.O.add_mem S.O.one_mem S.O.one_mem
    rwa [one_add_one_eq_two] at h11

  have diag : ∀ m : ι, ¬ S.NU (Γ m m) →
      ∃ (a : ι → K) (i : ι), S.IntV a ∧ ¬ S.NU (a i) ∧ S.hf Γ a a = 1 := by
    intro m hm
    have e : S.hf Γ (Pi.single m 1) (Pi.single m 1) = Γ m m := by
      rw [S.hf_single, map_one, one_mul, mul_one]
    refine key (Pi.single m 1) m (S.IntV_single m S.O.one_mem) (Pi.single_eq_same m 1) ?_ ?_ ?_
    · rw [e]; exact hΓ m m
    · rw [e]; exact hH m m
    · rw [e]; exact hm
  obtain ⟨i, j, hij⟩ := S.exists_not_NU hΓ hU h0
  by_cases hi : S.NU (Γ i i)
  swap
  · exact diag i hi
  by_cases hj : S.NU (Γ j j)
  swap
  · exact diag j hj

  have hne : i ≠ j := by
    rintro rfl
    exact hij hi
  have ht0 : Γ i j ≠ 0 := by
    intro hz
    apply hij
    unfold NU
    exact ⟨0, S.O.zero_mem, by rw [hz, mul_zero]⟩
  have hcO : (Γ i j)⁻¹ ∈ S.O := S.hinv _ (hΓ i j) hij
  have h1 : Γ i j * (Γ i j)⁻¹ = 1 := mul_inv_cancel₀ ht0
  have h2 : S.σ (Γ i j)⁻¹ * S.σ (Γ i j) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
  have hval : S.hf Γ (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) =
      Γ i i + 2 + S.σ (Γ i j)⁻¹ * Γ j j * (Γ i j)⁻¹ := by
    rw [S.hf_add_left, S.hf_add_right, S.hf_add_right, S.hf_single, S.hf_single, S.hf_single,
      S.hf_single, map_one, ← hH i j]
    linear_combination h1 + h2
  refine key (Pi.single i 1 + Pi.single j (Γ i j)⁻¹) i
    (S.IntV_add (S.IntV_single i S.O.one_mem) (S.IntV_single j hcO)) ?_ ?_ ?_ ?_
  · rw [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, add_zero]
  · rw [hval]
    exact S.O.add_mem (S.O.add_mem (hΓ i i) h2O) (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) (hΓ j j)) hcO)
  · rw [hval]
    simp only [map_add (f := _), map_mul, hH i i, hH j j, S.hσσ (Γ i j)⁻¹ hcO, hσ2]
    ring
  · rw [hval]
    intro hn
    unfold NU at hn hi hj
    obtain ⟨y, hy, hyeq⟩ := hn
    obtain ⟨a, ha, hae⟩ := hi
    obtain ⟨b, hb, hbe⟩ := hj
    rw [hae, hbe] at hyeq
    have h2inv : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ S.h2
    apply S.hone
    refine ⟨(y - a - S.σ (Γ i j)⁻¹ * b * (Γ i j)⁻¹) * 2⁻¹,
      S.O.mul_mem (S.O.sub_mem (S.O.sub_mem hy ha)
        (S.O.mul_mem (S.O.mul_mem (S.hσO _ hcO) hb) hcO)) S.htwo, ?_⟩
    linear_combination (2 : K)⁻¹ * hyeq - h2inv

end JSetup
end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.FrobStep
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def bd4 {R : Type*} [Zero R] (P : Matrix n n R) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = y.1 then P x.2 y.2 else 0

def bmv0 {R : Type*} [Zero R] [One R] (k : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = 0 ∧ y.1 = k ∧ x.2 = y.2 then 1 else 0

def gmat (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
  fun x w => g.symm (Pi.single w 1) x

end Blocks

def sq (d : ℕ) : ℂ := Complex.I * ((Real.sqrt d : ℝ) : ℂ)

def kmat {m m' : Type} (d : ℕ) (A B : Matrix m m' ℚ) : Matrix m m' ℂ :=
  A.map (fun q => (q : ℂ)) + _root_.Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.sq d • B.map (fun q => (q : ℂ))

def lmat {l : ℕ} [Fact l.Prime] {m m' : Type} (δ : MaximalUnramifiedExtension l) (A B : Matrix m m' ℚ) : Matrix m m' (MaximalUnramifiedExtension l) :=
  A.map (fun q => (q : MaximalUnramifiedExtension l)) + δ • B.map (fun q => (q : MaximalUnramifiedExtension l))

def FrobStep : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (dK : ℕ), 5 ≤ l → ¬ l ∣ dK → dK.Prime → dK % 8 = 7 →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ (ι : ℂ ≃+* ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l), UnrOK (MaximalUnramifiedExtension l) l σ →
    (∀ x, ‖σ x‖ = ‖x‖) ∧ ∃ δ : MaximalUnramifiedExtension l, (δ : ℂ_[l]) = ι (_root_.Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.sq dK) ∧ σ δ = -δ

def RatStep : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g₀ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) →
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))
      (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) →
    ∃ (P₀ : Matrix n n ℂ) (M₁ M₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ) (R₁ R₂ : Matrix n n ℚ) (c : ℚ),
      padicNorm l c = 1 ∧
      gmat g₁ = lam⁻¹ • (bd4 P₀ * kmat dK M₁ M₂) ∧
      (kmat dK M₁ M₂).transpose * bd4 (kmat dK R₁ R₂) * kmat dK M₁ (-M₂) = (c : ℂ) • 1 ∧
      ∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
        (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
        bmv0 k * kmat dK M₁ M₂ = kmat dK M₁ M₂ * kmat dK U₁ U₂

def LocCore : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (dK : ℕ) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (δ : MaximalUnramifiedExtension l), 5 ≤ l → ¬ l ∣ dK →
    (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) → (∀ x, ‖σ x‖ = ‖x‖) → δ ^ 2 = -(dK : MaximalUnramifiedExtension l) → σ δ = -δ →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (M₁ M₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ) (R₁ R₂ : Matrix n n ℚ)
    (c : ℚ), padicNorm l c = 1 →
    (lmat δ M₁ M₂).transpose * bd4 (lmat δ R₁ R₂) * lmat δ M₁ (-M₂) = (c : MaximalUnramifiedExtension l) • 1 →
    (∀ k : Fin 4, ∃ U₁ U₂ : Matrix (Fin 4 × n) (Fin 4 × n) ℚ,
        (∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) ∧
        bmv0 k * lmat δ M₁ M₂ = lmat δ M₁ M₂ * lmat δ U₁ U₂) →
    ∃ T Ti : Matrix n n (MaximalUnramifiedExtension l), T * Ti = 1 ∧ IsUnitaryK σ (bd4 Ti * lmat δ M₁ M₂)

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocPad
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

variable (l : ℕ) [Fact l.Prime]

private theorem norm_alg_lemma (x : ℚ_[l]) : ‖algebraMap ℚ_[l] ℂ_[l] x‖ = ‖x‖ := by
  first
  | exact norm_algebraMap' ℂ_[l] x
  | (rw [← PadicAlgCl.norm_extends l x, ← PadicComplex.norm_extends l]; rfl)
  | (rw [IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l], ← PadicAlgCl.norm_extends l x,
        ← PadicComplex.norm_extends l]; rfl)

private theorem cont_alg_lemma_2 : Continuous (algebraMap ℚ_[l] ℂ_[l]) :=
  (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] ℂ_[l]) (norm_alg_lemma l)).continuous

private theorem closed_rat_lemma_3 (S : Set ℚ_[l]) (hS : IsClosed S) (hq : ∀ r : ℚ, (r : ℚ_[l]) ∈ S)
    (x : ℚ_[l]) : x ∈ S := by
  rw [← hS.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := Padic.rat_dense l x hε
  exact ⟨r, hq r, by rw [dist_eq_norm]; exact hr⟩

theorem algebraMap_mem_Kur (x : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] x ∈ MaximalUnramifiedExtension l := by
  have hK : IsClosed (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    first
    | exact Subfield.isClosed_topologicalClosure _
    | exact isClosed_closure
  refine closed_rat_lemma_3 l {y | algebraMap ℚ_[l] ℂ_[l] y ∈ MaximalUnramifiedExtension l} (hK.preimage (cont_alg_lemma_2 l)) ?_ x
  intro r
  show algebraMap ℚ_[l] ℂ_[l] (r : ℚ_[l]) ∈ MaximalUnramifiedExtension l
  rw [map_ratCast]
  first
  | exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) r
  | exact (MaximalUnramifiedExtension l).ratCast_mem r

def φ : ℚ_[l] →+* MaximalUnramifiedExtension l := (algebraMap ℚ_[l] ℂ_[l]).codRestrict (MaximalUnramifiedExtension l) (algebraMap_mem_Kur l)

def ψ : ℤ_[l] →+* MaximalUnramifiedExtension l := (φ l).comp PadicInt.Coe.ringHom

theorem norm_φ (x : ℚ_[l]) : ‖φ l x‖ = ‖x‖ := by
  exact norm_alg_lemma l x

theorem norm_ψ (x : ℤ_[l]) : ‖ψ l x‖ = ‖x‖ := by
  exact norm_φ l (x : ℚ_[l])

theorem norm_ψ_le (x : ℤ_[l]) : ‖ψ l x‖ ≤ 1 := by
  rw [norm_ψ]
  exact x.norm_le_one

theorem continuous_φ : Continuous (φ l) := by
  exact (AddMonoidHomClass.isometry_of_norm (φ l) (norm_φ l)).continuous

theorem σ_φ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℚ_[l]) : σ (φ l x) = φ l x := by
  have hσc : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ hσ).continuous
  refine closed_rat_lemma_3 l {y | σ (φ l y) = φ l y}
    (isClosed_eq (hσc.comp (continuous_φ l)) (continuous_φ l)) ?_ x
  intro r
  show σ (φ l (r : ℚ_[l])) = φ l (r : ℚ_[l])
  rw [map_ratCast, map_ratCast]

theorem σ_ψ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : ℤ_[l]) : σ (ψ l x) = ψ l x := by
  exact σ_φ l σ hσ (x : ℚ_[l])

theorem norm_natCast_Kur (k : ℕ) : ‖(k : MaximalUnramifiedExtension l)‖ = ‖(k : ℚ_[l])‖ := by
  rw [← map_natCast (φ l) k, norm_φ]

theorem norm_l_Kur : ‖(l : MaximalUnramifiedExtension l)‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Kur, Padic.norm_p]

theorem toZMod_eq_zero_iff (z : ℤ_[l]) : PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
  first
  | rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  | rw [LocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_eq_one_iff (z : ℤ_[l]) : ‖z‖ = 1 ↔ PadicInt.toZMod z ≠ 0 := by
  rw [Ne, toZMod_eq_zero_iff]
  constructor
  · intro h h'
    rw [h] at h'
    exact lt_irrefl _ h'
  · intro h
    exact le_antisymm z.norm_le_one (not_lt.1 h)

theorem toZMod_natCast (k : ℕ) : PadicInt.toZMod (k : ℤ_[l]) = (k : ZMod l) := by
  exact map_natCast PadicInt.toZMod k

theorem odd_l (h5 : 5 ≤ l) : (2 : ZMod l) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod l) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod l) l] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem exists_sqrt (h5 : 5 ≤ l) (t : ℤ_[l]) (s : ZMod l) (hs : s ≠ 0) (ht : PadicInt.toZMod t = s ^ 2) :
    ∃ z : ℤ_[l], z * z = t := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[l], PadicInt.toZMod a = s :=
    ⟨(s.val : ℤ_[l]), by rw [toZMod_natCast, ZMod.natCast_zmod_val]⟩
  set F : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.C t with hF
  have h1 : Polynomial.aeval a F = a ^ 2 - t := by simp [hF]
  have h2 : Polynomial.aeval a (Polynomial.derivative F) = 2 * a := by
    first
    | (norm_num [hF]; done)
    | (simp [hF]; left; norm_num; done)
    | (simp [hF]; left; rfl)
    | (simp only [hF, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Polynomial.aeval_X, map_natCast]; norm_num)
  have n1 : ‖a ^ 2 - t‖ < 1 := by
    rw [← toZMod_eq_zero_iff l, map_sub, map_pow, ha, ht, sub_self]
  have n2 : ‖(2 : ℤ_[l]) * a‖ = 1 := by
    rw [norm_eq_one_iff l, map_mul, map_ofNat, ha]
    exact mul_ne_zero (odd_l l h5) hs
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h1, h2, n2, one_pow]; exact n1)
  have hz2 : z ^ 2 = t := by
    have : z ^ 2 - t = 0 := by simpa [hF] using hz
    exact sub_eq_zero.1 this
  exact ⟨z, by rw [← _root_.sq]; exact hz2⟩

theorem exists_norm (h5 : 5 ≤ l) (dK : ℕ) (hld : ¬ l ∣ dK) (a : ℤ_[l]) (ha : ‖a‖ = 1) :
    ∃ x y : ℤ_[l], x * x + dK * (y * y) = a := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hd : ((dK : ℕ) : ZMod l) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
  have hA : PadicInt.toZMod a ≠ 0 := (norm_eq_one_iff l a).1 ha
  obtain ⟨x0, y0, hxy⟩ : ∃ x0 y0 : ZMod l, x0 ^ 2 + (dK : ZMod l) * y0 ^ 2 = PadicInt.toZMod a := by
    have hR : Fintype.card (ZMod l) % 2 = 1 := by
      rw [ZMod.card]
      exact Nat.odd_iff.1 ((Fact.out : l.Prime).odd_of_ne_two (by omega))
    have h2 : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2).degree = 2 :=
      Polynomial.degree_C_mul_X_pow 2 hd
    have hg : (Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2
        - Polynomial.C (PadicInt.toZMod a)).degree = 2 := by
      rw [Polynomial.degree_sub_C (by rw [h2]; first | decide | norm_num | exact WithBot.coe_lt_coe.2 (by norm_num)), h2]
    obtain ⟨x0, y0, h⟩ := FiniteField.exists_root_sum_quadratic (f := Polynomial.X ^ 2)
      (g := Polynomial.C (dK : ZMod l) * Polynomial.X ^ 2 - Polynomial.C (PadicInt.toZMod a))
      (Polynomial.degree_X_pow 2) hg hR
    refine ⟨x0, y0, ?_⟩
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at h
    linear_combination h
  by_cases hx0 : x0 = 0
  · subst hx0
    have hy0 : y0 ≠ 0 := by
      rintro rfl
      apply hA
      rw [← hxy]
      simp

    obtain ⟨w, hw⟩ := exists_sqrt l h5 ((dK : ℤ_[l]) * a) ((dK : ZMod l) * y0) (mul_ne_zero hd hy0)
      (by
        rw [map_mul, toZMod_natCast]
        linear_combination (-(dK : ZMod l)) * hxy)
    have hdu : IsUnit (dK : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, norm_eq_one_iff l, toZMod_natCast]
      exact hd
    obtain ⟨u, hu⟩ := hdu
    have key : (u : ℤ_[l]) * ↑u⁻¹ = 1 := u.mul_inv
    rw [← hu] at hw
    refine ⟨0, ↑u⁻¹ * w, ?_⟩
    rw [← hu]
    linear_combination ((u : ℤ_[l]) * ↑u⁻¹ * ↑u⁻¹) * hw + ((u : ℤ_[l]) * ↑u⁻¹ + 1) * a * key
  ·
    obtain ⟨x, hx⟩ := exists_sqrt l h5 (a - dK * ((y0.val : ℤ_[l]) * (y0.val : ℤ_[l]))) x0 hx0
      (by
        rw [map_sub, map_mul, map_mul, toZMod_natCast, toZMod_natCast, ZMod.natCast_zmod_val]
        linear_combination -hxy)
    exact ⟨x, y0.val, by rw [hx]; ring⟩

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

