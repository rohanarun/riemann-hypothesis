module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.SphericalEisensteinCover

theorem isCompact_entries {A : Type} [TopologicalSpace A] (a b : ℕ) {Ω : Set A} (hΩ : IsCompact Ω) :
    IsCompact {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} := by
  have e : {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} =
      (Set.univ.pi fun _ => Set.univ.pi fun _ => Ω : Set (Matrix (Fin a) (Fin b) A)) :=
    Set.ext fun ω => ⟨fun h i _ k _ => h i k, fun h i k => h i trivial k trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ

variable {k A : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A] (s : A →+* A)

theorem cT_add {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M + N) = cT s M + cT s N := by
  ext; simp [cT]

theorem cT_neg {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (-M) = -cT s M := by
  ext; simp [cT]

theorem cT_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M - N) = cT s M - cT s N := by
  ext; simp [cT]

theorem cT_smul (hk : ∀ (c : k) x, s (c • x) = c • s x) {a b : ℕ} (c : k) (M : Matrix (Fin a) (Fin b) A) :
    cT s (c • M) = c • cT s M := by
  ext; simp [cT, hk]

theorem cT_cT (hs : ∀ x, s (s x) = x) {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (cT s M) = M := by
  ext; simp [cT, hs]

variable {j m : ℕ} (K : Matrix (Fin m) (Fin m) A)

theorem cT_pair (hs : ∀ x, s (s x) = x) (hK : cT s K = K) (u v : Matrix (Fin j) (Fin m) A) :
    cT s (u * (K * cT s v)) = v * (K * cT s u) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT s hs, hK, Matrix.mul_assoc]

theorem skew_rest (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (X y p : Matrix (Fin j) (Fin m) A) (c : Matrix (Fin j) (Fin j) A)
    (hc : c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p))) = 0) :
    cT s (c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) =
    -(c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) := by
  have hcc : cT s c = -c - (X + (y + p)) * (K * cT s (X + (y + p))) := by
    calc cT s c = (c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p)))) - c - (X + (y + p)) * (K * cT s (X + (y + p))) := by abel
      _ = _ := by rw [hc]; abel
  simp only [cT_add, cT_sub, cT_smul s hk, cT_pair s K hs hK, hcc]
  simp only [cT_add, cT_pair s K hs hK, Matrix.mul_add, Matrix.add_mul, smul_add, neg_add, sub_eq_add_neg]
  module

theorem rel_half (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (b : Matrix (Fin j) (Fin m) A) (z : Matrix (Fin j) (Fin j) A) (hz : cT s z = -z) :
    (z - (2⁻¹ : k) • (b * (K * cT s b))) + cT s (z - (2⁻¹ : k) • (b * (K * cT s b))) + b * (K * cT s b) = 0 := by
  rw [cT_sub, cT_smul s hk, cT_pair s K hs hK, hz]
  module

theorem final_eq (X y p : Matrix (Fin j) (Fin m) A) (c r z ws : Matrix (Fin j) (Fin j) A)
    (hR : c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p) = r + (z + ws)) :
    (-((2⁻¹ : k) • (X * (K * cT s X))) - r) + c - (-X) * (K * cT s (X + (y + p))) =
      (z - (2⁻¹ : k) • (y * (K * cT s y))) + (ws - (2⁻¹ : k) • (p * (K * cT s p))) - y * (K * cT s p) := by
  have h := sub_eq_zero.2 hR
  rw [← sub_eq_zero]
  rw [← h, Matrix.neg_mul]
  module

end GlobalTheory.SphEis.SphericalEisensteinCover

namespace GlobalTheory.SphEis


open GlobalTheory.SphEis.SphericalEisensteinCover in
theorem cover_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr lv hlv
  classical
  have hcm := hFr.cm
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hcm x)
  have hk : ∀ (c : F) x, sigR (AF F) σ (c • x) = c • sigR (AF F) σ x := fun c x =>
    map_smul (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) c x
  have hsc : Continuous (sigR (AF F) σ) := by
    have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a x => rfl
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _

  have hJ₀ : cT (σ : E →+* E) J₀ = J₀ := Matrix.ext fun i k => hFr.herm₀.1 i k
  have hJ₀i : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
    have hu : IsUnit J₀.det := IsUnit.mk0 _ hFr.herm₀.2
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ₀]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  have hK : cT (sigR (AF F) σ) (adMat F J₀⁻¹) = adMat F J₀⁻¹ := congrArg (adMat F) hJ₀i

  set K : Matrix (Fin m) (Fin m) (AF F ⊗[F] E) := adMat F J₀⁻¹ with hKdef
  have hplus : ∀ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), plus σ J₀ b = K * cT (sigR (AF F) σ) b := fun b => rfl
  obtain ⟨Ω₁, B₁, hΩ₁, hrect⟩ := _root_.GlobalTheory.SphEis.cover_rect_adMat F E σ hcm j m
  obtain ⟨Ω₂, B₂, hΩ₂, hskew⟩ := GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact F E σ hcm j
  set S₁ : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₁} with hS₁
  set S₂ : Set (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₂} with hS₂
  have hS₁c : IsCompact S₁ := isCompact_entries j m hΩ₁
  have hS₂c : IsCompact S₂ := isCompact_entries j j hΩ₂
  have hcont : ∀ i k, Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k := fun i k => by
    have h1 : Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        q.1 * (K * cT (sigR (AF F) σ) q.1) :=
      continuous_fst.matrix_mul (continuous_const.matrix_mul (continuous_fst.matrix_map hsc).matrix_transpose)
    have hsm : Continuous fun x : AF F ⊗[F] E => (2⁻¹ : F) • x := by
      simp only [Algebra.smul_def]; exact continuous_const.mul continuous_id
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    exact ((continuous_apply_apply i k).comp continuous_snd).sub (hsm.comp (h1.matrix_elem i k))
  set Ω₃ : Set (AF F ⊗[F] E) := Ω₁ ∪ ⋃ (i : Fin j) (k : Fin j),
    (fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k) '' (S₁ ×ˢ S₂) with hΩ₃
  have hΩ₃c : IsCompact Ω₃ :=
    hΩ₁.union (isCompact_iUnion fun i => isCompact_iUnion fun k => (hS₁c.prod hS₂c).image (hcont i k))
  obtain ⟨V, hV, hVmem⟩ := _root_.GlobalTheory.SphEis.exists_isCompact_of_crd_mem F E σ n J j m C D Z J₀ hFr Ω₃ hΩ₃c
  refine ⟨V, B₁ * B₂, hV, fun μ => ?_⟩

  obtain ⟨Y₁, hY₁, hcov₁⟩ := hrect μ
  obtain ⟨Y₂, hY₂, hY₂sk, hcov₂⟩ := hskew μ
  have crd2 := _root_.GlobalTheory.SphEis.UnipCrd.exists_unipRad_crd F E σ n J j m C D Z J₀ hFr
  have hrel : ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (z : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) z = -z →
      (z - (2⁻¹ : F) • (b * plus σ J₀ b)) + cT (sigR (AF F) σ) (z - (2⁻¹ : F) • (b * plus σ J₀ b)) +
        b * plus σ J₀ b = 0 :=
    fun b z hz => rel_half (sigR (AF F) σ) K hs hk hK b z hz
  let f : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → GAd σ J := fun q =>
    if hq : cT (sigR (AF F) σ) q.2 = -q.2 then Classical.choose (crd2 q.1 _ (hrel q.1 q.2 hq)) else 1
  have hf : ∀ b z, cT (sigR (AF F) σ) z = -z → f (b, z) ∈ unipRad σ J C ∧
      Crd σ J C D Z J₀ (f (b, z)) b (z - (2⁻¹ : F) • (b * plus σ J₀ b)) := by
    intro b z hz
    simp only [f, dif_pos hz]
    exact Classical.choose_spec (crd2 b _ (hrel b z hz))
  refine ⟨(Y₁ ×ˢ Y₂).image f, ?_, ?_, fun u hu => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul hY₁ hY₂ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hY₁)).trans (le_of_eq ?_)
    simp only [add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  · intro y hy
    obtain ⟨⟨b, z⟩, hq, rfl⟩ := Finset.mem_image.1 hy
    exact (hf b z (hY₂sk z (Finset.mem_product.1 hq).2)).1
  obtain ⟨b, c, hbc, hcond⟩ := _root_.GlobalTheory.SphEis.exists_crd_of_mem_unipRad F E σ n J j m C D Z J₀ hFr u hu
  obtain ⟨x₀, y, hy, ω, hω, hb⟩ := hcov₁ b
  set t := tor F E fun i => (μ i : ℤ) with ht
  have hcond' : c + cT (sigR (AF F) σ) c + (adMat F x₀ + (y + t.1 * ω)) *
      (K * cT (sigR (AF F) σ) (adMat F x₀ + (y + t.1 * ω))) = 0 := by
    rw [← hb]; exact hcond
  have hRsk := skew_rest (sigR (AF F) σ) K hs hk hK (adMat F x₀) y (t.1 * ω) c hcond'
  obtain ⟨x₁, hx₁, z, hz, ωs, hωs, hωsΩ, hR⟩ := hcov₂ _ hRsk

  let c₀ : Matrix (Fin j) (Fin j) E := -((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) - x₁
  have hneg : adMat F (-x₀) = -adMat F x₀ := by ext; simp
  have hc₀ : adMat F c₀ = -((2⁻¹ : F) • (adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)))) - adMat F x₁ := by
    have e1 : adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) = adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)) := by
      simp only [adMat, Matrix.map_mul]; rfl
    have e2 : adMat F ((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) =
        (2⁻¹ : F) • adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) :=
      Matrix.map_smul _ _ (fun a => map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (2⁻¹ : F) a) _
    have e3 : ∀ P Q : Matrix (Fin j) (Fin j) E, adMat F (P - Q) = adMat F P - adMat F Q := fun P Q => by ext; simp
    have e4 : ∀ P : Matrix (Fin j) (Fin j) E, adMat F (-P) = -adMat F P := fun P => by ext; simp
    simp only [c₀]
    rw [e3, e4, e2, e1]
  have hx₁' : cT (sigR (AF F) σ) (adMat F x₁) = -adMat F x₁ := by
    show adMat F (cT (σ : E →+* E) x₁) = _
    rw [hx₁]; ext; simp
  have hγrel : adMat F c₀ + cT (sigR (AF F) σ) (adMat F c₀) + adMat F (-x₀) * plus σ J₀ (adMat F (-x₀)) = 0 := by
    rw [hc₀, hneg, hplus]
    simp only [cT_sub, cT_neg, cT_smul _ hk, cT_pair _ K hs hK, hx₁', Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    module
  obtain ⟨γ, hγU, hγC⟩ := crd2 (adMat F (-x₀)) (adMat F c₀) hγrel
  have hγrat := _root_.GlobalTheory.SphEis.mem_ratPts_of_crd_rat F E σ n J j m C D Z J₀ hFr γ (-x₀) c₀ hγC

  obtain ⟨w, hwU, hwC⟩ := crd2 ω (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) (hrel ω ωs hωs)
  have hwV : w ∈ V := hVmem w ω _ hwC (fun i k => Or.inl (hω i k))
    (fun i k => Or.inr (Set.mem_iUnion₂.2 ⟨i, k, ⟨(ω, ωs), ⟨hω, hωsΩ⟩, rfl⟩⟩))

  have hy'mem : f (y, z) ∈ (Y₁ ×ˢ Y₂).image f := Finset.mem_image_of_mem f (Finset.mem_product.2 ⟨hy, hz⟩)
  obtain ⟨hy'U, hy'C⟩ := hf y z (hY₂sk z hz)

  have law := _root_.GlobalTheory.SphEis.crd_law F E σ n J j m C D Z J₀ hFr lv hlv
  have h1 := (law γ u (adMat F (-x₀)) (adMat F c₀) b c hγC).1 hbc
  have hcj := (law w w ω _ 0 0 hwC).2.2 t
  have h2 := (law (f (y, z)) _ y _ _ _ hy'C).1 hcj
  have eb : adMat F (-x₀) + b = y + t.1 * ω := by rw [hb, hneg]; abel
  have ec : adMat F c₀ + c - adMat F (-x₀) * plus σ J₀ b =
      (z - (2⁻¹ : F) • (y * plus σ J₀ y)) + t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 -
        y * plus σ J₀ (t.1 * ω) := by
    have hconj : t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 =
        t.1 * ωs * cT (sigR (AF F) σ) t.1 - (2⁻¹ : F) • ((t.1 * ω) * plus σ J₀ (t.1 * ω)) := by
      simp only [hplus, Formalism.UG.cT_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hconj, hc₀, hneg, hb]
    simp only [hplus]
    exact final_eq (sigR (AF F) σ) K (adMat F x₀) y (t.1 * ω) c (adMat F x₁) z (t.1 * ωs * cT (sigR (AF F) σ) t.1) hR
  rw [eb, ec] at h1
  have heq := (law (γ * u) _ _ _ 0 0 h1).2.1 h2
  refine ⟨γ, hγrat, hγU, f (y, z), hy'mem, w, hwV, hwU, ?_⟩
  rw [heq]
  simp only [mul_assoc]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCoordsTwoChartsTransition
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

theorem mem_prime_dual_iff {K : Type} [Field K] (p : Ideal (DualNumber K)) [hp : p.IsPrime] (x : DualNumber K) :
    x ∈ p ↔ x.fst = 0 := by
  constructor
  · intro hx
    by_contra h
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem p hx hu)
  · intro h
    have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext h rfl
    have h2 : x * x = 0 := by rw [hx, TrivSqZeroExt.inr_mul_inr]
    exact (hp.mem_or_mem (h2 ▸ p.zero_mem)).elim id id

theorem dual_pt_eq {K : Type} [Field K] (p q : Sp (DualNumber K)) : p = q := by
  apply PrimeSpectrum.ext
  ext x
  have hp : p.asIdeal.IsPrime := p.isPrime
  have hq : q.asIdeal.IsPrime := q.isPrime
  exact (mem_prime_dual_iff (K := K) p.asIdeal x).trans (mem_prime_dual_iff (K := K) q.asIdeal x).symm

theorem top_le_of_red {K : Type} [Field K] {T : Scheme.{0}} (φ : DualNumber K →+* K) (w : Sp (DualNumber K) ⟶ T)
    {V : T.Opens} (h : ⊤ ≤ (spMap φ ≫ w) ⁻¹ᵁ V) : ⊤ ≤ w ⁻¹ᵁ V := by
  intro p _
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have e : p = spMap φ q := dual_pt_eq _ _
  have hq := h (Set.mem_univ q)
  rw [e]
  exact hq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem ev_resU {T : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ T) {U V : T.Opens} (e : V ≤ U)
    (hV : ⊤ ≤ z ⁻¹ᵁ V) (hU : ⊤ ≤ z ⁻¹ᵁ U) (u : Γ(T, U)ˣ) :
    GlobalTheory.FlagMod.ev z V hV (res e u).val = GlobalTheory.FlagMod.ev z U hU u.val :=
  GlobalTheory.FlagMod.ev_res z e hV hU u.val

theorem tAt_congr {K : Type} [CommRing K] (k k' : X.F.J) {w w' : Sp K ⟶ X.YY} (e : w = w')
    (h : ⊤ ≤ w ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) (h' : ⊤ ≤ w' ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    X.F.TAt k k' w h = X.F.TAt k k' w' h' := by
  subst e; rfl


open Classical in
theorem ev_div_g (i i' : M.K.bundle.ι) (k k' : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X)
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k')))
    (hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i')) (hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k')) :
    GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k)
                 (i', flagIdx M _ k')).val =
      GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
        (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val := by
  set e := exOf Dw (FlagTan.kap Dw) 0
  have hL : ⊤ ≤ z ⁻¹ᵁ (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k) ⊓
      ((L₀ X Z (FlagTan.kap Dw)).pull M.σ).U (flagIdx M _ k')) := fun p hp => ⟨(hg hp).1.2, (hg hp).2.2⟩
  have hh1 : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ ((L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k PUnit.unit) ⊓
      (L₀ X Z (FlagTan.kap Dw)).U (flagIdx M _ k' PUnit.unit)) := fun p hp => ⟨mem_pIdx.2 (hh hp).1, mem_pIdx.2 (hh hp).2⟩
  have hh2 : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := fun p hp => hh hp
  have eL : GlobalTheory.FlagMod.ev z _ hL (((L₀ X Z (FlagTan.kap Dw)).pull M.σ).g (flagIdx M _ k) (flagIdx M _ k')).val =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix)).val := by
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ z hL hh1]
    rw [GlobalTheory.FlagMod.ev_pull_g _ _ _ _ (z ≫ M.σ) hh1 hh2]
    refine (X.F.ev_LL_g e k k' _ hh2).trans ?_
    rw [tAt_congr k k' (Category.assoc _ _ _) hh2 hh]
  have ei : ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ (-e ix) : Kˣ) : K)⁻¹ =
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ e ix : Kˣ) : K) := by
    rw [← Units.val_inv_eq_inv_val, ← Finset.prod_inv_distrib]
    simp only [zpow_neg, inv_inv]
  dsimp only [LB.div]
  refine ((GlobalTheory.FlagMod.ev z _ hg).map_mul _ _).trans (congrArg₂ (· * ·) (ev_resU z _ hg hK _)
    ((map_units_inv (GlobalTheory.FlagMod.ev z _ hg) _).trans ?_))
  refine (congrArg Inv.inv (ev_resU z _ hg hL _)).trans ?_
  rw [eL, ei]

theorem red_comp_eq {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P : FrPt Xo c K}
    (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) :
    spMap (FlagTan.red c K).toRingHom ≫ zw = z := by
  have hx : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun p hp => by
    have := ho hp
    rw [M.off_eq] at this
    exact this
  have h1 : (spMap (FlagTan.red c K).toRingHom ≫ zw) ≫ M.σ = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z)]
    simp only [Category.assoc]
    have e1 : zw ≫ M.σ ≫ inc₀ X Z = X.ptY w := hl
    have e2 : z ≫ M.σ ≫ inc₀ X Z = X.ptY P := hP
    rw [e1, e2]
    exact X.ptY_frMap hw
  exact (M.existsUnique_lift (z ≫ M.σ) hx).unique h1 rfl

theorem top_le_of_isDef {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
    {P : FrPt Xo c K} (hP : z ≫ toFlag M = X.ptY P) {w : FrPt Xo c (DualNumber K)} (hw : FlagTan.IsDef P w)
    (zw : Sp (DualNumber K) ⟶ M.X) (hl : zw ≫ toFlag M = X.ptY w) {V : M.X.Opens} (hV : ⊤ ≤ z ⁻¹ᵁ V) :
    ⊤ ≤ zw ⁻¹ᵁ V :=
  top_le_of_red _ zw (by rw [red_comp_eq M z ho hP hw zw hl]; exact hV)


open Classical in
theorem ksRel_of_ksRel {i i' : M.K.bundle.ι} {k k' : X.F.J} {K : Type} [Field K] {z : Sp K ⟶ M.X}
    (hs : ⊤ ≤ z ⁻¹ᵁ ksOpen M i k) (hs' : ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k')
    (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓
      (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) {x' : K}
    (hx' : KSRel M i' k' z x') :
    KSRel M i k z (GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g
      (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x') := by
  intro _ P Q t v zv O hO g hz hzv hk hQ ht hv hl
  have ho : ⊤ ≤ z ⁻¹ᵁ M.off := fun p hp => (hs hp).1
  have hi' : ⊤ ≤ z ⁻¹ᵁ M.K.bundle.U i' := fun p hp => (hs' hp).2.1
  have hK : ⊤ ≤ z ⁻¹ᵁ (M.K.bundle.U i ⊓ M.K.bundle.U i') := fun p hp => ⟨(hs hp).2.1, (hs' hp).2.1⟩
  have hk' : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k' := fun p hp => mem_pIdx.1 (mem_pIdx.1 (hs' hp).2.2)
  have hh : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') := GlobalTheory.FlagMod.le_preimage_inf hk hk'
  have hlies := hQ.lies
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd Q) hlies.1 k' hk'
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c K
  have hB := hQ.frBor hQ' hh
  have ht' := g1 _ _ _ _ _ (g2 _ _ _ hB) ht
  have hP : z ≫ toFlag M = X.ptY P := FlagCover.eq_ptY (hlies.frBor ht)
  have hzv' : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := fun b =>
    GlobalTheory.FlagMod.le_preimage_inf (hzv b) (top_le_of_isDef M z ho hP (hv.isDef b) (zv b) (hl b) hi')
  have hz' : ⊤ ≤ z ⁻¹ᵁ (O ⊓ M.K.bundle.U i') := GlobalTheory.FlagMod.le_preimage_inf hz hi'
  have key := hx' P Q' _ v zv (O ⊓ M.K.bundle.U i') inf_le_right (fun a => resG M.X inf_le_left (g a)) hz' hzv' hk'
    hQ' ht' hv hl
  have hdet : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) (O ⊓ M.K.bundle.U i') (hzv' _)
      (resG M.X inf_le_left (g a))).snd) = Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd := by
    ext a b
    simp only [Matrix.of_apply]
    rw [evalPt_res]
  rw [hdet] at key
  have hJ : evalPt z O hz (M.K.jacobian i hO g) = GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) := by
    rw [← evalPt_res z inf_le_left hz hz', CanonLB.resG_jacobian,
      CanonLB.jacobian_change _ i i' (inf_le_left.trans hO) inf_le_right, map_mul]
    congr 1
    exact evalPt_res z _ hK hz' _
  rw [ev_div_g M i i' k k' z hg hK hh, hJ]
  have hu : (∏ ix, ((X.F.TAt k k' (z ≫ toFlag M) hh)⁻¹ * t) ix ^ exOf Dw (FlagTan.kap Dw) 0 ix) =
      (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)⁻¹ *
        ∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ix _ => ?_
    rw [Pi.mul_apply, Pi.inv_apply, mul_zpow, inv_zpow]
  rw [hu, Units.val_mul] at key
  have hTT := Units.mul_inv (∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix)
  linear_combination (GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      ((∏ ix, X.F.TAt k k' (z ≫ toFlag M) hh ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K)) * key +
    ((∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix : Kˣ) : K) * GlobalTheory.FlagMod.ev z _ hK (M.K.bundle.g i i').val *
      evalPt z (O ⊓ M.K.bundle.U i') hz' (M.K.jacobian i' inf_le_right fun a => resG M.X inf_le_left (g a)) * hTT

end GlobalTheory.CompHS


open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS in
theorem GlobalTheory.CompHS.ksRel_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (i i' : M.K.bundle.ι) (k k' : X.F.J) (K : Type) [Field K] (z : Sp K ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ ksOpen M i k → ⊤ ≤ z ⁻¹ᵁ ksOpen M i' k' → ∀ (hg : ⊤ ≤ z ⁻¹ᵁ ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k) ⊓ (LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).U (i', flagIdx M _ k'))) (x x' : K), KSRel M i k z x → KSRel M i' k' z x' → x = GlobalTheory.FlagMod.ev z _ hg ((LB.div M.K.bundle ((L₀ X Z (GlobalTheory.FlagTan.kap Dw)).pull M.σ)).g (i, flagIdx M _ k) (i', flagIdx M _ k')).val * x' := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS i i' k k' K _ z hs hs' hg x x' hx hx'
  exact (_root_.GlobalTheory.CompHS.ksRel_unique_ne_zero M hKS i k K z hs).1 x _ hx (ksRel_of_ksRel M hs hs' hg hx')
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColon
section
set_option autoImplicit false
noncomputable section
open NumberField

namespace GlobalTheory.IdxMap

theorem dets_eq_detSpan (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p L = GlobalTheory.BetaEx.detSpan L := by
  unfold GlobalTheory.IdxTensor.dets GlobalTheory.BetaEx.detSpan
  congr 1
  ext d
  rw [GlobalTheory.BetaEx.mem_detSet]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Matrix.of y, hy, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem idx_map_eq_colon_dets : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  intro F V _ _ _ _ _ _ p φ hφ L N
  set v : Fin p → V := fun i => φ (Pi.basisFun F (Fin p) i) with hv
  have hli : LinearIndependent F v :=
    (Pi.basisFun F (Fin p)).linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφ)
  have hcoord : φ.restrictScalars (𝓞 F) = GlobalTheory.LatIndexDeg.coordMap F v := by
    refine LinearMap.ext fun x => ?_
    rw [GlobalTheory.LatIndexDeg.coordMap_apply, LinearMap.restrictScalars_apply]
    conv_lhs => rw [← (Pi.basisFun F (Fin p)).sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hv, map_sum, map_smul]
  have hω := GlobalTheory.LatIndexDeg.ιMulti_ne_zero_of_li v hli
  have hℓ : Function.Injective (GlobalTheory.LatIndexDeg.lineMap F (exteriorPower.ιMulti F p v)) :=
    fun s t e => smul_left_injective F hω e
  unfold GlobalTheory.FlatCM.idx
  rw [hcoord, GlobalTheory.LatIndexDeg.detSpan_map_coord, GlobalTheory.LatIndexDeg.detSpan_map_coord,
    GlobalTheory.LatIndexDeg.colon_map_of_injective _ hℓ, dets_eq_detSpan, dets_eq_detSpan]

end GlobalTheory.IdxMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePlaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAddCharUnramified_of_splitsCompletelyAbovePlace : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  first | exact @GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | exact GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully | (intros; apply GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully <;> assumption)
end

