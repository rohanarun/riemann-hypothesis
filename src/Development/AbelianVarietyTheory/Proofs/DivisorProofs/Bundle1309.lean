module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

namespace GlobalTheory.RigidTranslate

open GlobalTheory.PolTranslate ReciprocityTheory.ChartRestriction.G.DVR

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem toUnit_inv_mul_self (a : 𝟙_ (Over S) ⟶ A) (T : Over S) :
    (toUnit T ≫ a⁻¹) * (toUnit T ≫ a) = 1 := by
  rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one]

theorem transl_inv_comp_transl (a : 𝟙_ (Over S) ⟶ A) : transl a⁻¹ ≫ transl a = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]

theorem kTriv_pull_transl (x : 𝟙_ (Over S) ⟶ A) {L : LB A.left} (hL : L.IsLB) (h : Out.KTriv A L) :
    Out.KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x⁻¹).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x⁻¹))) V
  have k₂ : T ◁ transl x⁻¹ ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_inv_comp_transl, Category.comp_id]
  have k₃ : T ◁ transl x⁻¹ ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end

theorem kTriv_rigTransl_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro S A _ L hL a h R _ s y hy
  refine kTriv_pull_transl a hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

end GlobalTheory.RigidTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOnFibreUniqueTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.TensorTorsionNsmul

open scoped TensorProduct

variable {L : Type} [AddCommGroup L]

theorem tmul_surjective (n : ℕ) (x : ZMod n ⊗[ℤ] L) : ∃ a : L, (1 : ZMod n) ⊗ₜ[ℤ] a = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul r a =>
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective r
    refine ⟨m • a, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, _root_.mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add _ _ _⟩

theorem eq_nsmul_of_tmul_eq_zero {n : ℕ} {a : L} (h : (1 : ZMod n) ⊗ₜ[ℤ] a = 0) : ∃ d, a = n • d := by
  let e : ZMod n ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(n : ℤ)}) :=
    (Int.quotientSpanNatEquivZMod n).symm.toAddEquiv.toIntLinearEquiv
  have he : e 1 = 1 := map_one (Int.quotientSpanNatEquivZMod n).symm
  have h1 := congrArg (fun y => TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(n : ℤ)})
    (LinearMap.rTensor L e.toLinearMap y)) h
  simp only [LinearMap.rTensor_tmul, map_zero, LinearEquiv.coe_coe, he,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h1
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨d, -, hd⟩ := h1
  exact ⟨d, by rw [← hd, natCast_zsmul]⟩

theorem tmul_nsmul_eq_zero (n : ℕ) (d : L) : (1 : ZMod n) ⊗ₜ[ℤ] (n • d) = 0 := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, _root_.mul_one, ZMod.natCast_self,
    TensorProduct.zero_tmul]

variable {G : Type} [Group G]

theorem map_nsmul_of_add {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c) (m : ℕ) (a : L) :
    φ (m • a) = φ a ^ m := by
  have h0 : φ 0 = 1 := by
    have := hφ 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction m with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ m ih => rw [succ_nsmul, hφ, ih, pow_succ]

theorem tmul_eq_tmul_iff {n : ℕ} {φ : L → G} (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b) (a c : L) :
    (1 : ZMod n) ⊗ₜ[ℤ] a = 1 ⊗ₜ c ↔ φ a = φ c := by
  have e : φ a = φ (a - c) * φ c := by rw [← hφ, sub_add_cancel]
  rw [e, mul_eq_right, hk, ← sub_eq_zero, ← TensorProduct.tmul_sub]
  constructor
  · exact eq_nsmul_of_tmul_eq_zero
  · rintro ⟨d, hd⟩
    rw [hd]
    exact tmul_nsmul_eq_zero n d

def matchMap (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) : (ZMod n ⊗[ℤ] L) →ₗ[ZMod n] (ZMod n ⊗[ℤ] L) :=
  LinearMap.liftBaseChange (ZMod n)
    (AddMonoidHom.mk' (fun b => (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b)) (fun b b' => by
      rw [← TensorProduct.tmul_add, tmul_eq_tmul_iff hφ hk, hφ, Classical.choose_spec (hr _),
        Classical.choose_spec (hr _), Classical.choose_spec (hr _), hφ']) : L →+ ZMod n ⊗[ℤ] L).toIntLinearMap

theorem matchMap_tmul (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hr : ∀ b, ∃ c, φ c = φ' b) (b c : L) :
    matchMap n φ φ' hφ hφ' hk hr ((1 : ZMod n) ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  rw [matchMap, LinearMap.liftBaseChange_tmul, one_smul]
  change (1 : ZMod n) ⊗ₜ[ℤ] Classical.choose (hr b) = _ ↔ _
  rw [tmul_eq_tmul_iff hφ hk, Classical.choose_spec (hr b), eq_comm]

theorem exists_equiv (n : ℕ) (φ φ' : L → G) (hφ : ∀ a c, φ (a + c) = φ a * φ c)
    (hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c) (hk : ∀ a, φ a = 1 ↔ ∃ b, a = n • b)
    (hk' : ∀ a, φ' a = 1 ↔ ∃ b, a = n • b) (hr : ∀ b, ∃ c, φ c = φ' b) (hr' : ∀ c, ∃ b, φ' b = φ c) :
    ∃ e : (ZMod n ⊗[ℤ] L) ≃ₗ[ZMod n] (ZMod n ⊗[ℤ] L), ∀ b c, e (1 ⊗ₜ b) = 1 ⊗ₜ c ↔ φ c = φ' b := by
  let f := matchMap n φ φ' hφ hφ' hk hr
  let g := matchMap n φ' φ hφ' hφ hk' hr'
  have hfg : ∀ x, g (f x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr b
    obtain ⟨d, hd⟩ := hr' c
    rw [(matchMap_tmul n φ φ' hφ hφ' hk hr b c).2 hc, (matchMap_tmul n φ' φ hφ' hφ hk' hr' c d).2 hd,
      tmul_eq_tmul_iff hφ' hk', hd, hc]
  have hgf : ∀ x, f (g x) = x := by
    intro x
    obtain ⟨b, rfl⟩ := tmul_surjective n x
    obtain ⟨c, hc⟩ := hr' b
    obtain ⟨d, hd⟩ := hr c
    rw [(matchMap_tmul n φ' φ hφ' hφ hk' hr' b c).2 hc, (matchMap_tmul n φ φ' hφ hφ' hk hr c d).2 hd,
      tmul_eq_tmul_iff hφ hk, hd, hc]
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext hgf) (LinearMap.ext hfg), fun b c => ?_⟩
  exact matchMap_tmul n φ φ' hφ hφ' hk hr b c

end GlobalTheory.UPel.TensorTorsionNsmul

namespace GlobalTheory.UPel

open scoped TensorProduct

end GlobalTheory.UPel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviElem

open Matrix

section Abstract

variable {R : Type} [CommRing R]

def cols2 {n : ℕ} (x y : Fin n → R) : Matrix (Fin n) (Fin 2) R := Matrix.of fun i k => ![x i, y i] k

theorem conj_eq {n κ : Type} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ] (s : R →+* R)
    (P : Matrix n κ R) (Q : Matrix κ n R) (hPQ : P * Q = 1) (J : Matrix n n R) (D : Matrix κ κ R)
    (hK : Dᵀ * (Pᵀ * J * P.map s) * D.map s = Pᵀ * J * P.map s) :
    (P * D * Q)ᵀ * J * (P * D * Q).map s = J := by
  have h1 : (P * D * Q)ᵀ * J * (P * D * Q).map s = Qᵀ * (Dᵀ * (Pᵀ * J * P.map s) * D.map s) * Q.map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h1, hK]
  have h2 : Qᵀ * (Pᵀ * J * P.map s) * Q.map s = (P * Q)ᵀ * J * (P * Q).map s := by
    simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
  rw [h2, hPQ]
  simp

def swap2 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

def blk {b : ℕ} (g : Matrix (Fin b) (Fin b) R) (t u : R) : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) R :=
  fromBlocks g 0 0 (diagonal ![t, u])

theorem levi_mat {b : ℕ} (s : R →+* R) (hs : ∀ z, s (s z) = z) (ι : Matrix (Fin (b + 2)) (Fin b) R)
    (x y : Fin (b + 2) → R) (J : Matrix (Fin (b + 2)) (Fin (b + 2)) R) (J₁ : Matrix (Fin b) (Fin b) R)
    (Q : Matrix (Fin b ⊕ Fin 2) (Fin (b + 2)) R) (hQP : Q * fromCols ι (cols2 x y) = 1)
    (hK : (fromCols ι (cols2 x y))ᵀ * J * (fromCols ι (cols2 x y)).map s = fromBlocks J₁ 0 0 swap2)
    (l : Rˣ) (G : GL (Fin b) R) (hG : (G : Matrix (Fin b) (Fin b) R)ᵀ * J₁ * (G : Matrix (Fin b) (Fin b) R).map s = J₁) :
    ∃ m : GL (Fin (b + 2)) R, (m : Matrix _ _ R)ᵀ * J * (m : Matrix _ _ R).map s = J ∧
      (m : Matrix _ _ R) *ᵥ x = l.1 • x ∧ (m : Matrix _ _ R) *ᵥ y = s (l⁻¹).1 • y ∧
      (m : Matrix _ _ R) * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
  set P := fromCols ι (cols2 x y) with hP
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP
  set D := blk (G : Matrix (Fin b) (Fin b) R) l.1 (s (l⁻¹).1)
  set D' := blk ((G⁻¹ : GL (Fin b) R) : Matrix (Fin b) (Fin b) R) (l⁻¹).1 (s l.1)
  have hDD : D * D' = 1 := by
    simp only [D, D', blk, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      diagonal_mul_diagonal]
    rw [← fromBlocks_one]
    congr 1
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal, ← map_mul]
  have hDD' : D' * D = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hDD
  refine ⟨⟨P * D * Q, P * D' * Q, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · calc P * D * Q * (P * D' * Q) = P * D * (Q * P) * D' * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD, Matrix.mul_one, hPQ]
  · calc P * D' * Q * (P * D * Q) = P * D' * (Q * P) * D * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_assoc P, hDD', Matrix.mul_one, hPQ]
  · refine conj_eq s P Q hPQ J D ?_
    rw [hK]
    simp only [D, blk, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.map_zero _ (map_zero s), diagonal_map (map_zero s),
      diagonal_transpose, hG]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swap2, diagonal, Matrix.mul_apply, Fin.sum_univ_two, hs, ← map_mul]
  all_goals simp only [Units.val_mk]
  · have hx : P *ᵥ Pi.single (Sum.inr 0) 1 = x := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDx : D *ᵥ Pi.single (Sum.inr 0) 1 = l.1 • Pi.single (Sum.inr 0) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hx, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDx, mulVec_smul]
  · have hy : P *ᵥ Pi.single (Sum.inr 1) 1 = y := by
      rw [mulVec_single_one]; ext i; simp [P, cols2, Matrix.col]
    have hDy : D *ᵥ Pi.single (Sum.inr 1) 1 = s (l⁻¹).1 • Pi.single (Sum.inr 1) 1 := by
      rw [mulVec_single_one]; ext (i | i)
      · simp [D, blk, Matrix.col]
      · fin_cases i <;> simp [D, blk, diagonal, Matrix.col]
    rw [← hy, mulVec_mulVec, show P * D * Q * P = P * D by rw [Matrix.mul_assoc, hQP, Matrix.mul_one],
      ← mulVec_mulVec, hDy, mulVec_smul]
  · set E1 := fromRows (1 : Matrix (Fin b) (Fin b) R) (0 : Matrix (Fin 2) (Fin b) R) with hE1
    have hι : P * E1 = ι := by
      simp [P, E1, fromCols_mul_fromRows]
    have hDι : D * E1 = E1 * (G : Matrix (Fin b) (Fin b) R) := by
      rw [hE1, fromRows_mul]
      ext (i | i) j <;> simp [D, blk, Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    have h3 : P * D * Q * (P * E1) = P * D * E1 := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (P * D), hQP, Matrix.mul_one]
    have fin : P * D * Q * ι = ι * (G : Matrix (Fin b) (Fin b) R) := by
      rw [← hι, h3, Matrix.mul_assoc, hDι, ← Matrix.mul_assoc]
    exact fin

end Abstract

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_gram {n : ℕ} {p q : Type} [Fintype p] [Fintype q] (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (A : Matrix (Fin n) p E) (B : Matrix (Fin n) q E) (j : p) (k : q) :
    (Aᵀ * J * B.map σ) j k = form σ J (fun i => A i j) (fun i => B i k) := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_flip (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (herm : ∀ i j, σ (J j i) = J i j) (v w : Fin n → E) : form σ J v w = σ (form σ J w v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [herm]
  ring

theorem det_ne_of_sig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set Dg : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fromBlocks 1 0 0 (-1)
  have hD : Dg * Dg = 1 := by simp [Dg, fromBlocks_multiply, fromBlocks_one]
  have h1 : Dg * Aᵀ * M * A.map star = 1 := by
    have : Dg * Aᵀ * M * A.map star = Dg * (Aᵀ * M * A.map star) := by simp only [Matrix.mul_assoc]
    rw [this, hA, hD]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr hrs))).1 h1
  exact Matrix.det_ne_zero_of_left_inverse (B := A.map star * Dg * Aᵀ) (by simpa [Matrix.mul_assoc] using h2)

theorem gram_block (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {b : ℕ} {Y : Spc F E (b + 2)}
    {Y₁ : Spc F E b} (herm : ∀ i j, σ (Y.J j i) = Y.J i j) {H : Plane E (b + 2) b} {i₀ i₁ : ℕ}
    (hA : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (fromCols H.ι (cols2 H.x H.y))ᵀ * Y.J * (fromCols H.ι (cols2 H.x H.y)).map σ = fromBlocks Y₁.J 0 0 swap2 := by
  have hmap : (fromCols H.ι (cols2 H.x H.y)).map σ = fromCols (H.ι.map σ) ((cols2 H.x H.y).map σ) := by
    ext i (j | j) <;> rfl
  have ho : ∀ j, (fun i => H.ι i j) = H.ι *ᵥ Pi.single j 1 := fun j => by rw [mulVec_single_one]; rfl
  have orth' : ∀ j, form σ Y.J (fun i => H.ι i j) H.x = 0 ∧ form σ Y.J (fun i => H.ι i j) H.y = 0 := fun j => by
    rw [ho]; exact hA.orth _
  rw [hmap, transpose_fromCols, fromRows_mul, fromRows_mul_fromCols, hA.gram]
  congr 1
  · ext j k
    rw [form_gram, ho]
    fin_cases k
    · simpa [cols2] using (hA.orth (Pi.single j 1)).1
    · simpa [cols2] using (hA.orth (Pi.single j 1)).2
  · ext k j
    rw [form_gram, form_flip σ hσ herm]
    fin_cases k
    · simp [cols2, (orth' j).1]
    · simp [cols2, (orth' j).2]
  · ext k k'
    rw [form_gram]
    fin_cases k <;> fin_cases k' <;>
      simp [cols2, swap2, hA.xx, hA.yy, hA.xy, form_flip σ hσ herm H.y H.x]

theorem cA_invol {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add u v hu hv => simp [map_add (f := _), hu, hv]

theorem levi_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∃ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, ∀ l g₀, IsLevi H l g₀ (m l g₀) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  have hPf : P.map f = fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hK' : (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)))ᵀ * incM F G.V.J *
      (fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y))).map (cA σ).toRingHom =
      fromBlocks (incM F G₁.V.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ).toRingHom = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F G.V.J = G.V.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]
  have key : ∀ (l : (AE F E)ˣ) (g₀ : UA σ G₁.V.J), ∃ m : GL (Fin (b + 2)) (AE F E),
      (m : Matrix _ _ (AE F E))ᵀ * incM F G.V.J * (m : Matrix _ _ (AE F E)).map (cA σ).toRingHom = incM F G.V.J ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.x = l.1 • incV F H.x ∧
      (m : Matrix _ _ (AE F E)) *ᵥ incV F H.y = (cA σ).toRingHom (l⁻¹).1 • incV F H.y ∧
      (m : Matrix _ _ (AE F E)) * incM F H.ι = incM F H.ι * (g₀.1 : Matrix (Fin b) (Fin b) (AE F E)) :=
    fun l g₀ => levi_mat (cA σ).toRingHom (cA_invol hσ) (incM F H.ι) (incV F H.x) (incV F H.y) (incM F G.V.J)
      (incM F G₁.V.J) (Q.map f) hQP' hK' l g₀.1 g₀.2
  choose m hm using key
  exact ⟨fun l g₀ => ⟨m l g₀, (hm l g₀).1⟩, fun l g₀ => ⟨(hm l g₀).2.1, (hm l g₀).2.2.1, (hm l g₀).2.2.2⟩⟩

end Field

end GlobalTheory.LeviElem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.Unfold

theorem lintegral_chart_le_mul_fundSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro E _ _ _ r X x0 x FF A m Φ ho0 ho hF hA hAO hΦ hΓ hB hm
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM := ReciprocityTheory.ChartRestriction.G.AR.Up.measInv_holds (E := E)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x A).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (measurableSet_satFrames X ho hA hAO)
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x A _ hb, hB b hb y hy]
  have h1 : ∫⁻ z in A, Φ (cpt X x z) ∂muF X x = ∫⁻ z, ψ (cpt X x z) ∂muF X x := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho]
  rw [h1, ← hM r X x0 x ho0 ho ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB,
    ← lintegral_const_mul m (f := fun z => Φ (cpt X x0 z)) (hΦ.comp hc)]
  refine setLIntegral_mono ((hΦ.comp hc).const_mul m) fun z hz => ?_
  set y := cpt X x0 z with hy_def
  have hy : y ∈ X.dom := hF.2.1 hz
  let S : Set (GL (Fin r) E) := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r,
    lact γ (cpt X x z) = rmul (cpt X x z') b}
  let T : Set X.Γ := {γ | lact γ.1 y ∈ satFrames X x A}
  by_cases hT : T.Nonempty
  swap
  · have h0 : ∀ γ : X.Γ, ψ (lact γ.1 y) = 0 := fun γ =>
      Set.indicator_of_notMem (s := satFrames X x A) (fun h => hT ⟨γ, h⟩) Φ
    simp [h0]
  obtain ⟨γ0, hγ0⟩ := hT
  obtain ⟨z0, hz0, b0, hb0, e0⟩ := hγ0
  have hpt : ∀ γ : X.Γ, ψ (lact γ.1 y) ≤ T.indicator (fun _ => Φ y) γ := by
    intro γ
    by_cases hγ : γ ∈ T
    · rw [Set.indicator_of_mem hγ]
      show (satFrames X x A).indicator Φ _ ≤ _
      rw [Set.indicator_of_mem (s := satFrames X x A) hγ Φ, hΓ γ.1 γ.2 y hy]
    · rw [Set.indicator_of_notMem hγ]
      exact le_of_eq (Set.indicator_of_notMem (s := satFrames X x A) hγ Φ)
  have hTS : T.encard ≤ S.encard := by
    let f : X.Γ → GL (Fin r) E := fun γ => γ.1 * γ0.1⁻¹
    have hinj : Set.InjOn f T := fun a _ b _ h => Subtype.ext (mul_right_cancel h)
    rw [← hinj.encard_image]
    refine Set.encard_le_encard ?_
    rintro _ ⟨γ, ⟨z1, hz1, b1, hb1, e1⟩, rfl⟩
    refine ⟨X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2), z0, hz0, z1, hz1,
      rmul b1 (ExtFPf.invF X b0), ExtFPf.mul_mem X hb1 (ExtFPf.invF_mem X hb0), ?_⟩
    have e0' : cpt X x z0 = rmul (lact γ0.1 y) (ExtFPf.invF X b0) := by
      rw [e0, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb0, ExtFPf.rmul_oneF]
    show lact (γ.1 * γ0.1⁻¹) (cpt X x z0) = _
    rw [e0', FundSetPf.lact_rmul, FundSetPf.lact_mul, FundSetPf.lact_inv, e1, ExtFPf.rmul_assoc]
  calc ∑' γ : X.Γ, ψ (lact γ.1 y) ≤ ∑' γ : X.Γ, T.indicator (fun _ => Φ y) γ := ENNReal.tsum_le_tsum hpt
    _ = (T.encard : ℝ≥0∞) * Φ y := by rw [← tsum_subtype, ENNReal.tsum_set_const]
    _ ≤ m * Φ y := by
      gcongr
      exact le_trans (by exact_mod_cast hTS) hm

end GlobalTheory.Unfold
end

