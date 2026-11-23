module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.LetterSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ContinuousBlockDiagEmbedRingHom
section
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

section words

variable {k j ρ : ℕ}

def blockDiagEmbedRingHom (k j ρ : ℕ) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ →+* B.Mat k (j + ρ) where
  toFun x := blk3 x.2 0 0 0 x.1 0 0 0 x.2
  map_one' := Formalism.FourierDecayAlt.P.Ux4.block3_one.symm
  map_mul' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_mul]
    simp
  map_zero' := Formalism.FourierDecayAlt.P.Ux4.block_three_zero_size_eq
  map_add' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_add]
    simp

theorem continuous_blockDiagEmbedRingHom : Continuous (blockDiagEmbedRingHom k j ρ) := by
  show Continuous (fun x : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ => blk3 x.2 0 0 0 x.1 0 0 0 x.2)
  simp only [blk3]
  exact ((continuous_snd.matrix_fromBlocks continuous_const continuous_const continuous_fst).matrix_fromBlocks
    continuous_const continuous_const continuous_snd).matrix_reindex _ _

theorem exp_pair (Y : B.Mat k ρ) :
    NormedSpace.exp ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ) = (NormedSpace.exp Y, 1) := by
  open scoped Norms.Operator in
  ext1
  · exact Prod.fst_exp _
  · exact (Prod.snd_exp _).trans NormedSpace.exp_zero

theorem embG_exp (Y : B.Mat k ρ) :
    embG k j ρ (NormedSpace.exp Y) = NormedSpace.exp (blk3 0 0 0 0 Y 0 0 0 0 : B.Mat k (j + ρ)) := by
  have h := (open scoped Norms.Operator in
    NormedSpace.map_exp (blockDiagEmbedRingHom k j ρ) continuous_blockDiagEmbedRingHom ((Y, 0) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ))
  exact (congrArg (blockDiagEmbedRingHom k j ρ) (exp_pair (j := j) Y)).symm.trans h

theorem blockDiag3_smul_middle (c : ℂ) (Y : B.Mat k ρ) :
    (blk3 0 0 0 0 (c • Y) 0 0 0 0 : B.Mat k (j + ρ)) = c • blk3 0 0 0 0 Y 0 0 0 0 := by
  ext a b
  simp only [blk3, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
  generalize (eB k j ρ).symm a = x
  generalize (eB k j ρ).symm b = y
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;> simp

theorem conj_exp {m : ℕ} (n X : Matrix (Fin m) (Fin m) ℂ) (hn : n * n⁻¹ = 1) :
    n⁻¹ * NormedSpace.exp X * n = NormedSpace.exp (n⁻¹ * X * n) :=
  (Matrix.exp_conj' n X ((Matrix.isUnit_iff_isUnit_det n).2 (Matrix.isUnit_det_of_right_inverse hn))).symm

private lemma Rn_mul_inv' (x : RC k j ρ) : Rn k j ρ x * (Rn k j ρ x)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h0 : (Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)) = 0 := by
    ext a b; rcases b with b | b <;> rfl
  simp only [Rn, blk3, Matrix.det_reindex_self]
  rw [h0, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem conj_letter (x : RC k j ρ) (Y : B.Mat k ρ) (c : ℂ) :
    (Rn k j ρ x)⁻¹ * embG k j ρ (NormedSpace.exp (c • Y)) * Rn k j ρ x =
      NormedSpace.exp (c • cj k j ρ x Y) := by
  rw [embG_exp, blockDiag3_smul_middle, conj_exp _ _ (Rn_mul_inv' x), Matrix.mul_smul, Matrix.smul_mul]
  rfl

end words

section comp

variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdv_comp (hR : SliceRight) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    RdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => RdV (cj k (p + s) ρ ξ.1.2 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [RdV]
  congr 1
  funext t
  rw [hR k p s ρ σ d ξ Z γ' _, conj_letter]

theorem ldv_comp (hL : SliceLeft) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    B.LdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => B.LdV (cj k (p + s) ρ ξ.1.1 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [B.LdV]
  congr 1
  funext t
  rw [hL k p s ρ σ d ξ Z γ' _, ← neg_smul, conj_letter, neg_smul]

theorem rw_comp (hR : SliceRight) :
    ∀ (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E),
      B.Rw v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.Rw (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  := by
  intro v F
  induction v with
  | nil => rfl
  | cons Y v ih =>
    simp only [B.Rw] at ih
    simp only [B.Rw, List.foldr_cons, List.map_cons]
    rw [ih]
    exact rdv_comp hR _ Y

theorem dLR_comp (hL : SliceLeft) (hR : SliceRight) (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E) :
    ∀ u : List (B.Mat k ρ),
      B.dLR u v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.dLR (u.map (cj k (p + s) ρ ξ.1.1)) (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  := by
  intro u
  induction u with
  | nil =>
    simp only [B.dLR, List.foldr_nil, List.map_nil]
    exact rw_comp hR v F
  | cons Y u ih =>
    simp only [B.dLR] at ih
    simp only [B.dLR, List.foldr_cons, List.map_cons]
    rw [ih]
    exact ldv_comp hL _ Y

end comp

theorem wordsId : WordsId := by
  intro hL hR k p s ρ σ d ξ Z E _ _ F u v
  exact dLR_comp hL hR v F u

end PI.UnitaryGroupMassFormula.UsCost
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.ContinuousBlockMatrixThree
section
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost

theorem continuous_block_matrix_three {X : Type*} [TopologicalSpace X] {k j ρ : ℕ}
    {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A22 : X → B.Mat k ρ} {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ}
    {A31 : X → Matrix (Fin j) (Fin j) ℂ} {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : Continuous A11) (h12 : Continuous A12) (h13 : Continuous A13) (h21 : Continuous A21)
    (h22 : Continuous A22) (h23 : Continuous A23) (h31 : Continuous A31) (h32 : Continuous A32)
    (h33 : Continuous A33) :
    Continuous fun x => blk3 (A11 x) (A12 x) (A13 x) (A21 x) (A22 x) (A23 x) (A31 x) (A32 x) (A33 x) := by
  refine continuous_matrix fun a b => ?_
  unfold blk3
  show Continuous fun x => fromBlocks (fromBlocks (A11 x) (A12 x) (A21 x) (A22 x))
    (fromRows (A13 x) (A23 x)) (fromCols (A31 x) (A32 x)) (A33 x)
    ((eB k j ρ).symm a) ((eB k j ρ).symm b)
  rcases (eB k j ρ).symm a with (a' | a') | a' <;> rcases (eB k j ρ).symm b with (b' | b') | b' <;>
    first
    | exact h11.matrix_elem a' b' | exact h12.matrix_elem a' b' | exact h13.matrix_elem a' b'
    | exact h21.matrix_elem a' b' | exact h22.matrix_elem a' b' | exact h23.matrix_elem a' b'
    | exact h31.matrix_elem a' b' | exact h32.matrix_elem a' b' | exact h33.matrix_elem a' b'

theorem continuous_zjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ) :
    Continuous fun Z' : G.Mat s => ZjH σ d η Z' := by
  unfold ZjH Zj
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  refine continuous_matrix fun a b => ?_
  show Continuous fun Z' : G.Mat s => fromBlocks (headH σ d η.2.1 η.2.2) 0 0 (of Z')
    (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)
  rcases finSumFinEquiv.symm a with a' | a' <;> rcases finSumFinEquiv.symm b with b' | b'
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_apply_apply a' b'

theorem rn_mem_of (hR : RadicalParam) (k j ρ : ℕ) (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  unfold RadicalParam at hR
  obtain ⟨-, hrange, hsub⟩ := hR k j ρ
  have hx : Rn k j ρ x ∈ Rset k j ρ := hrange ▸ Set.mem_range_self x
  exact (hsub hx).1

theorem gaXi_mem_of (hM : SliceMem) (hR : RadicalParam) (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ)
    (hZ : G.detM Z ≠ 0) (hγ : γ ∈ B.GV k ρ) : gaXi k ρ σ d ξ Z γ ∈ B.GV k (p + s + ρ) := by
  unfold gaXi
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (rn_mem_of hR _ _ _ _))
      ((hM k (p + s) ρ).1 _ γ (det_zjH_ne hd ξ.2 hZ) hγ)) (rn_mem_of hR _ _ _ _)

theorem gaXi_contAt (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ) (hZ : G.detM Z ≠ 0) :
    ContinuousAt (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
  have hZj := continuous_zjH σ d ξ.2 (s := s)
  have hdet : ((ZjH σ d ξ.2 Z)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 (det_zjH_ne hd ξ.2 hZ)
  have hinvC : ContinuousAt Ring.inverse ((ZjH σ d ξ.2 Z)ᴴ).det := by
    simpa using NormedRing.inverse_continuousAt (Units.mk0 _ hdet)
  have hinv : ContinuousAt (fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ⁻¹) Z :=
    ContinuousAt.comp (g := (Inv.inv : Matrix (Fin (p + s)) (Fin (p + s)) ℂ → _))
      (f := fun Z' : G.Mat s => (ZjH σ d ξ.2 Z')ᴴ) (continuousAt_matrix_inv _ hinvC)
      hZj.matrix_conjTranspose.continuousAt
  let F : Matrix (Fin (p + s)) (Fin (p + s)) ℂ × Matrix (Fin (p + s)) (Fin (p + s)) ℂ → B.Mat k (p + s + ρ) :=
    fun P => (Rn k (p + s) ρ ξ.1.1)⁻¹ *
      blk3 0 0 (P.2 * G.wMat (p + s)) 0 γ 0 (G.wMat (p + s) * P.1) 0 0 * Rn k (p + s) ρ ξ.1.2
  have hF : Continuous F := by
    refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
    exact continuous_block_matrix_three continuous_const continuous_const
      (continuous_snd.matrix_mul continuous_const) continuous_const continuous_const continuous_const
      (continuous_const.matrix_mul continuous_fst) continuous_const continuous_const
  have : (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) =
      F ∘ fun Z' => (ZjH σ d ξ.2 Z', (ZjH σ d ξ.2 Z')ᴴ⁻¹) := by
    funext Z'; rfl
  rw [this]
  exact hF.continuousAt.comp (hZj.continuousAt.prodMk hinv)

theorem offK : OffK := by
  intro hM hR k p s ρ σ d hd E _ _ H O hO hH ξ Z γ hZ hγ hgO q
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[nhds Z] fun _ => (0 : E) := by
    have h1 : ∀ᶠ Z' in nhds Z, gaXi k ρ σ d ξ Z' γ ∈ O :=
      (gaXi_contAt k p s ρ σ d hd ξ Z γ hZ) (hO.mem_nhds hgO)
    have hdc : Continuous fun Z' : G.Mat s => G.detM Z' := by
      unfold G.detM; exact Continuous.matrix_det continuous_id
    have h2 : ∀ᶠ Z' in nhds Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hH _ (gaXi_mem_of hM hR k p s ρ σ d hd ξ Z' γ h2 hγ) h1
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_⟩
  rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
  simp

end PI.UnitaryGroupMassFormula.UsCost
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCost.DerivA
section
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.DA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cd

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

lemma cm_iff {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} :
    ContDiffAt ℝ n F x ↔ ∀ i j, ContDiffAt ℝ n (fun y => F y i j) x :=
  (contDiffAt_pi (Φ := F)).trans (forall_congr' fun _ => contDiffAt_pi)

lemma cm_mul {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by
  rw [cm_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ => (hF i l).mul (hG l j)

lemma c_det {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by
  rw [cm_iff] at hF
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hF _ _)

lemma cm_updateRow {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (j : Fin a)
    (b : Fin a → ℂ) : ContDiffAt ℝ n (fun y => (F y).updateRow j b) x := by
  rw [cm_iff] at hF ⊢
  intro i l
  by_cases hi : i = j
  · subst hi; simp only [updateRow_self]; exact contDiffAt_const
  · simp only [updateRow_ne hi]; exact hF i l

lemma cm_inv {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) (hu : (F x).det ≠ 0) :
    ContDiffAt ℝ n (fun y => (F y)⁻¹) x := by
  rw [cm_iff]
  intro i j
  have e : (fun y => (F y)⁻¹ i j)
      = fun y => ((F y).det)⁻¹ * ((F y).updateRow j (Pi.single i 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  exact ((c_det hF).inv hu).mul (c_det (cm_updateRow hF j _))

lemma cm_conjT {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y)ᴴ) x := by
  rw [cm_iff] at hF ⊢
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).contDiff.contDiffAt.comp x (hF j i)

lemma contDiffAt_block_matrix_two {p s : ℕ} {A : X → Matrix (Fin p) (Fin p) ℂ} {B' : X → Matrix (Fin p) (Fin s) ℂ}
    {C : X → Matrix (Fin s) (Fin p) ℂ} {D : X → Matrix (Fin s) (Fin s) ℂ}
    (hA : ContDiffAt ℝ n A x) (hB : ContDiffAt ℝ n B' x) (hC : ContDiffAt ℝ n C x) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ n (fun y => blk2 (A y) (B' y) (C y) (D y)) x := by
  rw [cm_iff] at hA hB hC hD ⊢
  intro i j
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize finSumFinEquiv.symm i = u
  generalize finSumFinEquiv.symm j = v
  rcases u with a | a <;> rcases v with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂] <;>
    first | exact hA _ _ | exact hB _ _ | exact hC _ _ | exact hD _ _

lemma contDiffAt_block_matrix_three {k j ρ : ℕ} {A11 : X → Matrix (Fin j) (Fin j) ℂ} {A12 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : X → Matrix (Fin j) (Fin j) ℂ} {A21 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : X → B.Mat k ρ}
    {A23 : X → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : X → Matrix (Fin j) (Fin j) ℂ}
    {A32 : X → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : X → Matrix (Fin j) (Fin j) ℂ}
    (h11 : ContDiffAt ℝ n A11 x) (h12 : ContDiffAt ℝ n A12 x) (h13 : ContDiffAt ℝ n A13 x)
    (h21 : ContDiffAt ℝ n A21 x) (h22 : ContDiffAt ℝ n A22 x) (h23 : ContDiffAt ℝ n A23 x)
    (h31 : ContDiffAt ℝ n A31 x) (h32 : ContDiffAt ℝ n A32 x) (h33 : ContDiffAt ℝ n A33 x) :
    ContDiffAt ℝ n (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y)) x := by
  rw [cm_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

end cd

section hd

variable {t : ℝ}

lemma hd_iff {a b : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {F' : Matrix (Fin a) (Fin b) ℂ} :
    HasDerivAt F F' t ↔ ∀ i j, HasDerivAt (fun y => F y i j) (F' i j) t :=
  (hasDerivAt_pi (φ := F)).trans (forall_congr' fun _ => hasDerivAt_pi)

lemma hd_mul {a b c : ℕ} {F : ℝ → Matrix (Fin a) (Fin b) ℂ} {G : ℝ → Matrix (Fin b) (Fin c) ℂ}
    {F' : Matrix (Fin a) (Fin b) ℂ} {G' : Matrix (Fin b) (Fin c) ℂ}
    (hF : HasDerivAt F F' t) (hG : HasDerivAt G G' t) :
    HasDerivAt (fun y => F y * G y) (F' * G t + F t * G') t := by
  rw [hd_iff] at hF hG ⊢
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun l _ => (hF i l).mul (hG l j)

lemma hasDerivAt_block_matrix_three {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by
  rw [hd_iff] at h11 h12 h13 h21 h22 h23 h31 h32 h33 ⊢
  intro i i'
  obtain ⟨a, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨b, rfl⟩ := (eB k j ρ).surjective i'
  simp only [P.Ux4.block3_apply]
  rcases a with (a | a) | a <;> rcases b with (b | b) | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _

lemma hd_invT {a : ℕ} (B : Matrix (Fin a) (Fin a) ℂ) :
    HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) (-Bᴴ) 0 := by
  have hL : HasDerivAt (fun t : ℝ => (1 + t • B)ᴴ) Bᴴ 0 := by
    have e : (fun t : ℝ => (1 + t • B)ᴴ) = fun t => 1 + t • Bᴴ := by
      funext t; simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
    rw [e]
    exact (((hasDerivAt_id' (0 : ℝ)).smul_const Bᴴ).const_add (1 : Matrix (Fin a) (Fin a) ℂ)).congr_deriv (one_smul _ _)
  have hC : ContDiffAt ℝ 1 (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 :=
    cm_inv (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))) (by simp)
  have hCd := (hC.differentiableAt one_ne_zero).hasDerivAt
  have hP := hd_mul hCd hL
  have hcont : ContinuousAt (fun t : ℝ => ((1 + t • B)ᴴ).det) 0 :=
    (c_det (n := 0) (cm_conjT (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))).continuousAt
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), ((1 + t • B)ᴴ).det ≠ 0 := hcont.eventually_ne (by simp)
  have hev : (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) =ᶠ[𝓝 0] fun _ => 1 := by
    filter_upwards [hne] with t ht
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  have h0 : HasDerivAt (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹ * (1 + t • B)ᴴ) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin a) (Fin a) ℂ)).congr_of_eventuallyEq hev
  have hu := h0.unique hP
  simp only [zero_smul, add_zero, Matrix.conjTranspose_one, inv_one, Matrix.mul_one, Matrix.one_mul] at hu
  have : deriv (fun t : ℝ => ((1 + t • B)ᴴ)⁻¹) 0 = -Bᴴ := eq_neg_of_add_eq_zero_left hu.symm
  exact hCd.congr_deriv this

end hd

end PI.UnitaryGroupMassFormula.UsCost.DA
end
end

