module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepOfIsometric
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.IsomT

variable {X : Scheme.{0}}

theorem res_twice {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom (u : Γ(X, U))) =
    (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom (u : Γ(X, U))
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem units_ext_cover {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) {W : X.Opens}
    {f g : Γ(X, W)ˣ} (h : ∀ i, res (inf_le_left : W ⊓ V i ≤ W) f = res inf_le_left g) : f = g := by
  apply Units.ext
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
    fun i => ?_
  exact congrArg Units.val (h i)

theorem exists_glue {ι : Type} (V : ι → X.Opens) (hc : ⨆ i, V i = ⊤) (W : X.Opens)
    (f : ∀ i, Γ(X, W ⊓ V i)ˣ)
    (hf : ∀ i j, res (inf_le_left : (W ⊓ V i) ⊓ (W ⊓ V j) ≤ W ⊓ V i) (f i) =
      res inf_le_right (f j)) :
    ∃ u : Γ(X, W)ˣ, ∀ i, res inf_le_left u = f i := by
  have hcov : W ≤ ⨆ i, W ⊓ V i := by
    rw [← inf_iSup_eq, hc, inf_top_eq]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => ((f i : Γ(X, W ⊓ V i))))
    (fun i j => congrArg Units.val (hf i j))
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ V i) W
    (fun i => homOfLE inf_le_left) hcov (fun i => (((f i)⁻¹ : Γ(X, W ⊓ V i)ˣ) : Γ(X, W ⊓ V i)))
    (fun i j => by
      have := congrArg Units.val (congrArg (·⁻¹) (hf i j))
      rw [← map_inv, ← map_inv] at this
      exact this)
  have hst : s * t = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ V i) W (fun i => homOfLE inf_le_left) hcov _ _
      fun i => ?_
    rw [map_mul, map_one, hs i, ht i]
    exact (f i).mul_inv
  refine ⟨⟨s, t, hst, by show (t : Γ(X, W)) * s = 1; rw [mul_comm]; exact hst⟩, fun i => Units.ext ?_⟩
  exact hs i

theorem ofMem {V U : X.Opens} (h : ∀ x, x ∈ V → x ∈ U) : V ≤ U := by
  intro x hx
  exact h x hx

end GlobalTheory.CompanionTheory.MPDict.IsomT

namespace GlobalTheory.CompanionTheory.MPDict

open IsomT

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k)
    {W W' : (MP ℤ m n).Opens} (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    res h' (blockUnit i j h) = blockUnit i j (h'.trans h) := by
  unfold blockUnit
  exact res_twice _ _ _

theorem res_mul_prod (c c' : ∀ k, Bk n k) (e : Fin (m + 1) → ℤ)
    {W W' : (MP ℤ m n).Opens} (x : Γ(MP ℤ m n, W)ˣ)
    (H : ∀ k, W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) (h' : W' ≤ W) :
    res h' (x * ∏ k, blockUnit (c k) (c' k) (H k) ^ e k) =
      res h' x * ∏ k, blockUnit (c k) (c' k) (h'.trans (H k)) ^ e k := by
  rw [map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, res_blockUnit]

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorProduct
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.TensRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens} (h : W' ≤ W)
    (h' : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    Semi.res h (blockUnit i j h') = blockUnit i j (h.trans h') :=
  DVR.res_res' _ _ _

def mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) :
    Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ :=
  Semi.res (inf_le_inf_right _ inf_le_left) u * Semi.res (inf_le_inf_right _ inf_le_right) v

theorem ev_mulUnit {P Q C : (MP ℤ m n).Opens} (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C)) :
    CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ Q ⊓ C) (mulUnit u v : Γ(MP ℤ m n, P ⊓ Q ⊓ C)ˣ) y =
      CxPts.ev (mpStr ℤ m n) σ₀ (P ⊓ C) (u : Γ(MP ℤ m n, P ⊓ C)) y *
        CxPts.ev (mpStr ℤ m n) σ₀ (Q ⊓ C) (v : Γ(MP ℤ m n, Q ⊓ C)) y := by
  rw [mulUnit, Units.val_mul, CxPts.ev_mul]
  exact congrArg₂ (· * ·) (CxPts.ev_res _ hy _) (CxPts.ev_res _ hy _)

theorem frame_mulUnit {P P' Q Q' C : (MP ℤ m n).Opens} (g : Γ(MP ℤ m n, P ⊓ P')ˣ) (g' : Γ(MP ℤ m n, Q ⊓ Q')ˣ)
    (u : Γ(MP ℤ m n, P ⊓ C)ˣ) (u' : Γ(MP ℤ m n, P' ⊓ C)ˣ) (v : Γ(MP ℤ m n, Q ⊓ C)ˣ) (v' : Γ(MP ℤ m n, Q' ⊓ C)ˣ)
    (a₁ : P ⊓ P' ⊓ C ≤ P' ⊓ C) (a₂ : P ⊓ P' ⊓ C ≤ P ⊓ P') (a₃ : P ⊓ P' ⊓ C ≤ P ⊓ C)
    (b₁ : Q ⊓ Q' ⊓ C ≤ Q' ⊓ C) (b₂ : Q ⊓ Q' ⊓ C ≤ Q ⊓ Q') (b₃ : Q ⊓ Q' ⊓ C ≤ Q ⊓ C)
    (hu : Semi.res a₁ u' = Semi.res a₂ g * Semi.res a₃ u) (hv : Semi.res b₁ v' = Semi.res b₂ g' * Semi.res b₃ v)
    (d₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P' ⊓ Q' ⊓ C) (d₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ (P' ⊓ Q'))
    (d₃ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ Q ⊓ C) (f₁ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ P ⊓ P') (f₂ : P ⊓ Q ⊓ (P' ⊓ Q') ≤ Q ⊓ Q') :
    Semi.res d₁ (mulUnit u' v') = Semi.res d₂ (Semi.res f₁ g * Semi.res f₂ g') * Semi.res d₃ (mulUnit u v) := by
  have l₁ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ P ⊓ P' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_left inf_le_left)
  have l₂ : P ⊓ Q ⊓ (P' ⊓ Q') ⊓ C ≤ Q ⊓ Q' ⊓ C := inf_le_inf_right _ (inf_le_inf inf_le_right inf_le_right)
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  exact (congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)

theorem mono_mulUnit {P Q : (MP ℤ m n).Opens} {c c' : ∀ k, Bk n k} (a b : Fin (m + 1) → ℤ)
    (u : Γ(MP ℤ m n, P ⊓ mchart c)ˣ) (u' : Γ(MP ℤ m n, P ⊓ mchart c')ˣ)
    (v : Γ(MP ℤ m n, Q ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, Q ⊓ mchart c')ˣ)
    (a₁ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c) (a₂ : P ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ mchart c')
    (b₁ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c) (b₂ : Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ mchart c')
    (ta : ∀ k, P ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (tb : ∀ k, Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k)))
    (hu : Semi.res a₁ u = Semi.res a₂ u' * ∏ k, blockUnit (c k) (c' k) (ta k) ^ a k)
    (hv : Semi.res b₁ v = Semi.res b₂ v' * ∏ k, blockUnit (c k) (c' k) (tb k) ^ b k)
    (d₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c) (d₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ Q ⊓ mchart c')
    (td : ∀ k, P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) :
    Semi.res d₁ (mulUnit u v) = Semi.res d₂ (mulUnit u' v') * ∏ k, blockUnit (c k) (c' k) (td k) ^ (a k + b k) := by
  have l₁ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ P ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_left
  have l₂ : P ⊓ Q ⊓ (mchart c ⊓ mchart c') ≤ Q ⊓ (mchart c ⊓ mchart c') := inf_le_inf_right _ inf_le_right
  have e₁ := congrArg (Semi.res l₁) hu
  have e₂ := congrArg (Semi.res l₂) hv
  simp only [map_mul, map_prod, map_zpow, DVR.res_res'] at e₁ e₂
  simp only [mulUnit, map_mul, DVR.res_res']
  refine ((congrArg₂ (· * ·) e₁ e₂).trans (mul_mul_mul_comm _ _ _ _)).trans (congrArg (HMul.hMul _) ?_)
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [res_blockUnit, res_blockUnit, ← zpow_add]

end GlobalTheory.CompanionTheory.MPDict.TensRep

namespace GlobalTheory.CompanionTheory.MPDict

open TensRep

theorem isHermRep_tens : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M N : HermLB (mpStr ℤ m n)) (A B : Geo.HermLine (Bk n)),
    IsHermRep M A → IsHermRep N B → IsHermRep (M.tens N) (A.tensor B) := by
  rintro m n M N A B ⟨u, hu₁, hu₂, hu₃⟩ ⟨v, hv₁, hv₂, hv₃⟩
  refine ⟨fun p c => mulUnit (u p.1 c) (v p.2 c), ?_, ?_, ?_⟩
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ c
    exact frame_mulUnit _ _ _ _ _ _ _ _ _ _ _ _ (hu₁ i j c) (hv₁ i' j' c) _ _ _ _ _
  · rintro ⟨i, i'⟩ c c'
    exact mono_mulUnit A.a B.a _ _ _ _ _ _ _ _ _ _ (hu₂ i c c') (hv₂ i' c c') _ _ _
  · rintro ⟨i, i'⟩ c y z hz hy
    have hy' := mem_ptsIn_inf.1 hy
    have h₁ := mem_ptsIn_inf.1 hy'.1
    have e₁ := hu₃ i c y z hz (mem_ptsIn_inf.2 ⟨h₁.1, hy'.2⟩)
    have e₂ := hv₃ i' c y z hz (mem_ptsIn_inf.2 ⟨h₁.2, hy'.2⟩)
    have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k => (hz k (c k)).1.1 (ptsIn_mono (mchart_le c k) hy'.2)
    have hp : ∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k) =
        (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) * ∏ k, ‖z ⟨k, c k⟩‖ ^ B.a k := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => zpow_add₀ (norm_ne_zero_iff.2 (hz0 k)) _ _
    have hev := ev_mulUnit (u i c) (v i' c) hy
    change A.h z * B.h z = (∏ k, ‖z ⟨k, c k⟩‖ ^ (A.a k + B.a k)) *
      ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ N.B.U i' ⊓ mchart c)
        (mulUnit (u i c) (v i' c) : Γ(MP ℤ m n, M.B.U i ⊓ N.B.U i' ⊓ mchart c)ˣ) y‖ *
      Real.exp (((M.φ σ₀).φ i y + (N.φ σ₀).φ i' y) / 2)
    rw [e₁, e₂, hev, hp, norm_mul, add_div, Real.exp_add]
    ring

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicSumNondegenerateFrame
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem hypOne_mul_hypOne_of_mul_eq_one {K : Type} [Field K] {M : ℕ} {A B : Matrix (Fin M) (Fin M) K}
    (h : A * B = 1) : hypOne A * hypOne B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, Matrix.one_apply,
      ← Matrix.mul_apply, h, Fin.ext_iff]

theorem isHermND_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    all_goals first
      | exact hJ.1 i j
      | simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
          hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one]
  · have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
    have h1 : hypOne J * hypOne J⁻¹ = 1 :=
      hypOne_mul_hypOne_of_mul_eq_one (Matrix.mul_nonsing_inv J hu)
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2

theorem e0_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨linearIndependent_unique_iff.2 ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · ext a b
    simp [gramE, hE, hform, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem hypOne_isHermND_and_e0_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (_hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) :=
  ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimit
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.TailProd

theorem term_mono {ι : Type} [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι)
    (hτ : Summable (fun v => |τ v - 1|)) (hp : Summable (fun v => |p v - 1|))
    (hM0 : ∀ v, 0 ≤ Mv v) (hτ0 : ∀ v, 0 ≤ τ v) (hp0 : ∀ v, 0 ≤ p v)
    (hle : ∀ v, v ∉ S → τ v * p v ≤ Mv v) :
    Monotone (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) := by
  intro S₁ S₂ h12
  have hU : S ∪ S₁ ⊆ S ∪ S₂ := Finset.union_subset_union_right h12
  dsimp only
  rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι τ (S ∪ S₁) (S ∪ S₂) hτ hU,
    GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι p (S ∪ S₁) (S ∪ S₂) hp hU]
  have hX : ∏ v ∈ (S ∪ S₂) \ S, Mv v =
      (∏ v ∈ (S ∪ S₁) \ S, Mv v) * ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    have hD : ((S ∪ S₂) \ S) \ ((S ∪ S₁) \ S) = (S ∪ S₂) \ (S ∪ S₁) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [← Finset.prod_sdiff (Finset.sdiff_subset_sdiff hU (Finset.Subset.refl S)), hD, mul_comm]
  have hΔ : (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), τ v) * (∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), p v) ≤
      ∏ v ∈ (S ∪ S₂) \ (S ∪ S₁), Mv v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (hτ0 v) (hp0 v))
      (fun v hv => hle v (fun hvS => (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ hvS)))
  have hX1 : 0 ≤ ∏ v ∈ (S ∪ S₁) \ S, Mv v := Finset.prod_nonneg fun v _ => hM0 v
  have hT : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, τ v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => τ v.1)
      (hτ.comp_injective Subtype.val_injective)).2.2.2 fun v => hτ0 v.1
  have hP : 0 ≤ ∏' v : {v // v ∉ S ∪ S₂}, p v.1 :=
    (GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {v // v ∉ S ∪ S₂} (fun v => p v.1)
      (hp.comp_injective Subtype.val_injective)).2.2.2 fun v => hp0 v.1
  rw [hX]
  set X := ∏ v ∈ (S ∪ S₁) \ S, Mv v
  set D := (S ∪ S₂) \ (S ∪ S₁)
  set T := ∏' v : {v // v ∉ S ∪ S₂}, τ v.1
  set P := ∏' v : {v // v ∉ S ∪ S₂}, p v.1
  calc X * ((∏ v ∈ D, τ v) * T * ((∏ v ∈ D, p v) * P))
      = X * ((∏ v ∈ D, τ v) * (∏ v ∈ D, p v)) * (T * P) := by ring
    _ ≤ X * (∏ v ∈ D, Mv v) * (T * P) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hX1) (mul_nonneg hT hP)

theorem iSup_partial_mul_tails : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι),
    Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) →
    (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) →
    ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) =
      ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  intro ι _ Mv τ p S hMs hτs hps hM0 hτ0 hp0 hle
  have hmono := GlobalTheory.CompanionTheory.TailProd.term_mono Mv τ p S hτs hps hM0 hτ0 hp0 hle
  have hg : Tendsto (fun S' : Finset ι => S ∪ S') atTop atTop :=
    tendsto_atTop_mono (fun S' => (Finset.subset_union_right : S' ⊆ S ∪ S')) tendsto_id
  have hM := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one Mv hMs).comp hg
  have hT := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one τ hτs).comp hg
  have hP := (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.tendsto_tprod_compl_one p hps).comp hg
  have hlim : Tendsto (fun S' : Finset ι => (∏' v : {v // v ∉ S}, Mv v.1) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * (∏' v : {v // v ∉ S ∪ S'}, p v.1) /
        ∏' v : {v // v ∉ S ∪ S'}, Mv v.1)) atTop (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    have := (tendsto_const_nhds (x := ∏' v : {v // v ∉ S}, Mv v.1)).mul
      ((hT.mul hP).div hM one_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, mul_one, div_one] using this
  have hA : Tendsto (fun S' : Finset ι => (∏ v ∈ (S ∪ S') \ S, Mv v) *
      ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) atTop
      (𝓝 (∏' v : {v // v ∉ S}, Mv v.1)) := by
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ne one_ne_zero] with S' hS'
    dsimp only [Function.comp] at hS' ⊢
    rw [GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut ι Mv S (S ∪ S') hMs Finset.subset_union_left,
      mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hS']
  exact iSup_eq_of_tendsto (fun a b h => ENNReal.ofReal_le_ofReal (hmono h))
    ((ENNReal.continuous_ofReal.tendsto _).comp hA)

end GlobalTheory.CompanionTheory.TailProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPrincipalElementNormBound
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink

theorem exists_ne_zero_mem_absNorm_le :
    ∀ (E : Type) [Field E] [NumberField E], ∃ C : ℝ, 0 < C ∧ ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ →
      ∃ t ∈ 𝔞, t ≠ 0 ∧ (Ideal.absNorm (Ideal.span {t}) : ℝ) ≤ C * Ideal.absNorm 𝔞 := by
  intro E _ _
  refine ⟨(4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E *
      ((Module.finrank ℚ E).factorial : ℝ) / (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E *
      Real.sqrt |(discr E : ℝ)|, ?_, ?_⟩
  · have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
    have h1 : (0 : ℝ) < (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces E :=
      pow_pos (div_pos (by norm_num) Real.pi_pos) _
    have h2 : (0 : ℝ) < ((Module.finrank ℚ E).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h3 : (0 : ℝ) < (Module.finrank ℚ E : ℝ) ^ Module.finrank ℚ E :=
      pow_pos (Nat.cast_pos.mpr hn) _
    exact mul_pos (div_pos (mul_pos h1 h2) h3) (Real.sqrt_pos.mpr hd)
  · intro 𝔞 h𝔞
    have hmem : (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    obtain ⟨a, ha, ha0, hle⟩ :=
      exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr E (Units.mk0 _ hmem)
    rw [Units.val_mk0] at ha
    obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    refine ⟨t, ht, ?_, ?_⟩
    · rintro rfl
      simp at ha0
    · have key : ((Ideal.absNorm (Ideal.span {t}) : ℚ)) =
          |Algebra.norm ℚ (algebraMap (𝓞 E) E t)| := by
        rw [← FractionalIdeal.coeIdeal_absNorm (K := E), FractionalIdeal.coeIdeal_span_singleton,
          FractionalIdeal.absNorm_span_singleton]
      have key' : (Ideal.absNorm (Ideal.span {t}) : ℝ) =
          ((|Algebra.norm ℚ (algebraMap (𝓞 E) E t)| : ℚ) : ℝ) := by
        rw [← key, Rat.cast_natCast]
      rw [key']
      refine hle.trans (le_of_eq ?_)
      simp only [Units.val_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
      ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Mink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LamIsLattice
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem isLat_lam_of_matrix (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K) : IsLat (lam c) := by
  have hL : IsLat (intVec K m) := isLat_intVec m
  refine ⟨Submodule.FG.sup hL.1 (Submodule.FG.map _ hL.1), ?_⟩
  rw [eq_top_iff, ← hL.2]
  exact Submodule.span_mono (fun v hv => (le_sup_left : intVec K m ≤ lam c) hv)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

