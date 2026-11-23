module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Formalism.LocalRingCardinality.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Formalism.LocalToGlobal.Columns.BaseLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.AdmissibleDegree

open Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

theorem admissibleDegree_count_at_parameter_const {D : D7} (L : SizeData₂ D) (h : SizesAt L) (P : ParameterChoice' D L) (hK : KapDef D) (hx : 2 ≤ L.sc.x) :
    Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound D L 40 := by
  intro u j hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  have hf := GlobalTheory.FockDegreeFine.degree_fine L h P hK hx u j hj
  have w0 : ∀ τ, 0 ≤ wj D j τ := fun τ => (GlobalTheory.HCEntries.wj_bounds h hx j j1 j2 τ).1
  have s0 : 0 ≤ sizeOffTops D j := by
    unfold sizeOffTops; exact Finset.sum_nonneg fun τ _ => w0 τ
  have s1 : sizeOffTops D j ≤ ∑ τ : D.what₂.Tau, wj D j τ := by
    unfold sizeOffTops
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun τ _ _ => w0 τ
  have hc := GlobalTheory.LossItemsCompare.cube_le_eta P
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have ht : (1 : ℝ) ≤ D.R.t := GlobalTheory.HCEntries.one_le_letterBlockLength D
  have hk : (1 : ℝ) ≤ D.R.k := GlobalTheory.HCEntries.one_le_k D
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hNm : Nm D = (D.R.N D.R.m : ℝ) := rfl
  have hN2 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
    have a1 : (D.R.N D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 := by
      rcases le_total (D.R.N D.R.m : ℝ) 1 with hN1 | hN1
      · nlinarith [pow_nonneg hN0 3]
      · nlinarith [pow_nonneg hN0 2]
    have a2 : L.etaSz ≤ (D.R.m : ℝ) * D.R.t * L.etaSz := by
      have : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := by nlinarith
      nlinarith
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hc0 : 0 ≤ (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (GlobalTheory.HCEntries.b'_pos L).le) (by linarith)
  have hkN : 0 ≤ (D.R.k : ℝ) * Nm D := by rw [hNm]; positivity
  have hdeg : degErr L ≤ 2 * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D) +
      (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x) := by
    unfold degErr
    have : (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + Nm D ^ 2 + (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) ≤
        2 * ((D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * Nm D)) := by
      rw [hNm] at hkN ⊢
      have hkS : 0 ≤ (D.R.k : ℝ) * L.Sc := by positivity
      have := mul_le_mul_of_nonneg_left (show (D.R.k : ℝ) * L.Sc + (D.R.N D.R.m : ℝ) ^ 2 + (D.R.m : ℝ) * D.R.t * L.etaSz ≤
        2 * ((D.R.k : ℝ) * L.Sc + (D.R.m : ℝ) * D.R.t * L.etaSz + (D.R.k : ℝ) * (D.R.N D.R.m : ℝ)) by linarith) hf0
      linarith
    linarith
  unfold Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound Formalism.MainNotions.WeightDegreeSizes.errG Formalism.MainNotions.WeightDegreeSizes.sumA at *
  change |degPi D u j - (fockDeg D j : ℝ) - topSum L| ≤ _
  rw [abs_le] at hf ⊢
  constructor <;> nlinarith [hf.1, hf.2]

theorem admissibleDegreeCount_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x →
    ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _
  refine ⟨40, 2, by norm_num, fun x hx2 hx i => ?_⟩
  have y := hx2
  rw [← Fm.L_x x i hx] at y
  exact admissibleDegree_count_at_parameter_const (Fm.L x i) (Fm.sizes x hx i) (Fm.params x hx i) (Fm.ex x hx i).kap_def y

end GlobalTheory.AdmissibleDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.SmallStepSurj

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem surj_of_smallExt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  intro R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w
  have hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)
  by_cases htm : t ∈ IsLocalRing.maximalIdeal R
  ·
    let R₀ := R ⧸ IsLocalRing.maximalIdeal R
    let σ₀ : R →+* R₀ := Ideal.Quotient.mk _
    have hR₀ : IsField R₀ :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)
    have hse : SmallExt t σ' σ₀ := by
      refine ⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · exact hm a
      · intro hat
        by_contra hna
        have hu : IsUnit a := by
          by_contra hnu
          exact hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)
        exact ht (hu.mul_right_eq_zero.1 hat)

    have hP' := IsPullback.of_hasPullback A.hom (spMap σ')
    have hP₀ := IsPullback.of_hasPullback A.hom (spMap σ₀)
    obtain ⟨i', hg', hab', hsm'⟩ := _root_.GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback R R' σ' A _ _ _ hP'
    obtain ⟨i₀, hg₀, hab₀, hsm₀⟩ := _root_.GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback R R₀ σ₀ A _ _ _ hP₀
    have hstep := _root_.GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg
      (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1

    have hle : RingHom.ker σ' ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]; exact htm
    let τ : R' →+* k := RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩
    have hτ : ∀ r, τ (σ' r) = σ r := fun r =>
      RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r
    have hτs : Function.Surjective τ := fun y => by
      obtain ⟨x, rfl⟩ := hσ y; exact ⟨σ' x, hτ x⟩
    have hcomp : spMap σ = spMap τ ≫ spMap σ' := by
      rw [← spMap_comp_hom]; congr 1; ext r; exact (hτ r).symm
    let ψ' : X₀ ⟶ pullback A.hom (spMap σ') := hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])
    have hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ := hP'.lift_fst _ _ _
    have w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ) := by
      refine IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'
      rw [hψ', ← hcomp]; exact w
    have hsurj := (hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'
    intro y
    obtain ⟨x', rfl⟩ := hsurj y
    obtain ⟨a, rfl⟩ := hstep x'
    refine ⟨a, ?_⟩
    exact ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ'))
      σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm
  ·
    have hu : IsUnit t := by
      by_contra hnu
      exact htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)
    have hinj : Function.Injective σ := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      have hma : a ∈ IsLocalRing.maximalIdeal R := by rw [← hkerσ]; exact ha
      exact (hu.mul_left_eq_zero).1 (hm a hma)
    exact _root_.GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩

end GlobalTheory.AbCoh.SmallStepSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuousStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_GL_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → Continuous φ.1 := by
  first | exact @GlobalTheory.CuspRep.IsAutForm.continuous | exact GlobalTheory.CuspRep.IsAutForm.continuous | (intros; apply GlobalTheory.CuspRep.IsAutForm.continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BuRatOfCoordinates
section
open Formalism.BasicNotions Formalism.MainNotions Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem buRat_of_coordinates : ∀ (D : D7) (μ : D.what₂.Tup), μ = D.what₂.mu0 → ∀ {n nV d : ℕ} (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (a : D.what₂.Word → ℕ) (eNu : ∀ u, (Fin (a u) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Formalism.BasicNotions.Rows.BuDefQ D.what₂ → (∀ x y, ⟪jA x, jA y⟫_ℂ ∈ Set.range D.what₂.embLL) → D.what₂.V0 μ = Submodule.span ℂ (Set.range fun F0 => jA (V.mulVec F0)) → (∀ F0, D.what₂.iota μ (jA (V.mulVec F0)) = D.jEE (eRR (Pq.mulVec F0))) → Function.Surjective Pq.mulVec → (∀ u x F0, D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec F0)) ∈ Set.range D.what₂.embLL) → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro D μ hμ n nV d jA V Pq eRR a eNu hB hinner hV hι hPq hper
  subst hμ
  intro u φ x
  obtain ⟨x', rfl⟩ := (eNu u).surjective φ
  obtain ⟨y, rfl⟩ := eRR.surjective x
  obtain ⟨G, rfl⟩ := hPq y
  have key := span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hset : {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0} = ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL)) := by
    ext z
    simp
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL))) := by
    rw [← hset, ← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  obtain ⟨G', hG', hperp⟩ := _root_.GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range D.what₂.LL D.what₂.embLL (D.what₂.Amb D.what₂.mu0) nV (jA.comp V.mulVecLin)
    (fun x y => hinner _ _) (LinearMap.ker Pq.mulVecLin) G
  have hG'0 : Pq.mulVec G' = 0 := hG'
  set q : D.what₂.Amb D.what₂.mu0 := jA (V.mulVec (G - G')) with hq
  have hqeq : q = (jA.comp V.mulVecLin) G - (jA.comp V.mulVecLin) G' := by
    rw [hq, ← map_sub]
    rfl
  have hqV : q ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G - G', rfl⟩
  have hqU : q ∈ (D.what₂.Usp D.what₂.mu0)ᗮ := by
    rw [hU, hqeq]
    exact hperp
  have hqQ : q ∈ D.what₂.Qsp D.what₂.mu0 := ⟨hqV, hqU⟩
  have hιq : D.what₂.iota D.what₂.mu0 q = D.jEE (eRR (Pq.mulVec G)) := by
    rw [hq, hι, Matrix.mulVec_sub, hG'0, sub_zero]
  obtain ⟨z, hz⟩ := hper u x' (G - G')
  refine ⟨z, ?_⟩
  rw [hB u, ← hιq, D.what₂.sec_iota _ q hqQ, hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem card_sq_mod_prime : ∀ (p : ℕ), p.Prime → p % 4 = 3 →
    2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  intro p hp h4
  obtain ⟨e, -⟩ := _root_.GlobalTheory.sq_sum_equiv_Ico p hp h4
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum] at hc
  have h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1 := by
    simp
  rw [h2] at hc
  have hp2 := hp.two_le
  have hsum : 2 * Fintype.card (Sq p) + 1 = p := by omega
  refine ⟨hsum, ?_⟩
  rw [Nat.odd_iff]
  omega

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetraction
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CechPic

theorem squareZero_localUnit_difference_ring_identity {R : Type*} [CommRing R] {Tj Tk Nj Nk H G G' Sj Sk Pj Pk Pj' Pk' M : R}
    (hT : Tj = G' * Tk) (hS : Sj = G * G * Sk) (hP : Pj = G' * G' * Pk) (hj' : Pj * Pj' = 1)
    (hk' : Pk * Pk' = 1) (hNj : Nj = Sj * Pj' - 1) (hNk : Nk = Sk * Pk' - 1) (hNj2 : Nj * Nj = 0)
    (hNk2 : Nk * Nk = 0) (hH : 2 * H = 1)
    (hM : M = Tj * (1 + Nj * H) - G * (Tk * (1 + Nk * H))) (hM2 : M * M = 0) :
    M * (G * (Tk * (1 + Nk * H))) = 0 := by
  have e1 : (Tj * (1 + Nj * H)) ^ 2 = Tj ^ 2 * Sj * Pj' := by
    linear_combination Tj ^ 2 * Nj * hH + Tj ^ 2 * H ^ 2 * hNj2 + Tj ^ 2 * hNj
  have e2 : (G * (Tk * (1 + Nk * H))) ^ 2 = G ^ 2 * Tk ^ 2 * Sk * Pk' := by
    linear_combination G ^ 2 * Tk ^ 2 * Nk * hH + G ^ 2 * Tk ^ 2 * H ^ 2 * hNk2 + G ^ 2 * Tk ^ 2 * hNk
  have e4 : Pj' * (G' * G') = Pk' := by
    linear_combination (-(Pj' * (G' * G'))) * hk' + Pk' * hj' - Pk' * Pj' * hP
  have e5 : (Tj * (1 + Nj * H)) ^ 2 = (G * (Tk * (1 + Nk * H))) ^ 2 := by
    rw [e1, e2, hT, hS]
    linear_combination G ^ 2 * Tk ^ 2 * Sk * e4
  linear_combination H * e5 - H * hM2 +
    H * (Tj * (1 + Nj * H) + G * (Tk * (1 + Nk * H)) + M) * hM - M * (G * (Tk * (1 + Nk * H))) * hH

end GlobalTheory.CechPic


open GlobalTheory.SmallExtLift in
theorem GlobalTheory.CechPic.eq_zero_of_sqZero_retract : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  intro X X' i q e hiq h2 hsq c hc hc2
  obtain ⟨Q, hQ, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  rw [two_nsmul, ← GlobalTheory.CechPic.cls_tens hQ hQ (GlobalTheory.CechPic.isLB_tens hQ hQ),
    GlobalTheory.CechPic.cls_eq_zero_iff] at hc2
  obtain ⟨s, hs⟩ := hc2
  rw [← GlobalTheory.CechPic.cls_pull hQ i (pull_isLB hQ i), GlobalTheory.CechPic.cls_eq_zero_iff] at hc
  obtain ⟨t₀, ht₀⟩ := hc
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hQ).2 ?_

  have genLaw : ∀ {M : LB X'} (t : LB.Gen M), t.IsGen → ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z)
      (a b : M.ι) (ha : f z ∈ M.U a) (hb : f z ∈ M.U b),
      gr f z _ ha (t.s a).val = gr f z (M.U a ⊓ M.U b) ⟨ha, hb⟩ (M.g a b).val * gr f z _ hb (t.s b).val := by
    intro M t ht Z f z a b ha hb
    have hm : f z ∈ M.U a ⊓ M.U b := ⟨ha, hb⟩
    have := congrArg (fun u => gr f z _ hm u.val) (ht a b)
    simp only [Units.val_mul, map_mul] at this
    exact (gr_res f z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) rfl (gr_res f z _ hm _)))
  let W : Q.ι → X.Opens := fun j => (Q.pull i).U (fun _ => j)
  have hσ : ∀ j, Q.U j ≤ (q ≫ i) ⁻¹ᵁ Q.U j := fun j x hx => by
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hiq]; exact hx
  have hW : ∀ j, Q.U j ≤ q ⁻¹ᵁ W j := fun j x hx => pull_le Q i j le_rfl (hσ j hx)
  have hσf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → ((f ≫ q) ≫ i) z ∈ Q.U j := by
    intro j Z f z hz
    simp only [Scheme.Hom.comp_apply, hiq]; exact hz
  have hWf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → (f ≫ q) z ∈ W j :=
    fun j Z f z hz => hW j hz
  let sj : ∀ j, Γ(X', Q.U j)ˣ := fun j => res (le_inf le_rfl le_rfl) (s.s (j, j))
  let u : ∀ j, Γ(X', Q.U j) := fun j => (q.appLE (W j) (Q.U j) (hW j)).hom (t₀.s fun _ => j).val
  let σi : ∀ j, Γ(X', Q.U j) := fun j => ((q ≫ i).appLE (Q.U j) (Q.U j) (hσ j)).hom (sj j)⁻¹.val
  let n : ∀ j, Γ(X', Q.U j) := fun j => (sj j).val * σi j - 1
  let hh : ∀ j, Γ(X', Q.U j) := fun j => (X'.presheaf.map (homOfLE le_top).op).hom h2.unit⁻¹.val
  let t : ∀ j, Γ(X', Q.U j) := fun j => u j * (1 + n j * hh j)
  have gn : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (n j) = gr f z _ hz (sj j).val * gr ((f ≫ q) ≫ i) z (Q.U j) (hσf j f z hz) (sj j)⁻¹.val - 1 := by
    intro Z f z j hz
    simp only [n, σi, map_sub, map_mul, map_one]
    rw [gr_appLE]
    exact congrArg (fun w => _ * w - 1) (gr_congr (Category.assoc f q i).symm z _ _ _)
  have gt : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (t j) = gr (f ≫ q) z (W j) (hWf j f z hz) (t₀.s fun _ => j).val *
        (1 + gr f z _ hz (n j) * gr f z ⊤ trivial h2.unit⁻¹.val) := by
    intro Z f z j hz
    simp only [t, u, hh, map_mul, map_add (f := _), map_one]
    rw [gr_appLE, gr_res]
  have E1 : (𝟙 X ≫ i) ≫ q = 𝟙 X := by rw [Category.assoc, e, Category.id_comp]
  have E2 : ((𝟙 X ≫ i) ≫ q) ≫ i = 𝟙 X ≫ i := by rw [E1]
  have hn0 : ∀ j, (i.app (Q.U j)).hom (n j) = 0 := fun j => gr_ext fun y hy => by
    rw [gr_app, map_zero, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv,
      map_one, sub_self]
  have hn2 : ∀ j, n j * n j = 0 := fun j => hsq _ _ _ (hn0 j) (hn0 j)
  have gti : ∀ j y (hy : (𝟙 X ≫ i) y ∈ Q.U j),
      gr (𝟙 X ≫ i) y _ hy (t j) = gr ((𝟙 X ≫ i) ≫ q) y (W j) (hWf j _ y hy) (t₀.s fun _ => j).val := by
    intro j y hy
    rw [gt (𝟙 X ≫ i) y j hy, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv, map_one, sub_self, zero_mul,
      add_zero, mul_one]
  let m : ∀ j k, Γ(X', Q.U j ⊓ Q.U k) := fun j k =>
    (X'.presheaf.map (homOfLE inf_le_left).op).hom (t j) -
      (Q.g j k).val * (X'.presheaf.map (homOfLE inf_le_right).op).hom (t k)
  have gm' : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j k (hz : f z ∈ Q.U j ⊓ Q.U k),
      gr f z _ hz (m j k) = gr f z _ hz.1 (t j) - gr f z _ hz (Q.g j k).val * gr f z _ hz.2 (t k) := by
    intro Z f z j k hz
    simp only [m, map_sub, map_mul]
    rw [gr_res, gr_res]
  have hm0 : ∀ j k, (i.app _).hom (m j k) = 0 := fun j k => gr_ext fun y hy => by
    rw [gr_app, map_zero, gm' (𝟙 X ≫ i) y j k hy, gti j y hy.1, gti k y hy.2, sub_eq_zero]
    have := gr_gen ht₀ ((𝟙 X ≫ i) ≫ q) y (hσf j _ y hy.1) (hσf k _ y hy.2)
    exact this.trans (congrArg (· * _) (gr_congr E2 y _ _ _))
  have gS : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) a b (ha : f z ∈ Q.U a) (hb : f z ∈ Q.U b),
      gr f z _ ha (sj a).val = gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val *
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z _ hb (sj b).val := by
    intro Z f z a b ha hb
    have hS := genLaw s hs f z (a, a) (b, b) ⟨ha, ha⟩ ⟨hb, hb⟩
    have hm : f z ∈ (Q.U a ⊓ Q.U a) ⊓ (Q.U b ⊓ Q.U b) := ⟨⟨ha, ha⟩, ⟨hb, hb⟩⟩
    have hg : gr f z _ hm ((GlobalTheory.CechPic.tens Q Q).g (a, a) (b, b)).val =
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val := by
      show gr f z _ hm (res _ (Q.g a b) * res _ (Q.g a b)).val = _
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)
    refine (gr_res f z (le_inf le_rfl le_rfl : Q.U a ≤ Q.U a ⊓ Q.U a) ha (s.s (a, a)).val).trans (hS.trans ?_)
    exact congrArg₂ (· * ·) hg (gr_res f z (le_inf le_rfl le_rfl : Q.U b ≤ Q.U b ⊓ Q.U b) hb (s.s (b, b)).val).symm
  refine gen_of_refine hQ Q.U hQ.cover id (fun _ => le_rfl) t
    (fun j => ((Units.isUnit _).map _).mul (isUnit_one_add (hn2 j) _)) fun a b x ha hb => ?_
  have hab : (𝟙 X') x ∈ Q.U a ⊓ Q.U b := ⟨ha, hb⟩
  have hmx := gm' (𝟙 X') x a b hab
  have hm := hmx
  rw [gt (𝟙 X') x a ha, gt (𝟙 X') x b hb] at hm
  have hmm := congrArg (gr (𝟙 X') x _ hab) (hsq _ _ _ (hm0 a b) (hm0 a b))
  rw [map_mul, map_zero] at hmm
  have hT := gr_gen ht₀ (𝟙 X' ≫ q) x (hσf a _ x ha) (hσf b _ x hb)
  have hSx := gS (𝟙 X') x a b ha hb
  have hPx := gS ((𝟙 X' ≫ q) ≫ i) x a b (hσf a _ x ha) (hσf b _ x hb)
  have hj' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hk' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hNa := gn (𝟙 X') x a ha
  have hNb := gn (𝟙 X') x b hb
  have hNa2 := congrArg (gr (𝟙 X') x _ ha) (hn2 a)
  have hNb2 := congrArg (gr (𝟙 X') x _ hb) (hn2 b)
  rw [map_mul, map_zero] at hNa2 hNb2
  have hH : 2 * gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val = 1 := by
    have := congrArg (gr (𝟙 X') x ⊤ trivial) h2.val_inv_mul
    rw [map_mul, map_one, map_ofNat] at this
    linear_combination this
  have key := GlobalTheory.CechPic.squareZero_localUnit_difference_ring_identity hT hSx hPx hj' hk' hNa hNb hNa2 hNb2 hH hm hmm
  have hB := ((Units.isUnit (Q.g a b)).map (gr (𝟙 X') x (Q.U a ⊓ Q.U b) hab)).mul
    (((Units.isUnit (t₀.s fun _ => b)).map (gr (𝟙 X' ≫ q) x (W b) (hWf b _ x hb))).mul (isUnit_one_add hNb2 (gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val)))
  have h0 := hB.mul_left_eq_zero.1 key
  rw [hmx] at h0
  exact sub_eq_zero.1 h0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantNinth
section
namespace GlobalTheory.ColNorms.StepRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem nuW_eq_nu (N : NumDatum) {X : Fields} {Pr : Primes X} (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word)
    (δ : Code N) (h : WeightTie N W pl u δ) {i : ℕ} (hi : i < N.R.m) (z : RPl N.R) (l : Fin (N.R.N i)) :
    (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  obtain ⟨h1, h2⟩ := h.2.2 z
  have he : (W.hc u (pl z)).e = (N.hc z).e := congrArg RowPar.e h1
  have hq : N.eQ (i + 1) z = (N.hc z).e ⟨i, hi⟩ := by
    unfold NumDatum.eQ
    rw [dite_eq_left ⟨by omega, by omega⟩]
    rfl
  rw [W.nuW_eq u hi, W.lamN_eq u hi.le, he]
  unfold NumDatum.nu NumDatum.srcPar
  rw [hq]
  by_cases hl : l.1 < N.R.k
  · rw [dite_eq_left hl, dite_eq_left hl]
    unfold hcToWeightQ rhoVec wG Ranks.N
    rw [h2, Nat.add_sub_cancel]
    push_cast
    ring
  · have hb := N.R.blk_lt hi.le l hl
    rw [dite_eq_right hl, dite_eq_right hl, dite_eq_left hb]
    have hdm := Nat.div_add_mod (l.1 - N.R.k) (N.R.t + 1)
    have hl2 : l.1 = N.R.k + ((N.R.t + 1) * ((l.1 - N.R.k) / (N.R.t + 1)) + (l.1 - N.R.k) % (N.R.t + 1)) := by omega
    have hl3 : ((l.1 : ℕ) : ℚ) = N.R.k + (((N.R.t : ℚ) + 1) * (((l.1 - N.R.k) / (N.R.t + 1) : ℕ) : ℚ) +
        (((l.1 - N.R.k) % (N.R.t + 1) : ℕ) : ℚ)) := by exact_mod_cast hl2
    rw [hl3]
    generalize (N.hc z).e ⟨(l.1 - N.R.k) / (N.R.t + 1), hb⟩ = eb
    generalize (l.1 - N.R.k) / (N.R.t + 1) = B
    generalize (l.1 - N.R.k) % (N.R.t + 1) = r
    unfold wG Ranks.N
    rw [Nat.add_sub_cancel]
    push_cast
    ring

theorem sExp_int (R : Ranks) (z : ℤ) (j : ℕ) :
    (∃ y : ℤ, sExp R (z : ℚ) (j + 1) = y) ∧ ∃ y : ℤ, sExp' R (z : ℚ) (j + 1) = y := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold sExp sExp' Ranks.N
  rw [Nat.add_sub_cancel, ha, hc]
  exact ⟨⟨z - a - j * (c + 1), by push_cast; ring⟩, ⟨z - a - (j + 1) * (c + 1), by push_cast; ring⟩⟩

theorem stepWeights {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau)
    (h0 : ∀ l : Fin (R.N i), 0 ≤ (W.nuW u (i + 1) τ).w l) :
    GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ) := by
  obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨i, hi⟩
  obtain ⟨⟨y, hy⟩, ⟨y', hy'⟩⟩ := sExp_int R z i
  refine ⟨h0, ⟨y', fun l => ?_⟩, ⟨y, fun l => ?_⟩⟩
  · have h := W.nuW_eq_true u hi τ l
    rw [hz, hy'] at h
    exact_mod_cast h
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero
    by_cases hl : l.1 < R.N i
    · rw [dite_eq_left hl]
      have h := W.nuW_eq_true u hi τ ⟨l.1, hl⟩
      have h' := W.lamTrue_old u hi τ l hl
      rw [hz, hy'] at h
      rw [hz, hy, hy', ← h] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = (((W.nuW u (i + 1) τ).w ⟨l.1, hl⟩ : ℤ) : ℚ) := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2
    · rw [dite_eq_right hl]
      have h' := W.lamTrue_new u hi τ l hl
      rw [hz, hy] at h'
      have h2 : (((W.lamTrue u (i + 1) τ).w l + y : ℤ) : ℚ) = 0 := by
        push_cast
        rw [h']
        ring
      exact_mod_cast h2

end GlobalTheory.ColNorms.StepRows
end

