module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

noncomputable section

namespace GlobalTheory.Poinc.SumSq

theorem exists_nat_smul_sub_posDef {ι : Type*} [Fintype ι] {G B : Matrix ι ι ℝ} (hG : G.PosDef)
    (hB : B.IsHermitian) : ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hne : ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  have hc : ContinuousOn (fun x : ι → ℝ => (x ⬝ᵥ B *ᵥ x) / (x ⬝ᵥ G *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
      fun x hx => (hp x (hne x hx)).ne'
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  obtain ⟨κ₀, hκ₀⟩ := exists_nat_gt C
  refine ⟨κ₀, fun κ hκ => ?_⟩
  have hκ' : C < κ := hκ₀.trans_le (by exact_mod_cast hκ)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.sub ?_ hB
    rw [IsHermitian, conjTranspose_smul, hG.isHermitian.eq, star_trivial]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := hC ⟨_, hs, rfl⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    rw [mul_div_mul_left _ _ (inv_pos.2 hn).ne', mul_div_mul_left _ _ (inv_pos.2 hn).ne',
      div_le_iff₀ (hp x hx)] at h1
    have h2 := mul_lt_mul_of_pos_right hκ' (hp x hx)
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith

theorem posDef_symm {n : Type*} {M : Matrix n n ℝ} (hM : M.PosDef) (i j : n) : M j i = M i j := by
  have := congrFun₂ hM.isHermitian.eq i j
  simpa using this

theorem schur_posDef {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hM : M.PosDef) :
    (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ).PosDef := by
  have hs := posDef_symm hM
  have ha : 0 < M 0 0 := hM.diag_pos
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp [hs]
    ring
  · set B := ∑ j, M 0 j.succ * y j with hB
    set x : Fin (n + 1) → ℝ := Fin.cons (-B / M 0 0) y with hx
    have hx0 : x ≠ 0 := by
      intro h
      apply hy
      funext j
      have := congrFun h j.succ
      simpa [hx] using this
    have h1 := hM.dotProduct_mulVec_pos hx0
    rw [star_trivial] at h1 ⊢
    have e1 : x ⬝ᵥ M *ᵥ x = M 0 0 * (-B / M 0 0) ^ 2 + 2 * (-B / M 0 0) * B +
        ∑ i, y i * ∑ j, M i.succ j.succ * y j := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      have h3 : ∑ i, y i * (M 0 i.succ * (-B / M 0 0)) = (-B / M 0 0) * B := by
        rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [dotProduct, mulVec, Fin.sum_univ_succ, hx, Fin.cons_zero, Fin.cons_succ, hc,
        mul_add, Finset.sum_add_distrib, h3]
      rw [← hB]
      ring
    have e2 : y ⬝ᵥ (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ) *ᵥ y =
        M 0 0 * ∑ i, y i * ∑ j, M i.succ j.succ * y j - B ^ 2 := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      simp only [dotProduct, mulVec, of_apply, hc, sub_mul, Finset.sum_sub_distrib, mul_sub]
      rw [hB, sq, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    rw [e1] at h1
    field_simp at h1
    nlinarith

theorem exists_smul_eq_sum_vecMulVec : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ),
    (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (ι : Type) (_ : Fintype ι) (D : ℕ) (a : ι → Fin r → ℤ),
      1 ≤ D ∧ (D : ℤ) • L = ∑ i, vecMulVec (a i) (a i) := by
  intro r
  induction r with
  | zero =>
    intro L _
    refine ⟨Empty, inferInstance, 1, Empty.elim, le_rfl, ?_⟩
    ext i
    exact i.elim0
  | succ n ih =>
    intro L hL
    have hs := posDef_symm hL
    have hsz : ∀ i j, L j i = L i j := fun i j => by
      have := hs i j
      simp only [Matrix.map_apply] at this
      exact_mod_cast this
    have ha : (0 : ℝ) < (L 0 0 : ℝ) := by simpa using (hL.diag_pos (i := 0))
    have ha' : 0 < L 0 0 := by exact_mod_cast ha
    set S : Matrix (Fin n) (Fin n) ℤ :=
      Matrix.of fun i j => L 0 0 * L i.succ j.succ - L i.succ 0 * L 0 j.succ with hS
    have hSr : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
      have := schur_posDef hL
      convert this using 1
      ext i j
      simp [hS]
    obtain ⟨ι, _, D, y, hD, hy⟩ := ih S hSr
    refine ⟨Fin D ⊕ ι, inferInstance, D * (L 0 0).toNat,
      Sum.elim (fun _ => fun j => L 0 j) (fun i => Fin.cons 0 (y i)), ?_, ?_⟩
    · have : 1 ≤ (L 0 0).toNat := by omega
      nlinarith
    · have hy' : ∀ p q, (D : ℤ) * (L 0 0 * L p.succ q.succ - L p.succ 0 * L 0 q.succ) =
          ∑ i, y i p * y i q := fun p q => by
        have := congrFun₂ hy p q
        simpa [hS, Matrix.sum_apply, vecMulVec_apply] using this
      have hc : ((L 0 0).toNat : ℤ) = L 0 0 := Int.toNat_of_nonneg ha'.le
      ext p q
      simp only [Matrix.smul_apply, Matrix.sum_apply, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, vecMulVec_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, nsmul_eq_mul]
      push_cast
      rw [hc]
      refine Fin.cases ?_ (fun p => ?_) p <;> refine Fin.cases ?_ (fun q => ?_) q
      · simp
        ring
      · simp
        ring
      · simp [hsz 0 p.succ]
        ring
      · simp only [Fin.cons_succ]
        rw [← hy' p q, hsz 0 p.succ]
        ring

theorem exists_smul_eq_sum_vecMulVec_span :
    ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef →
      ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧
        (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  intro r L hL
  obtain ⟨κ₀, hκ⟩ := exists_nat_smul_sub_posDef hL (isHermitian_one (α := ℝ) (n := Fin r))
  set d := max κ₀ 1 with hdd
  have hd1 : 1 ≤ d := le_max_right _ _
  have hd := hκ d (le_max_left _ _)
  set M : Matrix (Fin r) (Fin r) ℤ := (d : ℤ) • L - 1 with hMdef
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    convert hd using 1
    ext i j
    simp only [hMdef, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  obtain ⟨ι, _, D, a, hD, ha⟩ := exists_smul_eq_sum_vecMulVec r M hM
  let b : (Fin r × Fin D) ⊕ ι → Fin r → ℤ := Sum.elim (fun p => Pi.single p.1 1) a
  have hsum : ((D * d : ℕ) : ℤ) • L = ∑ k, vecMulVec (b k) (b k) := by
    rw [Fintype.sum_sum_type]
    simp only [b, Sum.elim_inl, Sum.elim_inr]
    rw [← ha]
    ext i j
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [hMdef, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
      vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
    simp only [nsmul_eq_mul]
    push_cast
    have hδ : ∑ c : Fin r, (Pi.single c (1 : ℤ) : Fin r → ℤ) i * (Pi.single c (1 : ℤ) : Fin r → ℤ) j =
        if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h
        simp [Pi.single_apply]
      · simp [Pi.single_apply, h]
    rw [← Finset.mul_sum, hδ]
    split_ifs <;> ring
  have hspan : Submodule.span ℤ (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inl (j, ⟨0, hD⟩), by simp [b]⟩
  let e := Fintype.equivFin ((Fin r × Fin D) ⊕ ι)
  refine ⟨D * d, Fintype.card ((Fin r × Fin D) ⊕ ι), b ∘ e.symm, ?_, ?_, ?_⟩
  · nlinarith
  · rw [e.symm.surjective.range_comp]
    exact hspan
  · rw [hsum]
    exact (e.symm.sum_comp (fun k => vecMulVec (b k) (b k))).symm

end GlobalTheory.Poinc.SumSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem square_hom_ext (A : Over S) {Z : Scheme.{0}} {f g : Z ⟶ (A ⊗ A).left}
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem eSec_fst (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  show (η[A ⊗ A] ≫ fst A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_snd (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  show (η[A ⊗ A] ≫ snd A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_lift_one (A : Over S) [GrpObj A] : eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

theorem exists_bundle_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  intro X Y π Ga _ ρ A _ A₀ _ φ ν P hπ hA hA₀ gp hν hνρ ν₁ νm hP ⟨t₀, ht₀⟩ hsq
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hA₂ : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  choose ν₂ hν₂ iν₂ using hsq
  have ν₂m : ∀ a c, ν₂ (a * c) = ν₂ a ≫ ν₂ c := fun a c => square_hom_ext A
    (by rw [(hν₂ _).1, Category.assoc, (hν₂ c).1, reassoc_of% (hν₂ a).1, νm])
    (by rw [(hν₂ _).2, Category.assoc, (hν₂ c).2, reassoc_of% (hν₂ a).2, νm])
  have wA : (fst A A).left ≫ A.hom = (snd A A).left ≫ A.hom := (Over.w (fst A A)).trans (Over.w (snd A A)).symm
  let φ₂ : (G2 A).left ⟶ (G2 A₀).left := pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, gp.1.w, reassoc_of% wA])
  have hsqφ : IsSquare φ φ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsqφ
  have hu : ∀ a, ν₂ a ≫ (G2 A).hom = (G2 A).hom ≫ ρ a := fun a => by
    rw [← Over.w (fst A A), reassoc_of% (hν₂ a).1, (hνρ a).1.w, Category.assoc]
  have hinv : ∀ a, ν₂ a ≫ φ₂ = φ₂ := fun a => square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% (hν₂ a).1, hν.inv a])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% (hν₂ a).2, hν.inv a])
  have hφ₂ : IsGaloisCover Ga ν₂ φ₂ := ((galoisCover_descent X Y π Ga ρ hπ).2.2 (G2 A).left (G2 A₀).left φ₂ ν₂
    (G2 A).hom (G2 A₀).hom hu hpb.w.symm).2 hpb.flip hinv
  have he : eSec (G2 A) ≫ (G2 A).hom = 𝟙 X := Over.w η[G2 A]
  have hτ : ∀ a, eSec (G2 A) ≫ ν₂ a = ρ a ≫ eSec (G2 A) := fun a => square_hom_ext A
    (by rw [Category.assoc, (hν₂ a).1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_fst])
    (by rw [Category.assoc, (hν₂ a).2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_snd])
  have hc0 : cls _ (pull_isLB hP (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 := (cls_eq_zero_iff _).2 ⟨t₀, ht₀⟩
  have hPe : pull (eSec (G2 A)) (cls P hP) = 0 := by
    rw [← eSec_lift_one, pull_comp, ← cls_pull hP _ (pull_isLB hP _), hc0, map_zero]
  obtain ⟨r, hr⟩ := (cls_eq_zero_iff (pull_isLB hP (eSec (G2 A)))).1 hPe
  obtain ⟨u, hu₁, hu₂⟩ := GlobalTheory.TripleDescent.exists_linearisation hP (G2 A).hom (eSec (G2 A)) he (hG _ _ hA₂).2 ρ ν₂
    hπ.mul ν₂m hτ r hr iν₂
  obtain ⟨M, hM, iM⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ₂ Ga ν₂ P hφ₂ hP u hu₁ hu₂
  have hMP : pull φ₂ (cls M hM) = cls P hP := ((cls_eq_iff hP (pull_isLB hM φ₂)).2 iM).symm
  have he₀ : eSec (G2 A₀) ≫ (G2 A₀).hom = 𝟙 Y := Over.w η[G2 A₀]
  have hφe : eSec (G2 A) ≫ φ₂ = π ≫ eSec (G2 A₀) := square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_fst])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_snd])
  let P₀ : LB (G2 A₀).left := LB.LinComb M (K := Fin 2) ![𝟙 _, (G2 A₀).hom ≫ eSec (G2 A₀)] ![1, -1]
  have hP₀ : P₀.IsLB := LB.isLB_linComb hM _ _
  have hc : cls P₀ hP₀ = cls M hM - pull ((G2 A₀).hom ≫ eSec (G2 A₀)) (cls M hM) := by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp [pull_id, sub_eq_add_neg]
  refine ⟨P₀, φ₂, hP₀, hsqφ, ?_, ?_⟩
  · refine (cls_eq_iff hP (pull_isLB hP₀ φ₂)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, hMP, ← Category.assoc, hpb.w, Category.assoc, ← hφe,
      ← Category.assoc, pull_comp, hMP, pull_comp, hPe, map_zero, sub_zero]
  · refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, ← Category.assoc, he₀]
    erw [Category.id_comp, sub_self]

end GlobalTheory.SquareDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTripleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_maps_for_theta_triple : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∃ uT uM : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) →+ Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      (∀ Y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uT Y) ∧ (uT Y).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ (uT Y) = Y) ∧
      (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (uM z) ∧
        (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 ∧ (uM z).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = -z) ∧
      (∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u → ∃ Y z, u = uT Y + uM z) ∧
      (∀ x u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) u →
        evFin D.host.F Bs.v₁ (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x u) =
          ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j * GlobalTheory.VacShape.coBar Bs Γ u i j -
            ∑ i, ∑ j, GlobalTheory.VacShape.coBar Bs Γ x i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁)) i j) := by
  first | exact @GlobalTheory.LinCoords.coords | exact GlobalTheory.LinCoords.coords | (intros; apply GlobalTheory.LinCoords.coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsLiftComplete

theorem existsUnique_torsion_lift : ∀ (V K : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [Field K] (n : ℕ), IsAdicComplete (IsLocalRing.maximalIdeal V) V → IsUnit (n : V) → ∀ π : V →+* K, Function.Surjective π → ∀ (A₀ : Over (Sp K)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp V)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A₀ A (spMap π) i → ∀ s₀ : 𝟙_ (Over (Sp K)) ⟶ A₀, s₀ ^ n = 1 → ∃! s : 𝟙_ (Over (Sp V)) ⟶ A, s ^ n = 1 ∧ s₀.left ≫ i = spMap π ≫ s.left := by
  intro V K _ _ _ _ n hc hn π hπ A₀ _ _ A _ _ i hA hpb s₀ hs₀
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal V) V := hc
  haveI : HenselianLocalRing V := GlobalTheory.henselianLocalRing_of_henselianRing V
  haveI : Smooth A.hom := hA.smooth
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  haveI := GlobalTheory.GrpTangent.etale_id_pow A hn'
  let T' : Over (Sp K) := 𝟙_ (Over (Sp K))
  let T : Over (Sp V) := Over.mk (T'.hom ≫ spMap π)
  have hwi : i ≫ A.hom = A₀.hom ≫ spMap π := hpb.1.w
  have hpt : ∀ x : T' ⟶ A₀, (x.left ≫ i) ≫ A.hom = T.hom := by
    intro x
    rw [Category.assoc, hwi, ← Category.assoc, Over.w x]
    rfl
  let pt : (T' ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk (x.left ≫ i) (hpt x)
  have hone : pt 1 = 1 := by
    have h := hpb.2 T' 1 1 (pt 1) (pt 1) rfl rfl
    rw [_root_.mul_one] at h
    have h2 : pt 1 * pt 1 = pt 1 := Over.OverMorphism.ext h
    exact mul_eq_left.mp h2
  have hpow : ∀ m : ℕ, (pt s₀) ^ m = pt (s₀ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact Over.OverMorphism.ext (hpb.2 T' (s₀ ^ m) s₀ ((pt s₀) ^ m) (pt s₀) (by rw [ih]; rfl) rfl)
  have hx : (pt s₀) ^ n = 1 := by rw [hpow, hs₀, hone]
  let f : A.left ⟶ A.left := (𝟙 A ^ n).left
  have hf : ∀ {Y : Over (Sp V)} (y : Y ⟶ A), y.left ≫ f = (y ^ n).left := by
    intro Y y
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have hone' : ∀ {Y : Over (Sp V)} , ((1 : Y ⟶ A)).left = Y.hom ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hw : (s₀.left ≫ i) ≫ f = Spec.map (CommRingCat.ofHom π) ≫ (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    have := hf (pt s₀)
    rw [hx, hone'] at this
    simpa [pt, T, T'] using this
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ :=
    GlobalTheory.existsUnique_lift_of_etale_of_henselian f π hπ (s₀.left ≫ i) _ hw
  have hls : l ≫ A.hom = (𝟙_ (Over (Sp V))).hom := by
    have e : f ≫ A.hom = A.hom := Over.w (𝟙 A ^ n)
    rw [← e, ← Category.assoc, hl2]
    exact Over.w (η[A] : 𝟙_ (Over (Sp V)) ⟶ A)
  let s : 𝟙_ (Over (Sp V)) ⟶ A := Over.homMk l hls
  have hsn : ∀ s' : 𝟙_ (Over (Sp V)) ⟶ A, s' ^ n = 1 ↔ s'.left ≫ f = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
    intro s'
    have e1 : ((1 : 𝟙_ (Over (Sp V)) ⟶ A)).left = (η[A] : 𝟙_ (Over (Sp V)) ⟶ A).left := by
      rw [hone']; exact Category.id_comp _
    rw [hf]
    constructor
    · intro h; rw [h, e1]
    · intro h
      apply Over.OverMorphism.ext
      rw [h, e1]
  refine ⟨s, ⟨(hsn s).2 hl2, hl1.symm⟩, ?_⟩
  rintro s' ⟨h1, h2⟩
  exact Over.OverMorphism.ext (huniq s'.left ⟨h2.symm, (hsn s').1 h1⟩)

end GlobalTheory.TorsLiftComplete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSubsingletonOfClosedImmersionModIdeal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem fibre_subsingleton_of_isClosedImmersion_restrict :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
      (p : Z ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) →
      ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  intro R _ I X Z φ p hci z hz
  have hmem : ∀ x : X, φ x = z → x ∈ Set.range ((baseIdeal p I).comap φ).subschemeι := by
    intro x hx
    rw [Scheme.IdealSheafData.range_subschemeι, _root_.GlobalTheory.FormalAlg.baseIdeal_calculus.1 R Z X p φ I]
    show x ∈ (baseIdeal (φ ≫ p) I).support
    refine (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus.2.2 R X (φ ≫ p) I x).mpr ?_
    have e : (φ ≫ p) x = p (φ x) := by simp
    rw [e, hx]
    exact hz
  intro x hx x' hx'
  obtain ⟨y, rfl⟩ := hmem x hx
  obtain ⟨y', rfl⟩ := hmem x' hx'
  have hinj := (((baseIdeal p I).comap φ).subschemeι ≫ φ).isClosedEmbedding.injective
  have : y = y' := hinj (by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    have e : ∀ w, (((baseIdeal p I).comap φ).subschemeι ≫ φ) w = φ (((baseIdeal p I).comap φ).subschemeι w) := fun w => by simp
    rw [e, e, hx, hx'])
  rw [this]

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFibrePowerAndExternalTensorSectionNonzeroCloStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_fibrePower_and_externalTensorSection_nonzero_closedFibre : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) [Flat G.hom] (L : LB G.left) (θ : L.Sec), NonzeroClosed (X := G) θ → ∀ N : ℕ, Flat (pow G N).hom ∧ NonzeroClosed (X := pow G N) (boxSec G θ N) := by
  first | exact @GlobalTheory.BoxNonzeroClosed.main | exact GlobalTheory.BoxNonzeroClosed.main | (intros; apply GlobalTheory.BoxNonzeroClosed.main <;> assumption)
end

