module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.QuotientUniformizationLower
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AbPartFieldChange

theorem exists_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨P', mK, mB, h₁, h₂, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange E H S t L L' z P e
  exact ⟨P', mK, mB, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.AbPartFieldChange
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlock
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AmpleBlock

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem homog_rename (k₀ : K) {F : MvPolynomial (J k₀) ℤ} {n : ℕ} (h : F.IsHomogeneous n) :
    IsMultiHomog (rename (Sigma.mk k₀) F : MRing J) (Pi.single k₀ n) := by
  classical
  intro m hm k
  rw [support_rename_of_injective sigma_mk_injective] at hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hm
  have hd : ∑ i, m' i = n := by
    have := h (mem_support_iff.1 hm')
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.mapDomain_apply_of_injective sigma_mk_injective, hd]
  · have h0 : ∀ i, Finsupp.mapDomain (Sigma.mk k₀) m' ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨i', hi'⟩
        exact hk (congrArg Sigma.fst hi').symm)
    simp [h0, Pi.single_apply, hk]

theorem rel_at_point {y : (Σ k, J k) → Ω} (k₀ k : K) {A B : MvPolynomial (J k₀) ℤ} {n : ℕ}
    (hA : A.IsHomogeneous n) (hB : B.IsHomogeneous n) (j j' : J k)
    (hr : aeval (fun i => y ⟨k₀, i⟩) A * y ⟨k, j'⟩ = aeval (fun i => y ⟨k₀, i⟩) B * y ⟨k, j⟩)
    {L : Type} [Field L] {z : (Σ k, J k) → L} (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) :
    aeval (fun i => z ⟨k₀, i⟩) A * z ⟨k, j'⟩ = aeval (fun i => z ⟨k₀, i⟩) B * z ⟨k, j⟩ := by
  have hm : (rename (Sigma.mk k₀) A * X ⟨k, j'⟩ - rename (Sigma.mk k₀) B * X ⟨k, j⟩ : MRing J) ∈ mCoordIdeal y := by
    change mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hA),
      ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hB)]
    simp only [mConeMap, aeval_X, aeval_rename]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hr
    rw [map_mul, map_mul] at this
    simp only [Function.comp_def]
    linear_combination ((∏ k, (X k : MvPolynomial K Ω) ^ (Pi.single k₀ n : K → ℕ) k) * X k) * this
  have := hz.2 _ hm
  simp only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def] at this
  exact sub_eq_zero.mp this

def gForm (k₀ : K) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : MRing J :=
  X ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, rename (Sigma.mk k₀) (G k)

def hForm (k₀ : K) (j : ∀ k, J k) : MRing J :=
  ∏ k ∈ Finset.univ.erase k₀, X ⟨k, j k⟩

theorem gForm_homog (k₀ : K) (i : J k₀) (e : ℕ) {G : K → MvPolynomial (J k₀) ℤ} {d : K → ℕ}
    (hG : ∀ k, (G k).IsHomogeneous (d k)) :
    IsMultiHomog (gForm k₀ i e G) (Pi.single k₀ (e + ∑ k ∈ Finset.univ.erase k₀, d k)) := by
  have h := isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X' k₀ i : IsMultiHomog (X ⟨k₀, i⟩ : MRing J) _) e)
    (isMultiHomog_prod (Finset.univ.erase k₀) (fun k => rename (Sigma.mk k₀) (G k))
      (fun k => Pi.single k₀ (d k)) fun k => homog_rename k₀ (hG k))
  rw [gForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Pi.single_apply, hk]

def hDeg (k₀ : K) : K → ℕ := fun k => if k = k₀ then 0 else 1

theorem hForm_homog (k₀ : K) (j : ∀ k, J k) : IsMultiHomog (hForm k₀ j) (hDeg k₀) := by
  have h := isMultiHomog_prod (Finset.univ.erase k₀) (fun k => (X ⟨k, j k⟩ : MRing J))
      (fun k => Pi.single k 1) fun k => isMultiHomog_X' k (j k)
  rw [hForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [hDeg, Finset.sum_apply, Pi.single_apply]
  · simp [hDeg, Finset.sum_apply, Pi.single_apply, hk]

theorem aeval_gForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (i : J k₀) (e : ℕ)
    (G : K → MvPolynomial (J k₀) ℤ) :
    aeval z (gForm k₀ i e G) = z ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => z ⟨k₀, i⟩) (G k) := by
  simp [gForm, map_prod, aeval_rename, Function.comp_def]

theorem aeval_hForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (j : ∀ k, J k) :
    aeval z (hForm k₀ j) = ∏ k ∈ Finset.univ.erase k₀, z ⟨k, j k⟩ := by
  simp [hForm, map_prod]

def sec (y : (Σ k, J k) → Ω) (k₀ : K) (js : ∀ k, J k) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : Ω :=
  y ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => y ⟨k₀, i⟩) (G k) / y ⟨k, js k⟩

theorem sec_mul (y : (Σ k, J k) → Ω) (k₀ : K) (js j : ∀ k, J k) (hjs : ∀ k, y ⟨k, js k⟩ ≠ 0) (i : J k₀) (e : ℕ)
    (G G' : K → MvPolynomial (J k₀) ℤ)
    (hr : ∀ k, aeval (fun i => y ⟨k₀, i⟩) (G k) * y ⟨k, j k⟩ = aeval (fun i => y ⟨k₀, i⟩) (G' k) * y ⟨k, js k⟩) :
    aeval y (gForm k₀ i e G') = sec y k₀ js i e G * aeval y (hForm k₀ j) := by
  rw [aeval_gForm, aeval_hForm, sec, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have := hjs k
  field_simp
  exact (hr k).symm

theorem ampleQ_of_forms (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ) (ha₀ : a k₀ = 1) (ha : ∀ k, k ≠ k₀ → a k = 0)
    (l : K → ℕ) (n : ∀ k, Fin (l k) → ℕ) (F : ∀ k, Fin (l k) → J k → MvPolynomial (J k₀) ℤ)
    (hom : ∀ k t j, (F k t j).IsHomogeneous (n k t))
    (rel : ∀ k t j j', aeval (fun i => y ⟨k₀, i⟩) (F k t j) * y ⟨k, j'⟩ =
      aeval (fun i => y ⟨k₀, i⟩) (F k t j') * y ⟨k, j⟩)
    (pts : ∀ k (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) →
      ∃ t j, aeval (fun i => z ⟨k₀, i⟩) (F k t j) ≠ 0) :
    Ht.AmpleQ y a := by
  by_cases hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0
  swap
  · push_neg at hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨0, 0, Fin.elim0, fun i => i.elim0, fun L _ _ z hz => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := hz.1 k
    have hm : (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal y := by
      change mConeMap y _ = 0
      simp [mConeMap, hk i]
    exact hi (by simpa using hz.2 _ hm)
  choose js hjs using hy

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ T : ∀ k, Fin (l k), ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ N := by
    refine ⟨∑ k, ∑ t, n k t, fun T => ?_⟩
    calc ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ ∑ k ∈ Finset.univ.erase k₀, ∑ t, n k t :=
          Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := n k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  let eT : (∀ k, Fin (l k)) → ℕ := fun T => N - ∑ k ∈ Finset.univ.erase k₀, n k (T k)
  have heT : ∀ T, eT T + ∑ k ∈ Finset.univ.erase k₀, n k (T k) = N := fun T => Nat.sub_add_cancel (hN T)
  let I := (∀ k, Fin (l k)) × J k₀
  let S : I → Ω := fun p => sec y k₀ js p.2 (eT p.1) fun k => F k (p.1 k) (js k)
  have hdeg : ∀ k, ((Pi.single k₀ N : K → ℕ) k : ℤ) = hDeg k₀ k + (((N + 1 : ℕ) : ℤ) * a k - 1) := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simp [hDeg, ha₀]
    · simp [hDeg, Pi.single_apply, hk, ha k hk]

  have hform : ∀ (p : I) (j : ∀ k, J k), IsMultiHomog (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k))
      (Pi.single k₀ N) ∧ aeval y (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) = S p * aeval y (hForm k₀ j) := by
    intro p j
    refine ⟨?_, sec_mul y k₀ js j hjs _ _ _ _ fun k => rel k (p.1 k) (js k) (j k)⟩
    have := gForm_homog k₀ p.2 (eT p.1) (G := fun k => F k (p.1 k) (j k)) (d := fun k => n k (p.1 k))
      fun k => hom k _ _
    rwa [heT] at this
  refine ⟨N + 1, Fintype.card I, fun q => S ((Fintype.equivFin I).symm q), fun q c hc => ?_, fun L _ _ z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := hform ((Fintype.equivFin I).symm q) c
    have h3 := FibreNormDehomRoots.aeval_mem_chartLatNm h1 c hc
    convert h3 using 1
    rw [h2, aeval_hForm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)]
    have e1 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) * a k - 1))) =
        ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ := by
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [ha k (Finset.ne_of_mem_erase hk)]
    have e2 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * (Pi.single k₀ N : K → ℕ) k : ℕ) : ℤ))) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      simp [Pi.single_apply, Finset.ne_of_mem_erase hk]
    rw [e1, e2]
    simp [ha₀]
    ring
  · obtain ⟨i, hi⟩ := hz.1 k₀
    choose T jz hF using fun k => pts k L z hz
    have hzj : ∀ k, z ⟨k, jz k⟩ ≠ 0 := by
      intro k h0
      obtain ⟨j', hj'⟩ := hz.1 k
      have := rel_at_point k₀ k (hom k (T k) (jz k)) (hom k (T k) j') (jz k) j' (rel k _ _ _) hz
      rw [h0, mul_zero] at this
      exact mul_ne_zero (hF k) hj' this
    obtain ⟨h1, h2⟩ := hform (T, i) jz
    have hg : aeval z (gForm k₀ i (eT T) fun k => F k (T k) (jz k)) ≠ 0 := by
      rw [aeval_gForm]
      exact mul_ne_zero (pow_ne_zero _ hi) (Finset.prod_ne_zero_iff.mpr fun k _ => hF k)
    have hh : aeval z (hForm k₀ jz) ≠ 0 := by
      rw [aeval_hForm]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hzj k
    refine ⟨Fintype.equivFin I (T, i), _ / _, div_ne_zero hg hh, Pi.single k₀ N, hDeg k₀, _, hForm k₀ jz, h1,
      hForm_homog k₀ jz, hdeg, ?_, hh, (div_mul_cancel₀ _ hh).symm⟩
    simpa using h2

theorem ampleQ_of_embeds : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  intro X Ω _ _ ξ K _ J _ y k₀ a hT hE ha₀ ha
  classical
  choose l n F hom rel pts using _root_.GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families X Ω ξ K J y k₀ hT hE
  exact ampleQ_of_forms y k₀ a ha₀ ha l n F hom rel fun k L _ _ z hz => pts k L z hz

end GlobalTheory.CompanionTheory.Ar.AmpleBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyReindexedStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reindexed : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (D d : ℕ), Function.Injective bk → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → IsArithVar (mCoordIdeal y₀) (D + 1) → IsArithVar (mCoordIdeal y) (D + 1) → Birational y₀ → Birational y → (letI := i.toAlgebra; Module.finrank Ω₀ Ω = d) → 0 < d → ∃ (Gf : GenFibre (GlobalTheory.CompanionTheory.Ar.Chg.blkV bk bx) (mCoordIdeal y)) (ch : ∀ k : FibreBlock bk, J k.1), (∀ k : FibreBlock bk, Gf.x' ⟨k.1, ch k⟩ ≠ 0) ∧ Module.finrank Gf.Φ (IntermediateField.adjoin Gf.Φ (Set.range fun q : Σ k : FibreBlock bk, J k.1 => Gf.x' ⟨q.1.1, q.2⟩ / Gf.x' ⟨q.1.1, ch q.1⟩)) = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | exact GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.GenFib.exists_genFibre_chart_degree <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLieMetricBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

-- Some dependency stubs refer to this doubly qualified name when unfolding `LieModel.Lifts`.
-- Keep it definitionally equal to the actual map.
abbrev GlobalTheory.CompanionTheory.Ar.GlobalTheory.CompanionTheory.Ar.dualMap
    {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    DualNumber R →+* DualNumber R' :=
  _root_.GlobalTheory.CompanionTheory.Ar.dualMap φ

theorem GlobalTheory.CompanionTheory.Ar.QuotUnif.chart_coords_le_metric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (jj : Sp C.R ⟶ X) (m : SABMap C.t t jj) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (h : LieMetric M y) (N : ℕ) (s : Fin N → Li) (sc : Fin N → Fin C.g → C.R) (ww : (Fin n → ℂ) → (Σ k, J k) → ℂ), ContinuousOn ww (ball 0 1) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∃ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), ∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, CoordsAt ξ y (spMap (C.ψ u) ≫ jj) (ww u)) → (∀ u ∈ ball (0 : Fin n → ℂ) 1, ∀ i, ∃ v : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G, M.ValAt (spMap (C.ψ u) ≫ jj) (s i) v ∧ v.left = spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt (sc i)).left ≫ m.φ) → (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (spMap (C.ψ 0) ≫ jj) V) (b : Fin N → V), (∀ i, M.ValAt (spMap (C.ψ 0) ≫ jj) (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤) → ∃ ρ Kc : ℝ, 0 < ρ ∧ 0 < Kc ∧ ∀ u ∈ ball (0 : Fin n → ℂ) ρ, ∀ Mz : LieModel C.t.G (spMap (C.ψ u)) (Fin C.g → ℂ), (∀ e : Fin C.g → C.R, ((Mz.pt fun i => C.ψ u (e i)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.GlobalTheory.CompanionTheory.Ar.dualMap (C.ψ u)) ≫ (C.M.pt e).left)) → ∀ (x : Fin C.g → ℂ) (v₀ : epsAt (spMap (C.ψ u) ≫ jj) ⟶ t.G), (Mz.pt x).left ≫ m.φ = v₀.left → ∑ i, ‖x i‖ ^ 2 ≤ Kc * (h.ip (spMap (C.ψ u) ≫ jj) v₀ v₀).re :=
  @PositivityTheory.Xgn.quotient_uniformization_lower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoordsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_closure_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ w : (Σ k, J k) → ℂ, w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'} →
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsInCoordRatioField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CstChart

theorem germ_top_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {q : X}
    (hq : ξ (IsLocalRing.closedPoint Ω) ⤳ q) :
    X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial) ≫ X.presheaf.stalkSpecializes hq ≫
        Scheme.stalkClosedPointTo ξ = ξ.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
  have e : ∀ (f : (⊤ : (Spec (CommRingCat.of Ω)).Opens) ⟶ ξ ⁻¹ᵁ ⊤),
      (Spec (CommRingCat.of Ω)).presheaf.map f.op = 𝟙 _ := fun f => (Spec (CommRingCat.of Ω)).presheaf.map_id _
  erw [e]
  simp

theorem ringHom_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] (φ : O →+* Ω) (s : X ⟶ Spec (CommRingCat.of O))
    (h : ξ ≫ s = Spec.map (CommRingCat.ofHom φ)) (p : Cpt ξ) (o : O) : φ o ∈ regAt ξ p := by
  obtain ⟨q, hq⟩ := p
  refine ⟨X.presheaf.germ ⊤ q (show q ∈ (⊤ : X.Opens) from trivial)
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)), ?_⟩
  have h1 := germ_top_stalk ξ hq
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ ξ.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom φ := by
    have : s.appTop ≫ ξ.appTop = (ξ ≫ s).appTop := by simp
    rw [reassoc_of% this, h]
    simp
  have h3 := congrArg (fun f => f.hom o) h2
  have h4 := congrArg (fun f => f.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  rw [CommRingCat.hom_ofHom] at h3
  refine Eq.trans ?_ (h4.trans h3)
  rfl

theorem segre_adjoin_le {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) :
    Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩) ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)).restrictScalars ℤ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, cc k⟩ ∈
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩)
  rw [← Finset.prod_div_distrib]
  exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem cst_mem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (cc : (k : K) → J k), (∀ k, y ⟨k, cc k⟩ ≠ 0) → ∀ r : c.F, 𝔐.cst r ∈ Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 cc hcc r
  have hx : (∏ k, y ⟨k, cc k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hcc k
  have hint : ∀ a : 𝓞 c.F, 𝔐.cst (algebraMap (𝓞 c.F) c.F a) ∈
      Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, cc p.1⟩) := fun a =>
    segre_adjoin_le y cc ((𝔐.tie.ring cc hx _).2 fun p _ =>
      ringHom_mem_regAt 𝔐.ξ (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) (𝔐.f ≫ Y.s) 𝔐.cst_over p a)
  haveI : FiniteDimensional ℚ c.F := c.fin
  have halg : IsAlgebraic ℤ r := (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic r)
  obtain ⟨n, hn, hr⟩ := halg.exists_integral_multiple
  have hn' : (n : Ω) ≠ 0 := Int.cast_ne_zero.2 hn
  have e : 𝔐.cst r = algebraMap ℚ Ω (n : ℚ)⁻¹ *
      𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) (n • r) hr)) := by
    rw [IsIntegralClosure.algebraMap_mk', zsmul_eq_mul, map_mul, map_intCast]
    simp [hn']
  rw [e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hint _)

end GlobalTheory.CompanionTheory.Ar.CstChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def PolarisedAt {X : Scheme.{0}} (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) : Prop :=
  ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}


open Classical in
def gramFn (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) (w : (Σ k, J k) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  if h : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ y z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ then h.choose else 0

def recentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) : Fin n → ℂ :=
  t₀ + (ρ : ℂ) • (u ∘ π)

def uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (ρ : ℂ)⁻¹ * (t (π.symm i) - t₀ (π.symm i))

def periodGram {n a₀ g r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) (u : Fin n → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => Real.pi * (U j u ⬝ᵥ L.H u *ᵥ star (U i u))

def IsFramePeriods (𝔐 : HodgeCpt Y S y) {r : ℕ} (b : Fin r → 𝔐.Li) {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω) {a₀ g : ℕ}
    {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ)
    (U : Fin r → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  0 < ρ ∧ ρ ≤ 1 ∧ (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) ∧ LinearIndependent ℂ (fun k => U k 0) ∧
  (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧
  ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
    InFrameDomain y cc f (χ.γ (recentre t₀ ρ π u)) ∧ (χ.γ (recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) ∧
    (u ∈ Flat.punct n a₀ 1 → ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ (recentre t₀ ρ π u)) →
      𝔐.M.GramAt 𝔐.t.PP.L z b (periodGram L U u))

theorem recentre_uncentre {n : ℕ} (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n)) (t : Fin n → ℂ) :
    recentre t₀ ρ π (uncentre t₀ ρ π t) = t := by
  have h : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  funext i
  simp [recentre, uncentre, h]

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (Flat.punct n a ρ) := by
  have : Flat.punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | i.val < a → z i ≠ 0} := by
    ext z; simp [Flat.punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases h : i.val < a
  · simpa [h] using isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [h]

theorem contDiff_uncentre {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uncentre t₀ ρ π) := by
  unfold uncentre
  exact contDiff_pi.2 fun i => contDiff_const.mul ((contDiff_apply ℝ (fun _ => ℂ) (π.symm i)).sub contDiff_const)

theorem uncentre_mem_ball {n : ℕ} {t₀ t : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (π : Equiv.Perm (Fin n))
    (h : ‖t - t₀‖ < ρ) : uncentre t₀ ρ π t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖t (π.symm i) - t₀ (π.symm i)‖ ≤ ‖t - t₀‖ := norm_le_pi_norm (t - t₀) (π.symm i)
  simp only [uncentre, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  rw [inv_mul_lt_iff₀ hρ]
  linarith

theorem uncentre_self {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : uncentre t ρ π t = 0 := by
  funext i
  simp [uncentre]

theorem recentre_zero {n : ℕ} (t : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) : recentre t ρ π 0 = t := by
  funext i
  simp [recentre]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExistsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_basis_exists : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (τ : 𝓞 E →+* k), Nonempty (Module.Basis (Fin (Module.finrank ℤ X / Module.finrank ℚ E)) k (GlobalTheory.Diag.eigenHom X τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom | exact GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.LatMult.nonempty_basis_eigenHom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootHeightDifferenceBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_height_difference_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c t s lo hi : ℝ) (lam : Wt Ψ N), Close M R i u c → ArchBetween M R i u t lam s lo hi → ∀ (L : Type) [Field L] [NumberField L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), rootHt M t lam s L (fun p => z (joinInl M.ι R.ι p)) - rootHt R 1 lam s L (fun p => z (joinInr M.ι R.ι p)) ∈ Set.Icc (lo - (l1 lam + |s|) * c) (hi + (l1 lam + |s|) * c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseHt.close_ht <;> assumption)
end

