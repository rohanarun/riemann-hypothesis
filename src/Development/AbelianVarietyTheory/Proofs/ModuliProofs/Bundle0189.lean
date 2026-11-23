module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfValFGeneric
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProducts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  first | exact @GlobalTheory.cutBy_idealOf_torsion | exact GlobalTheory.cutBy_idealOf_torsion | (intros; apply GlobalTheory.cutBy_idealOf_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAmpFramesExponents
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_ampFrames_of_cover (laws : Laws) {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens}
    {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE) (hU₀ : (U₀ : Set M.Z).Nonempty) {I : Type} (U : I → M.Z.Opens) (x : I → S.Gam)
    (b : I → Matrix S.J S.J Ω) (r : ℤ) (u : I → Ω) (hu : ∀ i, u i = S.th (x i) ^ (r + Fintype.card S.J) / (b i).det)
    (hcov : ∀ z, ∃ i, z ∈ U i) (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty)
    (hb : ∀ i, (b i).det ≠ 0)
    (hx : ∀ i, ∀ z ∈ U i, x i ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range (b i)))
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ A : LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  have h0 : ∀ i, S.th (x i) ≠ 0 := fun i => (hx i _ (hne i).some_mem).1.1
  obtain ⟨g, hLB, hamp, hg⟩ := exists_ample M U u hcov haff hne
    (fun i => by rw [hu]; exact div_ne_zero (zpow_ne_zero _ (h0 i)) (hb i)) hreg hconv
  choose σ hσ gσ nσ using fun i => Z.theta (U i) (x i) fun z hz => (hx i z hz).1
  choose τ hτ nτ using fun i => Z.sections (U i) (x i) (b i) (hx i)
  let e : Fin (Fintype.card S.J) ≃ S.J := (Fintype.equivFin S.J).symm
  refine ⟨⟨LB.mk I U g, hLB, hamp, Fintype.card S.J, fun i => secOver Z.G 1 (hσ i) _ (fun t => t.2),
    fun i k => secOver Z.G S.N (hτ i (e k)).1 _ (fun t => t.2), r, 1, fun i j => ?_, fun i V _ _ _ hV χ hχ => ?_⟩, rfl, rfl⟩
  · have n₂ : ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf (hne i) (hne j)
    obtain ⟨c, hc⟩ := exists_unit M n₂ (div_ne_zero (h0 j) (h0 i)) (fun z hz => (hx i z hz.1).1.2 _)
      (fun z hz => by rw [inv_div]; exact (hx j z hz.2).1.2 _)
    have reg : ∀ i j, ∀ z ∈ U i, z ∈ U j → ∀ k k',
        (((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e) k k' ∈ M.O z := fun i j z hi hj k k' =>
      (M.O z).mul_mem ((hx i z hi).1.2 _) ((mem_span_rows_iff (M.O z) (hb j) (b i (e k))).1
        ((hx j z hj).2 ▸ (hx i z hi).2 ▸ Submodule.subset_span ⟨e k, rfl⟩) (e k'))
    obtain ⟨m, hm⟩ := exists_GL M n₂ (A := ((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e)
      (A' := ((S.th (x i) / S.th (x j)) • (b j * (b i)⁻¹)).submatrix e e) (by
        rw [Matrix.submatrix_mul_equiv, smul_mul_smul_comm, div_mul_div_cancel₀ (h0 i), div_self (h0 j), one_smul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hb j).isUnit, Matrix.mul_nonsing_inv _ (hb i).isUnit,
          Matrix.submatrix_one_equiv])
      (fun z hz => reg i j z hz.1 hz.2) (fun z hz => reg j i z hz.2 hz.1)
    have one : valF M.pt (U i ⊓ U j) 1 = 1 := (M.res_apply _ n₂ 1).symm.trans (map_one _)
    refine ⟨Units.map (U i ⊓ U j).topIso.inv.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map (U i ⊓ U j).topIso.inv.hom m,
      ⟨_, lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ i) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (gσ i) (fun _ => gσ i) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ j) inf_le_left inf_le_right (fun _ => c.val)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (gσ i) (fun _ => gσ j) _ fun _ => by
            rw [Fin.sum_univ_one, ← M.res_apply _ n₂, hc, div_mul_eq_mul_div, mul_inv_cancel₀ (h0 j), one_div])
          _ _ (fun _ => rfl)⟩,
      fun k => ⟨_, lin_secOver Z.G S.N (hτ i (e k)).1 (fun _ : Fin 1 => (hτ i (e k)).1) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (hτ i (e k)).2 (fun _ => (hτ i (e k)).2) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G S.N (hτ i (e k)).1 (fun k' => (hτ j (e k')).1) inf_le_left inf_le_right (fun k' => m.val k k')
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (hτ i (e k)).2 (fun k' => (hτ j (e k')).2) _ fun l => ?_)
          _ _ (fun _ => rfl)⟩, ?_⟩
    · have v : ∀ k', valF M.pt (U i ⊓ U j) (m.val k k') = S.th (x j) / S.th (x i) * (b i * (b j)⁻¹) (e k) (e k') :=
        fun k' => (M.res_apply _ n₂ _).symm.trans (congrFun (congrFun hm k) k')
      have w : b i (e k) l = ∑ k', (b i * (b j)⁻¹) (e k) (e k') * b j (e k') l := by
        rw [e.sum_comp (fun a => (b i * (b j)⁻¹) (e k) a * b j a l), ← Matrix.mul_apply,
          Matrix.nonsing_inv_mul_cancel_right _ _ (hb j).isUnit]
      rw [w, Finset.sum_div]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [v]
      have := h0 i
      have := h0 j
      field_simp
    · have key : g i j = c ^ r * Matrix.GeneralLinearGroup.det m := by
        refine Units.ext (M.res_injective _ n₂ ((hg i j).trans (Eq.symm ?_)))
        have e₁ : M.res _ n₂ (c ^ r).val = (S.th (x j) / S.th (x i)) ^ r := by
          rw [← hc]
          exact (congrArg Units.val (map_zpow (Units.map (M.res _ n₂).toMonoidHom) c r)).trans (Units.val_zpow_eq_zpow_val _ _)
        rw [Units.val_mul, map_mul, e₁, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, hm,
          Matrix.det_submatrix_equiv_self, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          hu, hu, zpow_add₀ (h0 i), zpow_add₀ (h0 j), div_zpow, div_pow, zpow_natCast, zpow_natCast]
        have := h0 i
        have := h0 j
        have := hb i
        have := hb j
        field_simp
      show (U i ⊓ U j).topIso.inv.hom (g i j).val = _
      rw [key, zpow_one, Matrix.GeneralLinearGroup.map_det, ← map_zpow]
      exact map_mul _ _ _
  · let W₀ : M.Z.Opens := ⟨abLocus Z.G, by rw [Z.ab]; exact isOpen_TT_eq_bot S M⟩
    obtain ⟨ha, hk⟩ := Z.pol W₀ subset_rfl
    obtain ⟨A, φ, h₁, h₂, h₃⟩ := exists_polAV Z.G Z.semi S.g Z.dim Z.L Z.sym W₀ ha hk _ hχ
    have hr : ∀ {K : Type} [Field K] (y : Sp K ⟶ (U i).toScheme), Set.range (y ≫ (U i).ι) ⊆ U i := by
      rintro K _ y _ ⟨w, rfl⟩
      exact (y w).2
    refine ⟨GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L 1 1 (Over.mk (U i).ι) _ Z.L.isLB Z.semi le_rfl (fun K _ _ y c H => ?_) V hV χ A φ
        h₁ h₂ (one_pow _).symm,
      GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L S.N _ (Over.mk (U i).ι) _ Z.L.isLB Z.semi (one_le_two.trans S.N_ge)
        (fun K _ _ y c H => ?_) V hV χ A φ h₁ h₂ (ρ.card.trans (by rw [h₃]))⟩
    · obtain ⟨p, j, hp, hne⟩ := nσ i K _ (hr y)
      have := indep_secOver Z.G 1 (fun _ : Fin 1 => hσ i) y c H p j hp
      rw [Fin.sum_univ_one] at this
      exact funext fun a => by rw [Subsingleton.elim a 0]; exact (mul_eq_zero.1 this).resolve_right hne
    · have := (nτ i K _ (hr y)).2 (c ∘ e.symm) fun p j hp => by
        rw [← e.sum_comp]
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
          indep_secOver Z.G S.N (fun k => (hτ i (e k)).1) y c H p j hp
      exact funext fun a => by simpa using congrFun this (e a)

end GlobalTheory.AmpModel

namespace GlobalTheory

open AmpModel

theorem exists_ampFrames_exponents : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG : Fin n → S.J → Ω) (Z : ZHOut ρ M U₀ EE), M.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) → S.Over₀ M U₀ → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  intro laws o Ω _ _ _ _ S ρ M U₀ EE n a GG Z hN hO hdual
  let d : (S.J → Fin n) → Ω := fun k => Matrix.det (Matrix.of fun i j => GG (k i) j)
  let t : S.Gam × (S.J → Fin n) → Ω := fun q => S.th q.1 * d q.2
  refine ⟨1 + ((a : ℤ) - 1) * Fintype.card S.J, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Int.le.dest hr
  choose U haff hU _ using fun i : {q // t q ≠ 0} => hN.2 i.1 i.2
  have mem : ∀ i z, z ∈ U i ↔ M.Div t i.1 z := fun i z => Set.ext_iff.1 (hU i) z
  have h0 : ∀ i : {q // t q ≠ 0}, S.th i.1.1 ≠ 0 := fun i => left_ne_zero_of_mul i.2
  have hd : ∀ i : {q // t q ≠ 0}, d i.1.2 ≠ 0 := fun i => right_ne_zero_of_mul i.2
  have hth : ∀ i, ∀ z ∈ U i, i.1.1 ∈ S.supI M z := fun i z hz => ⟨h0 i, fun y => by
    have := ((mem i z).1 hz).2 (y, i.1.2)
    rwa [mul_div_mul_right _ _ (hd i)] at this⟩
  have hmin : ∀ i, ∀ z ∈ U i, ∀ k, d k / d i.1.2 ∈ M.O z := fun i z hz k => by
    have := ((mem i z).1 hz).2 (i.1.1, k)
    rwa [mul_div_mul_left _ _ (h0 i)] at this
  let B : {q // t q ≠ 0} → (S.J → Fin n) → Matrix S.J S.J Ω := fun i k => Matrix.of fun l j => GG (k l) j / S.th i.1.1 ^ a
  have hB : ∀ i k, (B i k).det = d k / (S.th i.1.1 ^ a) ^ Fintype.card S.J := fun i k => by
    have : B i k = (S.th i.1.1 ^ a)⁻¹ • Matrix.of fun l j => GG (k l) j := by
      ext l j
      simp [B, div_eq_inv_mul]
    rw [this, Matrix.det_smul, inv_pow, div_eq_inv_mul]
  have hB0 : ∀ i, (B i i.1.2).det ≠ 0 := fun i => by
    rw [hB]; exact div_ne_zero (hd i) (pow_ne_zero _ (pow_ne_zero _ (h0 i)))
  have hdet : ∀ i, ((B i i.1.2)⁻¹).transpose.det = (S.th i.1.1 ^ a) ^ Fintype.card S.J / d i.1.2 := fun i => by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hB, inv_div]
  have ratio : ∀ i j : {q // t q ≠ 0}, t j.1 * S.th j.1.1 ^ e / (t i.1 * S.th i.1.1 ^ e) =
      t j.1 / t i.1 * (S.th j.1.1 / S.th i.1.1) ^ e := fun i j => by rw [div_pow, div_mul_div_comm]
  refine exists_ampFrames_of_cover laws Z hO.ne U (fun i => i.1.1) (fun i => ((B i i.1.2)⁻¹).transpose) _
    (fun i => t i.1 * S.th i.1.1 ^ e) (fun i => ?_) (fun z => ?_) haff
    (fun i => ⟨_, (mem i _).2 (RatModel.div_genericPoint i.2)⟩) (fun i => ?_) (fun i z hz => ⟨hth i z hz, ?_⟩)
    (fun i j z hz => ?_) (fun i j z hz h => ?_)
  · have : 1 + ((a : ℤ) - 1) * Fintype.card S.J + e + Fintype.card S.J = ((1 + e + a * Fintype.card S.J : ℕ) : ℤ) := by
      push_cast; ring
    rw [hdet, this, zpow_natCast]
    have := h0 i
    have := hd i
    simp only [t]
    field_simp
    ring
  · obtain ⟨q, hq⟩ := hN.1 z
    exact ⟨⟨q, hq.1⟩, (mem _ z).2 hq⟩
  · rw [hdet]; exact div_ne_zero (pow_ne_zero _ (pow_ne_zero _ (h0 i))) (hd i)
  · obtain ⟨V, b, hzV, hb, hE⟩ := EE.loc z
    rw [hE z hzV]
    refine eq_span_dual (M.O z) hb (hB0 i) fun w => ?_
    rw [← hE z hzV, ← hdual z _ (hth i z hz) w]
    have dd : ∀ k, (Pi.basisFun Ω S.J).det ((fun k j => GG k j / S.th i.1.1 ^ a) ∘ k) = (B i k).det := fun k => by
      rw [Module.Basis.det_apply, ← Matrix.det_transpose]
      congr 1
    have := MaximalMinor.span_range_comp_eq (A := M.O z) (Pi.basisFun Ω S.J) (fun k j => GG k j / S.th i.1.1 ^ a)
      (σ := i.1.2) (mem_nonZeroDivisors_of_ne_zero (by rw [dd]; exact hB0 i)) fun k => by
        rw [dd, dd, hB, hB]
        refine Submodule.mem_span_singleton.2 ⟨⟨_, hmin i z hz k⟩, ?_⟩
        have := hd i
        show d k / d i.1.2 * _ = _
        field_simp
    exact SetLike.ext_iff.1 this w
  · rw [ratio]
    exact (M.O z).mul_mem (((mem i z).1 hz).2 _) (pow_mem ((hth i z hz).2 _) _)
  · rw [ratio] at h
    refine (mem j z).2 ⟨j.2, fun q => ?_⟩
    have := (M.O z).mul_mem ((M.O z).mul_mem (((mem i z).1 hz).2 q) h) (pow_mem ((hth i z hz).2 j.1.1) e)
    convert this using 1
    have := h0 i
    have := h0 j
    have := i.2
    have := j.2
    rw [div_pow, div_pow]
    field_simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDenseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighthPower_principalSiegel_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  first | exact @GlobalTheory.SharpFamily.exists_isSharp_of_dense | exact GlobalTheory.SharpFamily.exists_isSharp_of_dense | (intros; apply GlobalTheory.SharpFamily.exists_isSharp_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_volume_veryAmple_products : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)) (r : ℕ) (ε : Fin r → I → ℤ), 1 ≤ r → (∀ k, ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb P.L φ (ε k)).Sec), VAmp P.A.hom _ th) → ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) → Vol P.A.hom (LB.LinComb P.L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) P.g ((MvPolynomial.eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ) := by
  first | exact @GlobalTheory.VolPoly.exists_homogeneous_vol | exact GlobalTheory.VolPoly.exists_homogeneous_vol | (intros; apply GlobalTheory.VolPoly.exists_homogeneous_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPELTriple_of_dense_fibres : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (w w' : J), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), em ρ = H.rt0 → Function.Injective em → Dense (fromSet em (PELClass (b := b) D a bas ρ em) t) → ∃ τ : SAB H S, IsPEL D a bas ρ t τ := by
  first | exact @GlobalTheory.PELFamily.exists_isPEL_of_dense | exact GlobalTheory.PELFamily.exists_isPEL_of_dense | (intros; apply GlobalTheory.PELFamily.exists_isPEL_of_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleExt

theorem exists_hom {X U : Scheme.{0}} {j : U ⟶ X} {G G' : Over X} [GrpObj G] [GrpObj G'] {G₀ : Over U} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} {φ' : G₀.left ⟶ G'.left} (h : IsGrpPullback G₀ G j φ) (h' : IsGrpPullback G₀ G' j φ')
    (hx : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f) :
    ∃ F : G ⟶ G', IsMonHom F ∧ φ ≫ F.left = φ' := by
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h (isGrpPullback_pullback G j)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso h' (isGrpPullback_pullback G' j)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx (e.inv ≫ e'.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  rw [← hφ, Category.assoc, ← ExtUnique.pullback_map_left_fst j F, hFf, ← Category.assoc, ← Over.comp_left,
    e.hom_inv_id_assoc, hφ']

end TripleExt
end GlobalTheory

theorem GlobalTheory.exists_sabMap_id_of_common_generic : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X), (Geo.Tor.IsNormalScheme X ∧ ∃ z : X ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z) → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (t₀ : SAB H U) (t t' : SAB H X) (a : SABMap t₀ t j) (a' : SABMap t₀ t' j), IsProper t₀.G.hom → ∃ b : SABMap t t' (𝟙 X), a.φ ≫ b.φ = a'.φ := by
  intro hdvr E _ _ _ H X U j hX hj₁ hj₂ hj₃ hj₄ t₀ t t' a a' hp
  obtain ⟨hgen, -, hdom, -⟩ := densePart_basic X U j hj₁ hj₂ hj₃ hj₄
  have hred : IsReduced X := by
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      have := (hX.1 x).1
      infer_instance
    exact isReduced_of_isReduced_stalk X
  have hnoeth : IsLocallyNoetherian X := by
    obtain ⟨z, hz, -⟩ := hX.2
    exact LocallyOfFiniteType.isLocallyNoetherian z
  have := hdom hred
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t.G t.semi
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian t'.G t'.semi
  obtain ⟨F, hF, hφ⟩ := TripleExt.exists_hom a.cart a'.cart
    (_root_.GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t.G t'.G t.semi t'.semi)
  obtain ⟨F', -, hφ'⟩ := TripleExt.exists_hom a'.cart a.cart
    (_root_.GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr X U j hX hj₁ hj₂ hj₃ hj₄ t'.G t.G t'.semi t.semi)
  have hiso : IsIso F := ExtUnique.isIso_of_isPullback a.cart.1 a'.cart.1 (Iso.refl _) F F'
    ((Category.id_comp _).trans hφ.symm) ((Category.id_comp _).trans hφ'.symm)
  have gp : IsGrpPullback t.G t'.G (𝟙 X) F.left :=
    haveI : IsMonHom (asIso F).hom := hF
    isGrpPullback_of_iso (asIso F)
  have hact : ∀ x, (t.act.act x).left ≫ F.left = F.left ≫ (t'.act.act x).left := fun x => by
    have : t.act.act x ≫ F = F ≫ t'.act.act x := ExtUnique.over_hom_ext_of_isPullback a.cart.1 (by
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← a.act, Category.assoc, hφ, ← Category.assoc, hφ,
        a'.act])
    exact congrArg (fun z => z.left) this
  have hlb : LBIso t.PP.L (t'.PP.L.pull F.left) := by
    obtain ⟨w, hw, -⟩ := (isPullCubical_iff _ _ _).1 a.lin
    obtain ⟨w', hw', -⟩ := (isPullCubical_iff _ _ _).1 a'.lin
    have hw'' : ∃ w'' : LB.Iso t₀.PP.L (t'.PP.L.pull (a.cm.F ≫ F.left)), PGen w'' := by
      rw [hφ]; exact ⟨w', hw'⟩
    obtain ⟨w'', hw''⟩ := hw''
    obtain ⟨r, hr, -⟩ := Exist.CubicalExtension.exists_quot_of_isos t'.PP.isLB t.PP.isLB t₀.PP.isLB w w'' hw hw''
      a.cart.1.isoPullback.inv (pullback.fst t.G.hom j) a.cart.1.isoPullback_inv_fst
    obtain ⟨ρ, hρ, -⟩ := Exist.CubicalExtension.exists_quot_of_gens (CubeMap.ofHom F).e_comm t'.PP.rig t.PP.rig
      t'.PP.rigGen t.PP.rigGen
    have sm := t.semi.smooth
    have gc := t.semi.geomConnected
    exact _root_.GlobalTheory.GenericExtend.exists_isGen_of_densePart X U j hX.1 hj₁ hj₂ hj₃ hj₄ t.G (eSec t.G) (LB.div (t'.PP.L.pull F.left) t.PP.L) (Over.w η[t.G])
      sm (grpObj_geometricallyIntegral_of_smooth X t.G) (LB.isLB_div (LB.isLB_pull t'.PP.isLB _) t.PP.isLB) ⟨ρ, hρ⟩ ⟨r, hr⟩
  obtain ⟨b, hb⟩ := exists_sabMap_of_lbIso E H X X t' t (𝟙 X) F.left
    ⟨hred, hgen.trans (range_subset_abLocus_of_isProper t.semi a.cart.1)⟩ gp hact hlb
  exact ⟨b, by rw [hb]; exact hφ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecNeZeroOfLbIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleSpecialisation

theorem exists_sec_ne_zero_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push Not at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pull_div_lbPow {X Y : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (f : Y ⟶ X) (a : ℕ) :
    LBIso ((LB.div (lbPow M a) L).pull f) (LB.div (lbPow (M.pull f) a) (L.pull f)) := by
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hp' : (lbPow (M.pull f) a).IsLB := LB.isLB_linComb (pull_isLB hM f) _ _
  refine (CechPic.cls_eq_iff (pull_isLB (LB.isLB_div hp hL) f) (LB.isLB_div hp' (pull_isLB hL f))).1 ?_
  rw [CechPic.cls_pull (LB.isLB_div hp hL), CechPic.cls_div hp hL, CechPic.cls_div hp' (pull_isLB hL f),
    CechPic.cls_lbPow hM, CechPic.cls_lbPow (pull_isLB hM f), CechPic.cls_pull hM, CechPic.cls_pull hL,
    map_sub, map_nsmul]

def baseChange {S S' : Scheme.{0}} (P : Out.PolAV S) (f : S' ⟶ S) : Out.PolAV S' where
  A := (Over.pullback f).obj P.A
  isAb := Out.TLinPf.isAb_pullback f P.A P.isAb
  g := P.g
  smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (isGrpPullback_pullback P.A f).1 P.smoothDim
  L := P.L.pull (pullback.fst P.A.hom f)
  isLB := pull_isLB P.isLB _
  rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
  sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
  ample :=
    haveI := P.isAb.proper
    AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
  ktriv := by
    obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
    exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv

theorem relAmple_of_genericFibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [IsIntegral S] (P : Out.PolAV S) (M : LB P.A.left) (K : Type) [Field K] (x : Sp K ⟶ S), M.IsLB → Set.range x = {genericPoint S} → Out.RelAmple ((Over.pullback x).obj P.A) (M.pull (pullback.fst P.A.hom x)) → Out.RelAmple P.A M := by
  intro hL _ S _ _ P M K _ x hM hx hamp
  have hne : Nonempty (baseChange P x).A.left :=
    ⟨eSec (baseChange P x).A (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := _root_.GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K (baseChange P x).A (baseChange P x).L (M.pull (pullback.fst P.A.hom x))
    (baseChange P x).isAb.proper hne (baseChange P x).isLB (pull_isLB hM _) hamp
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN := LB.isLB_div hp P.isLB
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ P.A.left), (LB.div (lbPow (M.pull f) a) (P.L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB P.isLB f)
  obtain ⟨t, ht⟩ := exists_sec_ne_zero_of_lbIso (pull_isLB hN _) (hN' _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom x) a) ⟨s, hs⟩
  refine _root_.GlobalTheory.FibreAmple.relAmple_of_geometricFibres hL S P M hM fun K' _ _ y => ?_
  obtain ⟨t', ht'⟩ := exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (lbIso_pull_div_lbPow P.isLB hM (pullback.fst P.A.hom y) a).symm
    (_root_.GlobalTheory.GenericSection.exists_sec_ne_zero_of_generic hL S P _ K K' x y t hN hx ht)
  obtain ⟨r, u, hu⟩ := _root_.GlobalTheory.EffectiveCube.exists_sections_cube_cover _root_.GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.1 K' (baseChange P y) _ t' (hN' _) ht'
  exact _root_.GlobalTheory.relAmple_of_cube_div_generated K' (baseChange P y).A (baseChange P y).L (M.pull (pullback.fst P.A.hom y)) a r u
    (baseChange P y).isAb.proper (baseChange P y).isLB (pull_isLB hM _) ha (baseChange P y).ample hu

end GlobalTheory.AmpleSpecialisation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_fullLevel_of_pelThetaFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  first | exact @GlobalTheory.exists_famCore_of_thetaFam | exact GlobalTheory.exists_famCore_of_thetaFam | (intros; apply GlobalTheory.exists_famCore_of_thetaFam <;> assumption)
end

