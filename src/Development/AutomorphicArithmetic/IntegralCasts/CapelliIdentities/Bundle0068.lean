module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import GroundTheory.LocalFields.Uniqueness
public import GroundTheory.LocalFields.Interface

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AffineGenerators
section
open GlobalTheory.CompanionTheory.Ar.Num in
private theorem mem_spanOver_of_mem_span {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (S : Set E) {v : E}
    (hv : v ∈ Submodule.span R S) : v ∈ spanOver R S := by
  obtain ⟨m, a, g, rfl⟩ := Submodule.mem_span_set'.1 hv
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨(a i : Ω), (a i).2, (g i : E), (g i).2, rfl⟩

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem exists_finset_span_of_locFree {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) (N : ℕ) (L : AddSubgroup E)
    (h : LocFree R N L) :
    ∃ T : Finset E, (∀ t ∈ T, t ∈ L) ∧ ∀ e ∈ L, e ∈ Submodule.span R (T : Set E) := by
  classical
  obtain ⟨-, k, f, c, hf, hc, hsum, hb⟩ := h
  choose b _ _ hb using hb
  have hgen : ∀ l q, ∃ m : ℕ, f l ^ m • b l q ∈ L := by
    intro l q
    refine (hb l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq
        simpa using R.one_mem
      · simpa [Pi.single_eq_of_ne hq] using R.zero_mem
    · simp [Pi.single_apply]
  choose m hm using hgen
  refine ⟨Finset.univ.image fun x : Fin k × Fin N => f x.1 ^ m x.1 x.2 • b x.1 x.2, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
    exact hm x.1 x.2
  · intro e he
    let f' : Fin k → R := fun l => ⟨f l, hf l⟩
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range f') ?_ e ?_
    · rw [Ideal.eq_top_iff_one]
      have h1 : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * f' l := by
        apply Subtype.ext
        simpa [f'] using hsum.symm
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
    · rintro ⟨_, l, rfl⟩
      obtain ⟨a, ha, hea⟩ := (hb l e).1 ⟨0, by simpa using he⟩
      choose j hj using ha
      refine ⟨∑ q, (j q + m l q), ?_⟩
      rw [hea, Finset.smul_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      have hle : j q + m l q ≤ ∑ q, (j q + m l q) :=
        Finset.single_le_sum (f := fun q => j q + m l q) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ q)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have heq : (f' l ^ (∑ q, (j q + m l q))) • a q • b l q =
          (f' l ^ d * (⟨f l ^ j q * a q, hj q⟩ : R)) • (f l ^ m l q • b l q) := by
        rw [hd]
        change (f l ^ (j q + m l q + d)) • a q • b l q =
          (f l ^ d * (f l ^ j q * a q)) • (f l ^ m l q • b l q)
        rw [smul_smul, smul_smul]
        congr 1
        ring
      change (f' l ^ (∑ q, (j q + m l q))) • a q • b l q ∈ _
      rw [heq]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(l, q), Finset.mem_univ _, rfl⟩)

open GlobalTheory.CompanionTheory.Ar.Num in
private theorem linMap_injective {Ω : Type} [Field Ω] {F : Type} [Zero F] [One F] (n : ℕ)
    (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : LinearMap.ker (linMap n χ) = ⊥ := by
  classical
  rw [LinearMap.ker_eq_bot']
  intro l hl
  funext i
  have h := congrFun hl (Pi.single i 1)
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [h1] using h
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj, h0]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem UpperTheory.Reformulated.B.AffineGenerators.af_gens :
    ∀ {o Ω : Type} [inst : CommRing o] [inst_1 : Field Ω] [inst_2 : Algebra o Ω] {F : Type} [inst_3 : Zero F]
      [inst_4 : One F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : GlobalTheory.CompanionTheory.Ar.Num.LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
      (p N : ℕ) (χ : F → Ω),
      χ (0 : F) = (0 : Ω) →
        χ (1 : F) = (1 : Ω) →
          GlobalTheory.CompanionTheory.Ar.Num.LocFree R N (D.l1 R p) →
            GlobalTheory.CompanionTheory.Ar.Num.Summand (D.l1 R p) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ).range →
              ∃ (S : Finset (Fin n → Ω)),
                (↑S : Set (Fin n → Ω)) ⊆ (↑(D.af R p χ) : Set (Fin n → Ω)) ∧
                  D.af R p χ ≤ GlobalTheory.CompanionTheory.Ar.Num.spanOver R (↑S : Set (Fin n → Ω)) := by
  intro o Ω _ _ _ F _ _ n Sg r s D R p N χ h0 h1 hfree hsum
  classical
  obtain ⟨T, hT, hspan⟩ := exists_finset_span_of_locFree R N _ hfree
  obtain ⟨ρ, hρU, hρid, hρL⟩ := hsum
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ (linMap_injective n χ h0 h1)
  have hg' : ∀ l, g (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := fun l => LinearMap.congr_fun hg l
  refine ⟨T.image fun t => g (ρ t), ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
    obtain ⟨l, hl⟩ := hρU t
    change GlobalTheory.CompanionTheory.Ar.Num.linMap n χ (g (ρ t)) ∈ D.l1 R p
    rw [← hl, hg', hl]
    exact hρL t (hT t ht)
  · intro l hl
    have hl' : GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l ∈ D.l1 R p := hl
    have hmem := Submodule.apply_mem_span_image_of_mem_span
      ((g ∘ₗ ρ).restrictScalars R) (hspan _ hl')
    apply mem_spanOver_of_mem_span
    rw [Finset.coe_image]
    have heq : ((g ∘ₗ ρ).restrictScalars R) (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l) = l := by
      change g (ρ (GlobalTheory.CompanionTheory.Ar.Num.linMap n χ l)) = l
      rw [hρid _ ⟨l, rfl⟩, hg']
    rw [heq] at hmem
    exact hmem
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraTer
section
open Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Ue16.exists_smul_mem
    {G : Type} [inst : Group G] {LL : Type} [inst_1 : Field LL] {O : Type} [inst_2 : CommRing O]
    [inst_3 : Algebra O LL] [IsDomain O] [IsFractionRing O LL] {V : Type}
    [inst_6 : AddCommGroup V] [inst_7 : Module LL V] [inst_8 : Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (x : V) :
    ∃ a : O, a ≠ 0 ∧ a • x ∈ L.T := by
  have hx : x ∈ Submodule.span LL (L.T : Set V) := by
    rw [L.span]
    exact Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) LL (L.T : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerMore
section
private theorem UpperTheory.Reformulated.B.G5.irr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (P Q : Matrix (Fin m) (Fin m) R)
    (hPQ : P * Q = 1) (H : ∀ g ∈ U, a g = Q * a' g * P)
    (hirr : ∀ S : Submodule R (Fin m → R),
      (∀ g ∈ U, ∀ v ∈ S, (a g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤)
    (S : Submodule R (Fin m → R)) (hS : ∀ g ∈ U, ∀ v ∈ S, (a' g).mulVec v ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have key : ∀ v : Fin m → R, P.mulVec (Q.mulVec v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  have mem : ∀ v : Fin m → R, v ∈ S.comap P.mulVecLin ↔ P.mulVec v ∈ S := fun v => Iff.rfl
  have hst : ∀ g ∈ U, ∀ v ∈ S.comap P.mulVecLin, (a g).mulVec v ∈ S.comap P.mulVecLin := by
    intro g hg v hv
    rw [mem] at hv ⊢
    rw [H g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, key]
    exact hS g hg _ hv
  rcases hirr _ hst with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [mem, key]; exact hv
    rw [h0, Submodule.mem_bot] at h2
    rw [Submodule.mem_bot, ← key v, h2, Matrix.mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : Q.mulVec v ∈ S.comap P.mulVecLin := by rw [h1]; exact Submodule.mem_top
    rwa [mem, key] at h2

theorem UpperTheory.Reformulated.B.G5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ}
    {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R),
    (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
      UpperTheory.V.U3.MatIrr U a → UpperTheory.V.U3.MatIrr U a' := by
  intro G R _ _ m U a a' h H hirr
  exact UpperTheory.Reformulated.B.G5.irr_conj _ _ (Units.mul_inv h) H hirr
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinpolyProductMap
section
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

private theorem UpperTheory.Reformulated.B.MinpolyProductMap.field_case {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (y : L)
    (hy : Function.Injective fun σ : Gal(L/K) => σ y) :
    (minpoly K y).map (algebraMap K L) = ∏ σ : Gal(L/K), (Polynomial.X - Polynomial.C (σ y)) := by
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_of_monic _ _ fun σ _ => Polynomial.monic_X_sub_C _)
    ((minpoly.monic hint).map _) ?_ ?_
  · refine Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hy) fun σ => ?_
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap,
      Polynomial.aeval_algHom_apply σ, minpoly.aeval, map_zero]
  · rw [Polynomial.natDegree_map, Polynomial.natDegree_prod_of_monic _ _
      (fun σ _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one]
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact minpoly.natDegree_le y

theorem UpperTheory.Reformulated.B.MinpolyProductMap.map_minpoly_eq_prod.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K]
      [inst_3 : IsNonarchimedeanLocalField K] [inst_4 : Field L] [inst_5 : ValuativeRel L] [inst_6 : TopologicalSpace L]
      [inst_7 : IsNonarchimedeanLocalField L] [inst_8 : Algebra K L] [inst_9 : ValuativeExtension K L]
      [inst_10 : FiniteDimensional K L] [IsGalois K L] {x : ↥(ValuativeRel.valuation L).integer},
      (↥(ValuativeRel.valuation K).integer)[x] = ⊤ →
        Polynomial.map (Algebra.algebraMap ↥(ValuativeRel.valuation K).integer ↥(ValuativeRel.valuation L).integer)
            (minpoly (↥(ValuativeRel.valuation K).integer) x) =
          ∏ σ : Gal(L/K),
            (Polynomial.X -
              (Polynomial.C : ↥(ValuativeRel.valuation L).integer → Polynomial ↥(ValuativeRel.valuation L).integer)
                (((GroundTheory.LocalField.integerAlgEquiv K L :
                               Gal(L/K) →
                                 ↥(ValuativeRel.valuation L).integer ≃ₐ[↥(ValuativeRel.valuation K).integer]
                                   ↥(ValuativeRel.valuation L).integer)
                      σ :
                    ↥(ValuativeRel.valuation L).integer → ↥(ValuativeRel.valuation L).integer)
                  x)) := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ x hx
  have hinj : Function.Injective fun σ : Gal(L/K) => σ (x : L) := by
    intro σ τ h
    have h1 : ∀ z : (ValuativeRel.valuation L).integer, σ (z : L) = τ (z : L) := by
      have h2 : (GroundTheory.LocalField.integerAlgEquiv K L σ).toAlgHom =
          (GroundTheory.LocalField.integerAlgEquiv K L τ).toAlgHom := by
        refine AlgHom.ext_of_adjoin_eq_top hx ?_
        rintro _ rfl
        exact Subtype.ext h
      intro z
      exact congrArg Subtype.val (DFunLike.congr_fun h2 z)
    ext y
    rcases le_total (ValuativeRel.valuation L y) 1 with hy | hy
    · exact h1 ⟨y, hy⟩
    · have hy' : ValuativeRel.valuation L y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hy
      have h3 : σ y⁻¹ = τ y⁻¹ := h1 ⟨y⁻¹, hy'⟩
      rwa [map_inv₀, map_inv₀, inv_inj] at h3
  have hfield := UpperTheory.Reformulated.B.MinpolyProductMap.field_case (K := K) (x : L) hinj
  have hprod : (∏ σ : Gal(L/K), (Polynomial.X -
      Polynomial.C (GroundTheory.LocalField.integerAlgEquiv K L σ x))).map
        (algebraMap (ValuativeRel.valuation L).integer L) =
      (minpoly K (x : L)).map (algebraMap K L) := by
    rw [hfield, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun σ _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hlift : minpoly K (x : L) ∈
      Polynomial.lifts (algebraMap (ValuativeRel.valuation K).integer K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h4 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) hprod
    simp only [Polynomial.coeff_map] at h4
    have h5 : algebraMap K L ((minpoly K (x : L)).coeff n) ∈ (ValuativeRel.valuation L).integer := by
      rw [← h4]
      exact Subtype.property _
    exact ⟨⟨_, (GroundTheory.LocalField.algebraMap_mem_integer_iff K L _).mp h5⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    (minpoly.monic (Algebra.IsIntegral.isIntegral (x : L)))
  have hcomp : (algebraMap (ValuativeRel.valuation L).integer L).comp
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer) =
      (algebraMap K L).comp (algebraMap (ValuativeRel.valuation K).integer K) := by
    ext z
    exact GroundTheory.LocalField.coe_algebraMap_integer K L z
  have hxint : IsIntegral (ValuativeRel.valuation K).integer x := by
    refine ⟨q, hqm, ?_⟩
    apply Subtype.val_injective
    have h6 := Polynomial.hom_eval₂ q
      (algebraMap (ValuativeRel.valuation K).integer (ValuativeRel.valuation L).integer)
      (algebraMap (ValuativeRel.valuation L).integer L) x
    rw [hcomp, ← Polynomial.eval₂_map, hq] at h6
    exact h6.trans (minpoly.aeval K (x : L))
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions K L hxint
  apply Polynomial.map_injective (algebraMap (ValuativeRel.valuation L).integer L)
    Subtype.val_injective
  rw [hprod, Polynomial.map_map, hcomp, ← Polynomial.map_map, ← hmin]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMul
section
open TensorProduct Formalism.WeaklyAdmissibleFiltrations in
theorem UpperTheory.Reformulated.B.Qf14.phi_mul
    {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {E : Type} [Field E] [Algebra Qp E]
    (x y : E ⊗[Qp] B) :
    φVB PD (LL := E) (V := E) (x * y) =
      φVB PD (LL := E) (V := E) x * φVB PD (LL := E) (V := E) y := by
  have h : ∀ z : E ⊗[Qp] B,
      φVB PD (LL := E) (V := E) z = Algebra.TensorProduct.map (AlgHom.id E E) PD.φ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  exact (h (x * y)).trans ((map_mul _ x y).trans (congrArg₂ (· * ·) (h x).symm (h y).symm))
end

