module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoAgreesOnCompletePoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

noncomputable section
namespace GlobalTheory.Poinc.FieldConj
open GlobalTheory.Points _root_.GlobalTheory.ZH.RatModel
open scoped Pointwise

theorem eq_of_val_eq_fibre {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {X : Scheme.{0}}
    (q : M.Z ⟶ X) [IsAffineHom q] {K : Type} [Field K] (y y' : Sp K ⟶ M.Z) (hyy : y ≫ q = y' ≫ q)
    (h : ∀ b ∈ M.ringOn {z | q z = (y ≫ q) (IsLocalRing.closedPoint K)}, M.val y b = M.val y' b) : y = y' := by
  set x := (y ≫ q) (IsLocalRing.closedPoint K) with hx
  have hxz : q (y (IsLocalRing.closedPoint K)) = x := rfl
  have hxz' : q (y' (IsLocalRing.closedPoint K)) = x := by rw [hx, hyy]; rfl
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  have hU : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have hsub : ∀ a ∈ M.ringOn (q ⁻¹ᵁ V : Set M.Z), a ∈ M.ringOn {z | q z = x} := by
    have hsubset : {z : M.Z | q z = x} ⊆ (q ⁻¹ᵁ V : Set M.Z) := by
      intro z hz
      change q z ∈ V
      rw [hz]
      exact hxV
    exact fun a ha => M.ringOn_anti hsubset ha
  have hzU : y (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz]; exact hxV
  have hzU' : y' (IsLocalRing.closedPoint K) ∈ q ⁻¹ᵁ V := show q _ ∈ V by rw [hxz']; exact hxV
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)

  have hinv : ∀ {w : Sp K ⟶ M.Z} (hw : Set.range w = {w (IsLocalRing.closedPoint K)}) {a : Ω},
      a ∈ M.O (w (IsLocalRing.closedPoint K)) → a ≠ 0 → (a⁻¹ ∈ M.O (w (IsLocalRing.closedPoint K)) ↔ M.val w a ≠ 0) := by
    intro w hw a ha h0
    rw [val_ne_zero_iff hw ⟨a, ha⟩, isUnit_O_iff]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  have hpt : y (IsLocalRing.closedPoint K) = y' (IsLocalRing.closedPoint K) := by
    refine GlobalTheory.Points.point_eq_of_inv_mem_iff o Ω M _ hU _ _ hzU hzU' fun a ha h0 => ?_
    rw [hinv hr (M.ringOn_le_O hzU ha) h0, hinv hr' (M.ringOn_le_O hzU' ha) h0, h a (hsub a ha)]
  set z := y (IsLocalRing.closedPoint K) with hz
  have hO : ∀ a ∈ M.O z, M.val y a = M.val y' a := by
    intro a ha
    obtain ⟨c, hc, d, hd, hd0, hdi, rfl⟩ :=
      GlobalTheory.Poinc.exists_eq_div_of_mem_O_affine o Ω M _ hU z hzU a ha
    have hsp : ∀ w, y w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
    have hsp' : ∀ w, y' w ⤳ z := fun w => by rw [Subsingleton.elim w (IsLocalRing.closedPoint K), hpt]
    have hcz := M.ringOn_le_O hzU hc
    have hdz := M.ringOn_le_O hzU hd
    have hq : c / d ∈ M.O z := ha
    have e1 := val_mul hsp hq hdz
    have e1' := val_mul hsp' hq hdz
    rw [div_mul_cancel₀ c hd0] at e1 e1'
    have hne : M.val y d ≠ 0 := (hinv hr hdz hd0).1 hdi
    have hne' : M.val y' d ≠ 0 := by rw [← h d (hsub d hd)]; exact hne
    rw [eq_div_of_mul_eq hne e1.symm, eq_div_of_mul_eq hne' e1'.symm, h c (hsub c hc), h d (hsub d hd)]
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local hpt fun W h₁ h₂ => ?_
  have hW : z ∈ W := h₁ (x := IsLocalRing.closedPoint K) trivial
  ext f
  have e1 := val_valF ((top_le_preimage_iff y W).1 h₁) f
  have e2 := val_valF ((top_le_preimage_iff y' W).1 h₂) f
  have e3 := hO _ (valF_mem_O hW f)
  rw [e1, e2] at e3
  unfold valF at e3
  rw [dite_eq_left h₁, dite_eq_left h₂] at e3
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective e3

theorem galConj : ∀ (A F L K : Type) [CommRing A] [IsDomain A] [Field F] [Field L] [Field K] [CharZero K] [Algebra A F] [IsFractionRing A F] [IsIntegrallyClosed A] [Algebra F L] [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] [IsGalois F L] (B : Subring L), (∀ b : L, b ∈ B ↔ IsIntegral A b) → ∀ e e' : B →+* K, (∀ b : B, (∃ a : A, algebraMap A L a = b) → e b = e' b) → ∃ σ : L ≃ₐ[F] L, ∀ b c : B, (c : L) = σ b → e' b = e c := by
  intro A F L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ B hB e e' hA
  classical
  have hσB : ∀ (σ : L ≃ₐ[F] L) (b : L), b ∈ B → σ b ∈ B := fun σ b hb =>
    (hB _).2 (IsIntegral.map ((σ : L →ₐ[F] L).restrictScalars A) ((hB b).1 hb))
  let σB : (L ≃ₐ[F] L) → B →+* B := fun σ =>
    ((σ : L →+* L).comp B.subtype).codRestrict B fun b => hσB σ b b.2
  have hσB_apply : ∀ σ (b : B), ((σB σ b : B) : L) = σ b := fun _ _ => rfl

  have claim : ∀ b : B, ∃ σ : L ≃ₐ[F] L, e' b = e (σB σ b) := by
    intro b
    let P : Polynomial B := ∏ σ : L ≃ₐ[F] L, (Polynomial.X - Polynomial.C (σB σ b))
    have hPmap : ∀ τ : L ≃ₐ[F] L, (P.map B.subtype).map (τ : L →+* L) = P.map B.subtype := by
      intro τ
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
      rfl
    have hcoeff : ∀ n, ∃ a : A, algebraMap A L a = (P.coeff n : L) := by
      intro n
      have hfix : ∀ τ : L ≃ₐ[F] L, τ (P.coeff n : L) = P.coeff n := by
        intro τ
        have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) (hPmap τ)
        simpa [Polynomial.coeff_map] using this
      obtain ⟨f, hf⟩ := (IsGalois.mem_bot_iff_fixed (P.coeff n : L)).2 hfix
      change algebraMap F L f = _ at hf
      have hint : IsIntegral A (algebraMap F L f) := by rw [hf]; exact (hB _).1 (P.coeff n).2
      have hint' : IsIntegral A f := by
        rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A F L) (algebraMap F L).injective]
        exact hint
      obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
      exact ⟨a, by rw [IsScalarTower.algebraMap_apply A F L, ha, hf]⟩
    have hmap : P.map e = P.map e' := by
      ext n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      obtain ⟨a, ha⟩ := hcoeff n
      exact hA _ ⟨a, ha⟩
    have h0 : (P.map e').eval (e' b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_univ 1) (by rw [sub_eq_zero]; exact Subtype.ext rfl), map_zero]
    rw [← hmap] at h0
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h0
    obtain ⟨σ, -, hσ⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨σ, sub_eq_zero.1 hσ⟩
  let H : (L ≃ₐ[F] L) → AddSubgroup B := fun σ =>
    (e'.toAddMonoidHom - (e.comp (σB σ)).toAddMonoidHom).ker
  have hmemH : ∀ σ (b : B), b ∈ H σ ↔ e' b = e (σB σ b) := fun σ b => by
    simp [H, AddMonoidHom.mem_ker, sub_eq_zero]
  have hcover : ⋃ σ ∈ (Finset.univ : Finset (L ≃ₐ[F] L)), (0 : B) +ᵥ ((H σ : AddSubgroup B) : Set B) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => ?_
    obtain ⟨σ, hσ⟩ := claim b
    refine Set.mem_iUnion₂.2 ⟨σ, Finset.mem_univ _, ?_⟩
    rw [zero_vadd]
    exact (hmemH σ b).2 hσ
  obtain ⟨σ, -, hfin⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcover
  refine ⟨σ, fun b c hc => ?_⟩
  have hcσ : c = σB σ b := Subtype.ext hc
  subst hcσ
  have hn : (H σ).index ≠ 0 := hfin.index_ne_zero
  have hmem := (hmemH σ _).1 (AddSubgroup.nsmul_index_mem (H σ) b)
  rw [map_nsmul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at hmem
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hn) hmem

theorem val_algebraMap_of_comp {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
    [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] {M₁ : RatModel o₁ Ω₁} {M₂ : RatModel o₂ Ω₂} {q : M₂.Z ⟶ M₁.Z}
    (hg : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt) {K : Type} [Field K] (y : Sp K ⟶ M₂.Z) {x : Ω₁}
    (hx : x ∈ M₁.O ((y ≫ q) (IsLocalRing.closedPoint K))) :
    M₂.val y (algebraMap Ω₁ Ω₂ x) = M₁.val (y ≫ q) x := by
  obtain ⟨U, f, hzU, rfl⟩ := hx
  have h1 : Set.range (y ≫ q) ⊆ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  have h2 : Set.range y ⊆ q ⁻¹ᵁ U := by
    rw [range_eq_singleton _ (IsLocalRing.closedPoint K)]; exact Set.singleton_subset_iff.2 hzU
  rw [← GlobalTheory.Poinc.FinPts.valF_app hg ⟨_, hzU⟩ f, val_valF h2, val_valF h1]
  exact (valR_comp y q U f).symm

theorem exists_aut_eq_of_comp_eq : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ _ _ M₁ M₂ q hN₁ hN₂ hF hg K _ _ y y' hyy
  set z₁ := (y ≫ q) (IsLocalRing.closedPoint K) with hz₁
  haveI : IsIntegrallyClosed (M₁.O z₁) := isIntegrallyClosed_O hN₁ z₁
  let B : Subring Ω₂ := (M₂.ringOn {z | q z = z₁}).toSubring
  have hB : ∀ b : Ω₂, b ∈ B ↔ IsIntegral (M₁.O z₁) b := by
    intro b
    letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
    have h1 := (GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg z₁).1 b
    have h2 : IsIntegral (M₁.Z.presheaf.stalk z₁) b ↔ IsIntegral (M₁.O z₁) b := by
      constructor
      · intro hb
        exact IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).toRingHom (RingHom.id Ω₂) (RingHom.ext fun _ => rfl) hb
      · intro hb
        refine IsIntegral.map_of_comp_eq (M₁.stalkEquiv z₁).symm.toRingHom (RingHom.id Ω₂) (RingHom.ext fun x => ?_) hb
        show algebraMap Ω₁ Ω₂ (M₁.stalkHom z₁ ((M₁.stalkEquiv z₁).symm x)) = algebraMap Ω₁ Ω₂ (x : Ω₁)
        rw [← coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [← h2, ← mem_integralClosure_iff, h1, Subalgebra.mem_toSubring, mem_ringOn]
    rfl
  have hr := range_eq_singleton y (IsLocalRing.closedPoint K)
  have hr' := range_eq_singleton y' (IsLocalRing.closedPoint K)
  have hz : q (y (IsLocalRing.closedPoint K)) = z₁ := rfl
  have hz' : q (y' (IsLocalRing.closedPoint K)) = z₁ := by rw [hz₁, hyy]; rfl
  let e : B →+* K := (M₂.valHom y _ hr).comp
    (Subring.inclusion (show B ≤ (M₂.O (y (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz))
  let e' : B →+* K := (M₂.valHom y' _ hr').comp
    (Subring.inclusion (show B ≤ (M₂.O (y' (IsLocalRing.closedPoint K))).toSubring from
      fun b hb => mem_ringOn.1 hb _ hz'))
  have he : ∀ b : B, e b = M₂.val y b := fun _ => rfl
  have he' : ∀ b : B, e' b = M₂.val y' b := fun _ => rfl
  have hA : ∀ b : B, (∃ a : M₁.O z₁, algebraMap (M₁.O z₁) Ω₂ a = b) → e b = e' b := by
    rintro b ⟨a, hab⟩
    rw [he, he', ← hab]
    show M₂.val y (algebraMap Ω₁ Ω₂ a) = M₂.val y' (algebraMap Ω₁ Ω₂ a)
    rw [val_algebraMap_of_comp hg y a.2, val_algebraMap_of_comp hg y' (by rw [← hyy]; exact a.2), hyy]
  obtain ⟨σ, hσ⟩ := galConj (M₁.O z₁) Ω₁ Ω₂ K B hB e e' hA
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.Poinc.GalAut.autAct o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN₂ hF hg σ
  haveI := hF
  have key : y ≫ s = y' := by
    refine eq_of_val_eq_fibre M₂ q (y ≫ s) y' (by rw [Category.assoc, hs2, hyy]) fun b hb => ?_
    have hys : (y ≫ s) ≫ q = y ≫ q := by rw [Category.assoc, hs2]
    rw [hys] at hb
    have hbB : b ∈ B := hb
    have hσB : σ b ∈ B := (hB _).2
      (IsIntegral.map ((σ : Ω₂ →ₐ[Ω₁] Ω₂).restrictScalars (M₁.O z₁)) ((hB b).1 hbB))
    rw [hs3]
    exact (hσ ⟨b, hbB⟩ ⟨σ b, hσB⟩ rfl).symm
  refine ⟨σ, s, hs1, key, fun b => ?_⟩
  rw [← key]
  exact hs3 K y b

end GlobalTheory.Poinc.FieldConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorNearFibresOfFiniteFlat
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_gen_near_of_finFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp hY hbij L hL hloc x
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨hkf, hqc, hqs, hsurj, hcl, hclp, hO, d, b, hb⟩ :=
    _root_.GlobalTheory.finiteFlat_proper_baseChange_facts R R' ρ hfin.2.1 hfin.2.2 hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  obtain ⟨V, hV, y₀, hy₀, hxy, hE⟩ := _root_.GlobalTheory.ClosedPt.exists_closed_point Y x
  obtain ⟨hclV, -⟩ := hE V le_rfl hV hy₀
  have hL' : (L.pull k').IsLB := LB.isLB_pull hL _
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.Mum.exists_sec_nonzero_on_fibre Y Y' Z' k hkf p' hqc hqs V hV y₀ hy₀ hclV (L.pull k') hL' (fun x' _ => hloc x')
  obtain ⟨V₁, hy₁, hV₁V, hV₁⟩ := _root_.GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap Z' Y (p' ≫ k) hcl (L.pull k') V s y₀ hy₀ hs
  obtain ⟨f, hf1, hf2⟩ := hV.exists_basicOpen_le ⟨y₀, hy₁⟩ hy₀
  have hV₂V : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have hV₂ : IsAffineOpen (Y.basicOpen f) := hV.basicOpen f
  obtain ⟨-, M, hM, hMiff⟩ := hE (Y.basicOpen f) hV₂V hV₂ hf2
  have hcomm : ∀ z : Z', p (k' z) = k (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk'.w]
  have hle : k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) ≤ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := fun z hz => by
    show k (p' z) ∈ V
    rw [← hcomm]
    exact hV₂V hz
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.GenRestrict.exists_gen_restrict Z' (L.pull k') hL' _ _ hle s (fun z₀ hz₀ => hV₁ z₀ (by
    rw [Scheme.Hom.comp_apply, ← hcomm]
    exact hf1 hz₀))
  have hsurjp : Function.Surjective (p.app (Y.basicOpen f)).hom := (hbij _).2
  let e := RingEquiv.ofBijective (p.app (Y.basicOpen f)).hom (hbij _)
  haveI hm : (Ideal.comap e.symm.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨hOc, hOq⟩ := hO _ hV₂
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.FlatGenDescent.exists_sec_of_free R R' ρ d b hb Z Z' k' (p ≫ y) (p' ≫ y') (hk'.paste_vert hk) (p ⁻¹ᵁ Y.basicOpen f) hOc hOq
    L hL σ hσ _ hm
  have hfib : ∀ z₀ : (p ⁻¹ᵁ Y.basicOpen f).toScheme, p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) = y₀ → z₀ ∈ nonzeroLocus u := by
    intro z₀ hz₀
    obtain ⟨z', hz'⟩ := hsurj ((p ⁻¹ᵁ Y.basicOpen f).ι z₀)
    have hz'O : z' ∈ k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) := by
      show k' z' ∈ p ⁻¹ᵁ Y.basicOpen f
      rw [hz']
      first | exact z₀.2 | simpa using z₀.2 | exact (Scheme.Opens.range_ι _).subset ⟨z₀, rfl⟩
    obtain ⟨w, hw⟩ : z' ∈ Set.range (k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hz'O
    refine hu w (fun a ha => ?_) z₀ (by rw [← hz']; exact congrArg k'.base hw |>.symm)
    have ha₀ : e.symm a ∈ M := ha
    have ea : a = p.app (Y.basicOpen f) (e.symm a) := (e.apply_symm_apply a).symm
    intro hmem
    rw [ea, ← Scheme.preimage_basicOpen] at hmem
    have : k' ((k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι w) = (p ⁻¹ᵁ Y.basicOpen f).ι z₀ := by
      rw [← hz']; exact congrArg k'.base hw
    rw [this] at hmem
    have hmem' : p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) ∈ Y.basicOpen (e.symm a) := hmem
    rw [hz₀] at hmem'
    exact (hMiff _).1 ha₀ hmem'
  obtain ⟨V₃, hy₃, hV₃, hV₃u⟩ := _root_.GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap Z Y p hclp L _ u y₀ hf2 hfib
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.GenRestrict.exists_gen_restrict Z L hL (p ⁻¹ᵁ V₃) (p ⁻¹ᵁ Y.basicOpen f) (fun z hz => hV₃ hz) u
    (fun z hz => hV₃u z hz)
  exact ⟨V₃, hxy.mem_open V₃.isOpen hy₃, t, ht⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportMumfordBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GenTransport

section Nest

variable {X X' Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (X' ⟶ X)} {ε : K → ℤ} {p : Y ⟶ X'}

theorem trF_nest (r : Z ⟶ Y) (z : Z) (j j' : PUnit.{1} → K → L.ι)
    (hj : (r ≫ p) z ∈ LB.wchart L φ (j PUnit.unit)) (hj' : (r ≫ p) z ∈ LB.wchart L φ (j' PUnit.unit)) :
    trF (L := LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1) r z j j' =
      trF (fun k => p ≫ φ k) (fun k => - ε k) r z (j PUnit.unit) (j' PUnit.unit) := by
  unfold trF
  refine (Fintype.prod_unique _).trans ?_
  refine (zpow_neg_one _).trans ?_
  refine (congrArg (·⁻¹) (gm_linComb L φ ε (r ≫ p) z _ _ hj hj')).trans ?_
  simp only [← Finset.prod_inv_distrib, zpow_neg, Category.assoc]

theorem mem_nest {y : Y} {j : PUnit.{1} → K → L.ι} :
    y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) j ↔
      y ∈ LB.wchart L (fun k => p ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 h PUnit.unit) k,
    fun h => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k⟩

theorem exists_nest (t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k))) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) =
          gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) := by
  refine ⟨⟨fun j => res (fun _ hy => mem_nest.1 hy) (t.s (j PUnit.unit))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ (mem_nest.2 hj) _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ht (𝟙 Y) y (mem_nest.1 hj) (mem_nest.1 hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y j j' (Set.mem_iInter.1 hj PUnit.unit)
      (Set.mem_iInter.1 hj' PUnit.unit)).symm (gm_res _ y _ hj' _).symm))

theorem exists_unnest (a : LB.Gen (LB.LinComb (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => -1)))
    (ha : a.IsGen) : ∃ t : LB.Gen (LB.LinComb L (fun k => p ≫ φ k) (fun k => - ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => p ≫ φ k) j →
        gm r z (LB.wchart L (fun k => p ≫ φ k) j) (t.s j) =
          gm r z (LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j)) (a.s fun _ => j) := by
  have mk : ∀ {y : Y} {j : K → L.ι}, y ∈ LB.wchart L (fun k => p ≫ φ k) j →
      y ∈ LB.wchart (LB.LinComb L φ ε) (fun _ : PUnit.{1} => p) (fun _ => j) := fun h => mem_nest.2 h
  refine ⟨⟨fun j => res (fun _ hy => mk hy) (a.s fun _ => j)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z j hj => gm_res r z _ hj _⟩
  refine (gm_res _ y _ hj _).trans ((gen_trans ha (𝟙 Y) y (mk hj) (mk hj')).trans
    (congrArg₂ (· * ·) (trF_nest (𝟙 Y) y (fun _ => j) (fun _ => j') (Set.mem_iInter.1 (mk hj) PUnit.unit)
      (Set.mem_iInter.1 (mk hj') PUnit.unit)) (gm_res _ y _ hj' _).symm))

end Nest


open GlobalTheory.PrimCocycle in
theorem prod_neg_lam {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B)
    {U : Type} [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ I, k ((lift x y).left ≫ lamφ B I) ^ (- lamε I) = ∏ i, k (lamPts x y i) ^ negε i := by
  have a := prod_lam x y (fun q => (k q)⁻¹)
  have b := Wit.prod_neg_lamPts x y (fun q => (k q)⁻¹)
  simp only [inv_inv, Category.id_comp] at a b
  rw [b, ← a]
  simp only [zpow_neg, inv_zpow]


open GlobalTheory.PrimCocycle in
theorem gen_transport : ∀ (SB SC : Scheme.{0}) (B : Over SB) [GrpObj B] [IsCommMonObj B] (C : Over SC) [GrpObj C] [IsCommMonObj C] (M : LB B.left) (N : LB C.left), M.IsLB → N.IsLB → ∀ (m : (G2 B).left ⟶ (G2 C).left) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen → ∀ (T : Over SB) (T₀ : Over SC) (x y : T ⟶ B) (x₀ y₀ : T₀ ⟶ C) (h : T.left ⟶ T₀.left), (lift x y).left ≫ m = h ≫ (lift x₀ y₀).left → ∀ t₀ : LB.Gen (LB.LinComb N (lamPts x₀ y₀) negε), t₀.IsGen → ∃ u : LB.Gen (LB.LinComb M (lamPts x y) negε), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J', Good N z J → Good M z J' → val u r z J' = lamVal w (r ≫ (lift x y).left) z J J' * val t₀ (r ≫ h) z J := by
  intro SB SC B _ _ C _ _ M N hM hN m w hw T T₀ x y x₀ y₀ h hm t₀ ht₀
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  obtain ⟨t₁, h₁, v₁⟩ := exists_gen hN (φ' := fun I => (lift x₀ y₀).left ≫ lamφ C I) (ε' := fun I => - lamε I)
    (fun U _ k => (prod_neg_lam x₀ y₀ k).symm) t₀ ht₀
  obtain ⟨t₂, h₂, v₂⟩ := exists_nest t₁ h₁
  obtain ⟨t₃, h₃, v₃⟩ := DegPull.exists_pmaps (L := abelian₂ C N) (L' := abelian₂ B M) ((isGen_iff w).1 hw) lN lM
    (φ' := fun _ : PUnit.{1} => (lift x y).left) h (fun _ => hm) t₂ h₂
  obtain ⟨t₄, h₄, v₄⟩ := exists_unnest (L := M) (φ := lamφ B) (ε := lamε) t₃ h₃
  obtain ⟨u, hu, vu⟩ := exists_gen hM (fun U _ k => prod_neg_lam x y k) t₄ h₄
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => ?_⟩
  have e : ∀ I, (r ≫ h) ≫ (lift x₀ y₀).left ≫ lamφ C I = (r ≫ (lift x y).left) ≫ m ≫ lamφ C I := fun I => by
    rw [Category.assoc, Category.assoc, ← Category.assoc h, ← hm, Category.assoc]
  have E := v₃ Z r z (fun _ I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (fun _ => Set.mem_iInter.2 fun I => hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I))
    (fun _ => Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [Fintype.prod_unique, zpow_neg_one] at E
  have a := v₂ Z (r ≫ h) z (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (Set.mem_iInter.2 fun I => by
    have := hJ ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)
    have e' := congrArg (fun q : Z ⟶ C.left => q z) (e I)
    exact (congrArg (· ∈ N.U _) e').mpr this)
  have b := v₄ Z r z (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ' ((r ≫ (lift x y).left) ≫ lamφ B I))
  rw [vu Z r z J' hJ', ← v₁ Z (r ≫ h) z J hJ,
    val_of t₄ r z J' (fun I => J' ((r ≫ (lift x y).left) ≫ lamφ B I)) (fun I => by rw [Category.assoc]),
    val_of t₁ (r ≫ h) z J (fun I => J ((r ≫ (lift x y).left) ≫ m ≫ lamφ C I)) (fun I => by rw [e]), b, ← a]
  exact (mul_inv_cancel_left _ _).symm.trans (congrArg (_ * ·) E.symm)

end GlobalTheory.GenTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolyLocalInvariantNonposChar0Statement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → ∀ e k : ℕ, 0 < e → GlobalTheory.FactorDepth.nuLocOf C e k (MvPolynomial.map io P₁) ≤ 0 := by
  first | exact @GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | exact GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos | (intros; apply GlobalTheory.ResZeroDepth.exists_harmA_nuLocOf_nonpos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSectionsUniformisedGroupPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

theorem sections_move_integral : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) {k m : ℕ}, 1 ≤ k → ∀ (b : Fin (m + 1) → H0 A.L k), ∃ (σ : Fin (m + 1) → H0 U.LG.L k) (c : Fin (m + 1) → (FractionRing R)ˣ), ∀ (y : ↥(pullback G.hom (jK R))) (j : Fin 1 → U.LG.L.ι) (jA : Fin 1 → A.L.ι), pullback.fst G.hom (jK R) y ∈ U.LG.L.U (j 0) → U.gen.hom.left y ∈ A.L.U (jA 0) → ∃ u : ((pullback G.hom (jK R)).presheaf.stalk y)ˣ, ∀ i, secGerm (pullback.fst G.hom (jK R)) y (σ i) j = u.val * gs (pullback.snd G.hom (jK R)) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (c i : FractionRing R)) * secGerm (show pullback G.hom (jK R) ⟶ A.A.left from U.gen.hom.left) y (b i) jA := by
  intro R _ _ I D A G _ _ U k m hk b
  obtain ⟨w, hw⟩ := U.ext
  obtain ⟨w', hw', -⟩ := GlobalTheory.Algebraise.exists_swap _ _ w hw (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _)
  choose s hs using fun i => GlobalTheory.Algebraise.exists_down A.isLB U.LG.isLB U.gen.hom.left
    (pullback.fst G.hom (jK R)) w' hw' (b i)
  choose c' σ hc' hσ using fun i => GlobalTheory.FormalGeneric.exists_integral U hk (s i)
  refine ⟨σ, fun i => Units.mk0 (algebraMap R (FractionRing R) (c' i))
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hc' i)), fun y j jA hj hjA => ?_⟩
  refine ⟨(gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k)⁻¹, fun i => ?_⟩
  have e₁ := hs i _ (𝟙 _) y (jA 0) (j 0) hjA hj
  have e₂ := hσ i _ (𝟙 _) y (j 0) hj
  have hc : cst (pullback.snd G.hom (jK R) ≫ jK R) y (c' i) = gs (pullback.snd G.hom (jK R)) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom (algebraMap R (FractionRing R) (c' i))) :=
    (gs_pull _ (jK R) y ⊤ trivial _).symm.trans
      (congrArg (gs _ y ⊤) (GlobalTheory.FormalGeneric.appTop_spec (algebraMap R (FractionRing R)) (c' i)))
  rw [Category.id_comp] at e₁ e₂
  rw [Category.id_comp, hc] at e₂
  rw [GlobalTheory.Algebraise.fin_one_const j, GlobalTheory.Algebraise.fin_one_const jA]
  change GlobalTheory.SectionRingIso.vl (σ i) _ y _ = _ * _ * GlobalTheory.SectionRingIso.vl (b i) _ y _
  rw [e₂, e₁, Units.val_mk0, ← Units.val_pow_eq_pow_val]
  generalize gw w' (𝟙 _) y (jA 0) (fun _ => j 0) ^ k = v
  rw [_root_.mul_assoc, mul_left_comm _ v.val, Units.inv_mul_cancel_left]
  rfl

end GlobalTheory.Mum
end
end

