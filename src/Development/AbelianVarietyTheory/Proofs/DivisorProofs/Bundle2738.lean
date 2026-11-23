module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLiftStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Hodge := by
  first | exact @GlobalTheory.AbelianHodge.abelianDeRham_hodge | exact GlobalTheory.AbelianHodge.abelianDeRham_hodge | (intros; apply GlobalTheory.AbelianHodge.abelianDeRham_hodge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeNoPrimitiveO2
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.NoPrimNoeth

theorem injective_of_algClosure (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (N : Type) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], Function.Injective (f.baseChange K)) :
    Function.Injective f := by
  obtain ⟨g, hg⟩ : ∃ g : N →ₗ[R] M, g ∘ₗ f = LinearMap.id := by
    refine GlobalTheory.split_injective_of_forall_lTensor_residueField_injective f fun m hm => ?_
    let k := AlgebraicClosure m.ResidueField
    have hinj := h k
    have e : (AlgebraTensorModule.cancelBaseChange R m.ResidueField m.ResidueField k N) ∘
          ((f.baseChange m.ResidueField).lTensor k) =
        (f.lTensor k) ∘ (AlgebraTensorModule.cancelBaseChange R
          m.ResidueField m.ResidueField k M) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        m.ResidueField m.ResidueField (M := k) f) x).symm
    have h1 : Function.Injective ((f.baseChange m.ResidueField).lTensor k) :=
      Function.Injective.of_comp (e ▸ (hinj.comp (LinearEquiv.injective _)))
    haveI : Module.FaithfullyFlat m.ResidueField k :=
      (fun (F L : Type) [Field F] [Field L] [Algebra F L] ↦ (inferInstance : Module.FaithfullyFlat F L)) _ _
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective m.ResidueField k _).1 h1
  exact Function.LeftInverse.injective (g := g) fun x ↦ LinearMap.congr_fun hg x

theorem abelian_scheme_second_cohomology_finite_projective (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    (Module.Finite R (HO2 A.hom) ∧ Module.Projective R (HO2 A.hom)) ∧ StructureSheafH2BaseChange A.hom := by
  have hsm : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have H := _root_.GlobalTheory.AbCoh.CohBaseChange.main R A.left A.hom hA.proper inferInstance (_root_.GlobalTheory.AbCoh.uConst_of_isAbelianScheme R A hA) (by
    intro R' _ _ _ _ k _ _ α hα X' s' φ X₀ s₀ ψ hp w
    obtain ⟨_, -, h1, h2⟩ := _root_.GlobalTheory.AbCoh.exists_grpObj_isGrpPullback_of_isPullback R R' (algebraMap R R') A X' s' φ hp
    exact _root_.GlobalTheory.AbCoh.artinian_pullHO_surjective R' (Over.mk s' : Over (Sp R')) g (h1 hA) (h2 g hg) k (α : R' →+* k) hα X₀ s₀ ψ w)
  exact ⟨H.2.1, H.2.2.2⟩

theorem pull_comm {R K : Type} [CommRing R] [CommRing K] {σ : R →+* K} {A A' : Over (Sp R)} {B B' : Over (Sp K)}
    {pr : B.left ⟶ A.left} {pr' : B'.left ⟶ A'.left} (h : pr ≫ A.hom = B.hom ≫ spMap σ)
    (h' : pr' ≫ A'.hom = B'.hom ≫ spMap σ) (f : A' ⟶ A) (f' : B' ⟶ B) (e : f'.left ≫ pr = pr' ≫ f.left)
    (c : HO2 A.hom) : pullHO2 h' (structureSheafH2Pullback f c) = structureSheafH2Pullback f' (pullHO2 h c) := by
  have h'' : (pr' ≫ f.left) ≫ A.hom = B'.hom ≫ spMap σ := by rw [Category.assoc, Over.w f, h']
  have a1 := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R R _ _ A.hom A'.hom (RingHom.id R) f.left (ovw f) K _ B'.hom σ pr' h' σ _ h''
    rfl (fun _ ↦ rfl)).2.1 c
  have a2 := (_root_.GlobalTheory.AbCoh.pull_comp_cup_id.1 R K _ _ A.hom B.hom σ pr h K _ B'.hom (RingHom.id K) f'.left (ovw f') σ _ h''
    e.symm (fun _ ↦ rfl)).2.1 c
  exact a1.trans a2.symm

theorem noPrimO2_of_isNoetherianRing : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → NoPrimitiveStructureSheafH2 A := by
  intro R _ _ A _ g hA hg
  obtain ⟨⟨_, _⟩, bc⟩ := abelian_scheme_second_cohomology_finite_projective R A g hA hg
  obtain ⟨hA2, hg2⟩ := (_root_.GlobalTheory.Obs.sq_abelian_and_affine_H1 R).1 A g hA hg
  obtain ⟨⟨_, _⟩, bc2⟩ := abelian_scheme_second_cohomology_finite_projective R (A ⊗ A) (g + g) hA2 hg2
  let D : HO2 A.hom →ₗ[R] HO2 (A ⊗ A).hom := structureSheafH2Pullback μ[A] - structureSheafH2Pullback (fst A A) - structureSheafH2Pullback (snd A A)
  have hD : Function.Injective D := by
    refine injective_of_algClosure R _ _ D fun K _ _ _ ↦ ?_
    obtain ⟨B, _, pr, pr', hB, hgB, p1, p2, eμ, e1, e2, -, -⟩ := _root_.GlobalTheory.AbBaseChangeSq.exists_baseChange_and_sq R K A g hA hg
    obtain ⟨e, he⟩ := bc K _ _ _ p1
    obtain ⟨e', he'⟩ := bc2 K _ _ _ p2
    have hN := (_root_.GlobalTheory.AbCoh.wedgeO_noPrimO2 K B g hB hgB).2
    let DB : HO2 B.hom →ₗ[K] HO2 (B ⊗ B).hom := structureSheafH2Pullback μ[B] - structureSheafH2Pullback (fst B B) - structureSheafH2Pullback (snd B B)
    have key : ∀ x, e' (D.baseChange K x) = DB (e x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a c =>
        have : a ⊗ₜ[R] c = a • ((1 : K) ⊗ₜ[R] c) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, map_smul, map_smul, map_smul, map_smul, LinearMap.baseChange_tmul, he, he']
        congr 1
        simp only [D, DB, LinearMap.sub_apply, map_sub]
        rw [pull_comm p1.w p2.w _ _ eμ, pull_comm p1.w p2.w _ _ e1, pull_comm p1.w p2.w _ _ e2]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : DB (e x) = 0 := by rw [← key, hx, map_zero]
    have h1 : e x = 0 := hN _ (by
      simp only [DB, LinearMap.sub_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0)
    exact e.map_eq_zero_iff.1 h1
  intro z hz
  refine (injective_iff_map_eq_zero D).1 hD z ?_
  simp only [D, LinearMap.sub_apply]
  rw [hz]; abel

end GlobalTheory.AbCoh.NoPrimNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  apply Subtype.ext
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := _root_.GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := _root_.GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

section Lin

variable {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem smul_top_le_comap (f : M →ₗ[S] N) (J : Ideal S) :
    J • (⊤ : Submodule S M) ≤ (J • (⊤ : Submodule S N)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hr trivial

theorem mem_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (x : M) :
    e x ∈ J • (⊤ : Submodule S N) ↔ x ∈ J • (⊤ : Submodule S M) :=
  ⟨fun h ↦ by simpa using smul_top_le_comap (e.symm : N →ₗ[S] M) J h,
   fun h ↦ smul_top_le_comap (e : M →ₗ[S] N) J h⟩

theorem mem_sup_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (K : Submodule S N) (x : M) :
    x ∈ K.comap (e : M →ₗ[S] N) ⊔ J • ⊤ ↔ e x ∈ K ⊔ J • ⊤ := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup ha ((mem_smul_top_equiv e J b).2 hb)
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    have hx : x = e.symm a + e.symm b := by rw [← map_add (f := _), hab, LinearEquiv.symm_apply_apply]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ((mem_smul_top_equiv e J _).1 (by simpa using hb))
    simpa using ha

theorem exists_isCompl_comap_iff (e : M ≃ₗ[S] N) (K : Submodule S N) :
    (∃ L, IsCompl K L) ↔ ∃ L, IsCompl (K.comap (e : M →ₗ[S] N)) L := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨L.comap (e : M →ₗ[S] N), (Submodule.orderIsoMapComap e).symm.isCompl h⟩
  · rintro ⟨L, h⟩
    refine ⟨L.map (e : M →ₗ[S] N), ?_⟩
    have := (Submodule.orderIsoMapComap e).isCompl h
    simpa [Submodule.orderIsoMapComap, Submodule.map_comap_eq_of_surjective e.surjective] using this

end Lin

theorem admissible_classification : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  obtain ⟨-, -, pc, bij, fin, proj, hA₀, hg₀⟩ :=
    abelianLift_facts H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨rs, rk⟩ := _root_.GlobalTheory.LiftSys.rhoBC_of_abelianLift H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨-, ⟨N₀, hN₀⟩, -⟩ := GlobalTheory.AbelianHodge.abelianDeRham_hodge H1 H2 R₀ A₀ g hA₀ hg₀
  let P := prim (divided₂ hI) (spMap π) A₀
  let Ψ : primDR A' ≃ₗ[R] P := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').pull bij
  let Φ : primDR A' ≃ₗ[R] Cr hI π A₀.hom := Ψ.trans (LinearEquiv.ofTop _ pc)
  have hΦ : ∀ c, Φ c = ((Ψ c : P) : Cr hI π A₀.hom) := fun _ ↦ rfl
  let ρ := (GrothendieckMessing.redMor h').pull
  have mT : IsMor (dp0 R₀) (A₀.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have mT' : IsMor (dp0 R₀) A₀.hom (dp0 R₀) (A₀.hom ≫ 𝟙 _) (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have back : ∀ x, mT'.pull1 (mT.pull1 x) = x := fun x ↦
    (IsMor.pullback1_comp mT mT' (IsMor.id _ _) (fun _ ↦ rfl) (Category.id_comp _) x).trans
      (IsMor.pullCohomologyOne_id _ x)
  have inj : Function.Injective mT.pull1 := Function.LeftInverse.injective back
  have mD : IsMor (dp0 R) (A'.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom π i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id]; exact h'.1.w)
  have key : ∀ c : primDR A',
      mT.pull1 ((ρ c : primDR A₀) : FirstDeRham (A₀.hom ≫ 𝟙 _)) = rho hI hk A₀.hom (Φ c) := by
    intro c
    rw [hΦ]
    exact (IsMor.pullback1_comp _ mT mD (fun _ ↦ rfl) (Category.id_comp _) c.1).trans
      (IsMor.pullback1_comp _ (redMor hI hk A₀.hom) mD (fun _ ↦ rfl) (Category.id_comp _) c.1).symm
  have F1iff : ∀ c : primDR A', ρ c ∈ PrimitiveSubmodule A₀ ↔ rho hI hk A₀.hom (Φ c) ∈ F1 A₀.hom := by
    intro c
    rw [← key]
    constructor
    · intro h
      exact mT.pullback1_mem_hodgeFiltration h
    · intro h
      have := mT'.pullback1_mem_hodgeFiltration h
      rw [back] at this
      exact this
  have ρker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R (primDR A')) := by
    intro c
    rw [hk, ← mem_smul_top_equiv Φ, ← rk, ← key, map_eq_zero_iff _ inj, Submodule.coe_eq_zero]
  have ρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨d, hd⟩ := rs (mT.pull1 y.1)
    refine ⟨Φ.symm d, Subtype.ext (inj ?_)⟩
    rw [key, LinearEquiv.apply_symm_apply, hd]
  obtain ⟨D1, D2⟩ := _root_.GlobalTheory.LiftSys.summand_dual_reduction R R₀ π hπ (primDR A') (primDR A₀) (Module.Finite.equiv Φ.symm)
    (Module.Projective.of_equiv Φ.symm) ρ ρsurj ρker (PrimitiveSubmodule A₀) ⟨N₀, hN₀⟩
  have cond : ∀ K : Submodule R (Cr hI π A₀.hom),
      (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ↔
        ∀ c, c ∈ K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) ⊔ RingHom.ker π • ⊤ ↔
          ρ c ∈ PrimitiveSubmodule A₀ := by
    intro K
    rw [hk]
    constructor
    · intro H c
      rw [mem_sup_smul_top_equiv, F1iff]
      exact H (Φ c)
    · intro H c
      have := H (Φ.symm c)
      rwa [mem_sup_smul_top_equiv, F1iff, LinearEquiv.apply_symm_apply] at this
  have crysSurj : Function.Surjective (crysToDR (divided₂ hI) h') := fun y ↦
    ⟨y.comp (Ψ.symm : P →ₗ[R] primDR A'), LinearMap.ext fun c ↦ by
      rw [crysToDR_apply]
      exact congrArg y (Ψ.symm_apply_apply c)⟩
  have ann : ∀ K : Submodule R (Cr hI π A₀.hom),
      (K.comap P.subtype).dualAnnihilator =
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator.comap
          (crysToDR (divided₂ hI) h') := by
    intro K
    ext d
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator, crysToDR_apply]
    constructor
    · intro H c hc
      exact H _ hc
    · intro H p hp
      have e : (liftMor (divided₂ hI) h').pull (Ψ.symm p) = p := Ψ.apply_symm_apply p
      have hm : Φ (Ψ.symm p) ∈ K := by
        rw [hΦ, Ψ.apply_symm_apply]
        exact hp
      have := H (Ψ.symm p) hm
      rwa [crysToDR_apply, e] at this
  have eqiff : ∀ (K : Submodule R (Cr hI π A₀.hom)) (F : Submodule R (HdR A')),
      (K.comap P.subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h') ↔
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator = F := by
    intro K F
    rw [ann]
    exact (Submodule.comap_injective_of_surjective crysSurj).eq_iff
  refine ⟨fun K hK hc ↦ ?_, fun F hF ↦ ?_, fun K K' hK hK' he ↦ ?_⟩
  · obtain ⟨c1, -, c3⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    exact ⟨_, ⟨c1, c3.1 ((cond K).1 hc)⟩, (eqiff K _).2 rfl⟩
  · obtain ⟨K', hK', rfl⟩ := D2 F hF.1
    have hKK : (K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).comap
        (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) = K' :=
      Submodule.comap_map_eq_of_injective Φ.injective K'
    obtain ⟨-, -, c3⟩ := D1 K' hK'
    refine ⟨K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom), (exists_isCompl_comap_iff Φ _).2 (by rw [hKK]; exact hK'),
      (cond _).2 (by rw [hKK]; exact c3.2 hF.2), (eqiff _ _).2 (by rw [hKK])⟩
  · rw [ann, ann] at he
    have e := Submodule.comap_injective_of_surjective crysSurj he
    obtain ⟨-, c2, -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    obtain ⟨-, c2', -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K').1 hK')
    refine Submodule.comap_injective_of_surjective Φ.surjective ?_
    rw [← c2, ← c2', e]

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleVanishing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.AmpleGen

namespace GlobalTheory.AmpleGen

theorem stepTwo {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h2 : (2 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (2 * a : ℕ) (2 * b : ℕ)) j₁ ∧
      NV A (mix A L (a + b : ℕ) (a + b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 1 * 1 : ℤ) : K) = -2 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h2
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := _root_.GlobalTheory.AmpleGen.nv_mix_pair_of_nv K A hA 1 1 1 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  simp only [t1, t0, neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem stepFive {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (h5 : (5 : K) ≠ 0) (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (h : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (4 * a + b : ℕ) (a + 4 * b : ℕ)) j₁ ∧
      NV A (mix A L (3 * a + 2 * b : ℕ) (2 * a + 3 * b : ℕ)) j₂ := by
  have hd : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) ≠ 0 := by
    have : (((1 : ℤ) * (-1) - 2 * 2 : ℤ) : K) = -5 := by push_cast; ring
    rw [this]; exact neg_ne_zero.2 h5
  obtain ⟨j₁, j₂, e, h₁, h₂⟩ := _root_.GlobalTheory.AmpleGen.nv_mix_pair_of_nv K A hA 1 2 2 (-1) (by norm_num) hd L hL a b j h
  have t1 : tri 1 = 1 := by decide
  have t0 : tri (-1) = 0 := by decide
  have t2 : tri 2 = 3 := by decide
  have t2' : tri (-2) = 1 := by decide
  simp only [t1, t0, t2, t2', neg_neg] at h₁ h₂
  refine ⟨j₁, j₂, e, ?_, ?_⟩
  · convert h₁ using 2 <;> push_cast <;> ring
  · convert h₂ using 2 <;> push_cast <;> ring

theorem step {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (L : LB A.left) (hL : L.IsLB) (a b i : ℕ) (h : NV A (mix A L a b) i) :
    ∃ (i₁ i₂ a₁ b₁ a₂ b₂ : ℕ), i₁ + i₂ = 2 * i ∧ NV A (mix A L a₁ b₁) i₁ ∧ NV A (mix A L a₂ b₂) i₂ ∧
      a + b ≤ a₁ + b₁ ∧ 2 * (a + b) ≤ a₂ + b₂ ∧ ((a₂ : ℤ) - b₂ = (a : ℤ) - b ∨ (a₂ : ℤ) - b₂ = 0) := by
  by_cases h2 : (2 : K) = 0
  · have h5 : (5 : K) ≠ 0 := by
      have : (5 : K) = 2 * 2 + 1 := by norm_num
      rw [this, h2]; simp
    obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepFive A hA h5 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inl (by push_cast; ring)⟩
  · obtain ⟨i₁, i₂, e, h₁, h₂⟩ := stepTwo A hA h2 L hL a b i h
    refine ⟨i₁, i₂, _, _, _, _, e, h₁, h₂, by omega, by omega, Or.inr (by push_cast; ring)⟩

theorem ampleVanishing : GlobalTheory.Published.AmpleVanishing := by
  intro K _ _ A _ hA L hL hamp
  refine _root_.GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV K A L fun j hj => ?_
  have h0 := _root_.GlobalTheory.AmpleGen.nv_mix_one_zero K A L hL _ hj
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.AmpleGen.not_NV_of_ge K A hA
  have hLB : ∀ a b : ℤ, (mix A L a b).IsLB := fun a b => LB.isLB_linComb hL _ _

  let S : ℕ → Prop := fun i => 1 ≤ i ∧ ∃ a b : ℕ, 1 ≤ a + b ∧ NV A (mix A L a b) i
  have hS : ∀ i, S i → i ≤ c := fun i ⟨_, a, b, _, h⟩ =>
    le_of_lt (not_le.1 fun hi => hc _ (hLB a b) i hi h)
  have hj1 : S (j + 1) := ⟨by omega, 1, 0, by omega, by exact_mod_cast h0⟩
  classical
  let T := Nat.findGreatest S c
  have hT : S T := Nat.findGreatest_spec (hS _ hj1) hj1
  have hmax : ∀ i, S i → i ≤ T := fun i hi => Nat.le_findGreatest (hS i hi) hi
  obtain ⟨hT1, a, b, hab, hTab⟩ := hT

  have next : ∀ a' b' : ℕ, 1 ≤ a' + b' → NV A (mix A L a' b') T → ∃ a₂ b₂ : ℕ,
      NV A (mix A L a₂ b₂) T ∧ 2 * (a' + b') ≤ a₂ + b₂ ∧
        ((a₂ : ℤ) - b₂ = (a' : ℤ) - b' ∨ (a₂ : ℤ) - b₂ = 0) := by
    intro a' b' h1 h
    obtain ⟨i₁, i₂, a₁, b₁, a₂, b₂, e, h₁, h₂, l₁, l₂, hd⟩ := step A hA L hL a' b' T h
    have u₁ : i₁ ≤ T := by
      rcases Nat.eq_zero_or_pos i₁ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₁, b₁, by omega, h₁⟩
    have u₂ : i₂ ≤ T := by
      rcases Nat.eq_zero_or_pos i₂ with h0 | h0
      · omega
      · exact hmax _ ⟨h0, a₂, b₂, by omega, h₂⟩
    exact ⟨a₂, b₂, by rwa [show i₂ = T by omega] at h₂, l₂, hd⟩
  have grow : ∀ n : ℕ, ∃ a' b' : ℕ, 1 ≤ a' + b' ∧ n ≤ a' + b' ∧ NV A (mix A L a' b') T ∧
      ((a' : ℤ) - b' = (a : ℤ) - b ∨ (a' : ℤ) - b' = 0) := by
    intro n
    induction n with
    | zero => exact ⟨a, b, hab, by omega, hTab, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨a', b', h1, hn, h, hd⟩ := ih
      obtain ⟨a₂, b₂, h₂, l, hd₂⟩ := next a' b' h1 h
      refine ⟨a₂, b₂, by omega, by omega, h₂, ?_⟩
      rcases hd₂ with e | e
      · rw [e]; exact hd
      · exact Or.inr e
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp ((a : ℤ) - b)
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.T.serre_vanishing_lineBundleInvMix_fixed_difference K A hA L hL hamp 0
  obtain ⟨a', b', -, hn, h, hd⟩ := grow (N₁ + N₂)
  obtain ⟨t, ht⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  rw [ht] at h
  rcases hd with e | e
  · exact hN₁ a' b' (by omega) e t h
  · exact hN₂ a' b' (by omega) e t h

end GlobalTheory.AmpleGen
end
end

