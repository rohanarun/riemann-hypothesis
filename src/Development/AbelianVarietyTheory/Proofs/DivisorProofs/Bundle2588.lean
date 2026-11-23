module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparating
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAmpleSep

theorem mem_iff_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (I : Ideal R) (hI : ∀ j, r j - φ (c j) ∈ I) (p : MvPolynomial κ A) :
    MvPolynomial.eval₂Hom φ r p ∈ I ↔ φ (MvPolynomial.eval c p) ∈ I := by
  have hr : (Ideal.Quotient.mk I) ∘ r = ((Ideal.Quotient.mk I).comp φ) ∘ c := by
    funext j; exact Ideal.Quotient.eq.2 (hI j)
  have e : Ideal.Quotient.mk I (MvPolynomial.eval₂Hom φ r p) = Ideal.Quotient.mk I (φ (MvPolynomial.eval c p)) := by
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, hr, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.eval₂_comp_left]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := I), e]

theorem ideal_eq_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom φ r)) (P Q : Ideal R)
    (hP : ∀ j, r j - φ (c j) ∈ P) (hQ : ∀ j, r j - φ (c j) ∈ Q) (hPQ : ∀ x, φ x ∈ P ↔ φ x ∈ Q) : P = Q := by
  ext a
  obtain ⟨p, rfl⟩ := hs a
  rw [mem_iff_of_gen φ r c P hP, mem_iff_of_gen φ r c Q hQ]
  exact hPQ _

theorem mem_basicOpen_iff_prime {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) {y : Y} (hy : y ∈ D)
    (a : Γ(Y, D)) : y ∈ Y.basicOpen a ↔ a ∉ (hD.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have h := hD.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hD.primeIdealOf ⟨y, hy⟩ ∈ hD.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ y ∈ Y.basicOpen a := by
    show hD.fromSpec (hD.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a ↔ y ∈ Y.basicOpen a
    rw [h]
  rw [← h2, hD.fromSpec_preimage_basicOpen]
  rfl

variable {K : Type} [Field K]

theorem one_left_comp_hom (B : AbVar K) : (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ≫ B.X.hom = 𝟙 _ := Over.w _

theorem sp_pt_eq (a b : Sp K) : a = b := by
  have h : ∀ p : PrimeSpectrum K, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem top_le_preimage_unit (B : AbVar K) : (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens) ≤
    (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ⁻¹ᵁ (B.X.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial

def unitU (B : AbVar K) : (⊤ : (Sp K).Opens).toScheme ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left.resLE (B.X.hom ⁻¹ᵁ ⊤) (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens)
    (top_le_preimage_unit B)

theorem unitU_comp (B : AbVar K) : unitU B ≫ (B.X.hom ∣_ ⊤) = 𝟙 _ := by
  rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, unitU,
    Scheme.Hom.resLE_comp_ι_assoc, one_left_comp_hom, Category.comp_id, Category.id_comp]

theorem unitU_ι (B : AbVar K) (t : (⊤ : (Sp K).Opens).toScheme) :
    (B.X.hom ⁻¹ᵁ ⊤).ι (unitU B t) = B.origin := by
  rw [← Scheme.Hom.comp_apply, unitU, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, AbVar.origin]
  exact congrArg _ (sp_pt_eq _ _)

theorem topU_pt_eq (a b : (⊤ : (Sp K).Opens).toScheme) : a = b := Subtype.ext (sp_pt_eq _ _)

theorem isUnit_sub_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (c : R) (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a - c * b) := by
  by_contra h
  have hb' : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hb
  have h' : a - c * b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h'' := Ideal.add_mem _ h' (Ideal.mul_mem_left _ c hb')
  rw [sub_add_cancel] at h''
  exact (IsLocalRing.mem_maximalIdeal _).1 h'' ha

theorem gs_secSubScale {Y : Scheme.{0}} {P : LB Y} (a b : P.Sec) (c : Γ(Y, ⊤)) (y : Y) (k : P.ι) (hk : y ∈ P.U k) :
    gs (𝟙 Y) y _ ((DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k) =
      gs (𝟙 Y) y _ (a.f k) - gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (b.f k) := by
  have e : (DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k =
      a.f k - Out.resTop _ c * b.f k := by
    simp only [DVR.SecOps.secAdd, DVR.SecOps.secNeg, DVR.SecOps.secScale, sub_eq_add_neg]
  rw [e, LBGerm.gs_sub _ y _ hk, gs_mul _ y _ hk, Out.resTop, gs_res _ y _ hk]

theorem exists_sep_of_chart {Y T : Scheme.{0}} (π : Y ⟶ T) (u : T ⟶ Y) (hu : u ≫ π = 𝟙 T) (hT : ∀ a b : T, a = b)
    {P : LB Y} (hP : P.IsLB) {n : ℕ} (s : Fin n → P.Sec) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (i : Fin n) (hD : IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : Fin n → Γ(Y, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
            (Y.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r))
    (t₀ : T) (hi : u t₀ ∈ Out.nonzeroLocus (s i)) :
    ∃ t : Fin n → P.Sec, (∀ j, u t₀ ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, y ≠ u t₀ → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  classical
  have hTle : ⊤ ≤ u ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t _ => by rw [hT t t₀]; exact hi
  let c : Fin n → Γ(T, ⊤) := fun j => (u.appLE (Out.nonzeroLocus (s i)) ⊤ hTle).hom (r j)
  let φ := (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom
  have hc : ∀ (y : Y) (x : Γ(T, ⊤)), gs (𝟙 Y) y ⊤ (π.appTop.hom x) = gs π y ⊤ x := fun y x =>
    (gs_pull (𝟙 Y) π y ⊤ trivial x).trans (by rw [Category.id_comp])
  have hφ : ∀ y ∈ Out.nonzeroLocus (s i), ∀ x, gs (𝟙 Y) y _ (φ x) = gs π y ⊤ x := fun y hy x =>
    (gs_appLE π ⊤ _ le_top (𝟙 Y) y hy x).trans (by rw [Category.id_comp])
  have hrel : ∀ j k y, y ∈ Out.nonzeroLocus (s i) → y ∈ P.U k →
      gs (𝟙 Y) y _ ((s j).f k) = gs (𝟙 Y) y _ (r j) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro j k y hyD hk
    have hm : y ∈ Out.nonzeroLocus (s i) ⊓ P.U k := ⟨hyD, hk⟩
    have e := congrArg (gs (𝟙 Y) y (Out.nonzeroLocus (s i) ⊓ P.U k)) (hr j k)
    rwa [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  have hkey : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j k, y ∈ P.U k →
      gs (𝟙 Y) y _ ((DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))).f k) =
        gs (𝟙 Y) y _ (r j - φ (c j)) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro y hy j k hk
    rw [gs_secSubScale _ _ _ y k hk, hrel j k y hy hk, hc, LBGerm.gs_sub _ y _ hy, hφ y hy]
    ring
  have hiff : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j,
      y ∈ Out.nonzeroLocus (DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))) ↔ y ∈ Y.basicOpen (r j - φ (c j)) := by
    intro y hy j
    obtain ⟨k, hk⟩ := exists_chart hP y
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, hkey y hy j k hk, IsUnit.mul_iff,
      ← GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk, LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy]
    exact and_iff_left hy
  have h0 : ∀ j, u t₀ ∉ Y.basicOpen (r j - φ (c j)) := by
    intro j h
    have hu1 := (LBGerm.isUnit_gs_iff u t₀ _ hi _).2 h
    have e1 : gs u t₀ _ (r j) = gs (𝟙 T) t₀ ⊤ (c j) :=
      ((gs_appLE u _ ⊤ hTle (𝟙 T) t₀ trivial (r j)).trans (by rw [Category.id_comp])).symm
    have e2 : gs u t₀ _ (φ (c j)) = gs (𝟙 T) t₀ ⊤ (c j) :=
      (gs_appLE π ⊤ _ le_top u t₀ hi (c j)).trans (by rw [hu])
    rw [LBGerm.gs_sub u t₀ _ hi, e1, e2, sub_self] at hu1
    exact not_isUnit_zero hu1
  refine ⟨fun j => DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i))),
    fun j h => h0 j ((hiff _ hi j).1 h), fun y hy => ?_⟩
  by_cases hyD : y ∈ Out.nonzeroLocus (s i)
  · by_contra hno
    push_neg at hno
    have hPy : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal := fun j => by
      by_contra h
      exact hno j ((hiff y hyD j).2 ((mem_basicOpen_iff_prime hD hyD _).2 h))
    have hQ : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := fun j => by
      by_contra h
      exact h0 j ((mem_basicOpen_iff_prime hD hi _).2 h)
    have hb : ∀ z ∈ Out.nonzeroLocus (s i), ∀ x, z ∈ Y.basicOpen (φ x) ↔ π z ∈ T.basicOpen x := fun z hz x =>
      (LBGerm.isUnit_gs_iff (𝟙 Y) z _ hz (φ x)).symm.trans (by rw [hφ z hz]; exact LBGerm.isUnit_gs_iff π z ⊤ trivial x)
    have hPQ : ∀ x, φ x ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal ↔ φ x ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := by
      intro x
      rw [← not_iff_not, ← mem_basicOpen_iff_prime hD hyD, ← mem_basicOpen_iff_prime hD hi, hb y hyD, hb _ hi,
        hT (π y) (π (u t₀))]
    have hE := ideal_eq_of_gen φ r c hs _ _ hPy hQ hPQ
    have e1 := hD.fromSpec_primeIdealOf ⟨y, hyD⟩
    have e2 := hD.fromSpec_primeIdealOf ⟨u t₀, hi⟩
    rw [PrimeSpectrum.ext hE] at e1
    exact hy (e1.symm.trans e2)
  · have hy' : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨k, hk⟩ := exists_chart hP y
    refine ⟨j, ?_⟩
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, gs_secSubScale _ _ _ y k hk]
    exact isUnit_sub_mul_of_not_isUnit _ ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s j) hk).1 hj)
      fun h => hyD ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk).2 h)

theorem exists_sec_sep_origin : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB →
    Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)),
      (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  intro K _ B L hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  obtain ⟨t₀⟩ : Nonempty (⊤ : (Sp K).Opens).toScheme := ⟨⟨IsLocalRing.closedPoint K, trivial⟩⟩
  have hmem : unitU B t₀ ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨t, h1, h2⟩ := exists_sep_of_chart (B.X.hom ∣_ ⊤) (unitU B) (unitU_comp B) topU_pt_eq
    (LB.isLB_linComb hL _ _) s hcov i hD r hr hsurj t₀ hi
  have hinj : ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y = unitU B t₀ := fun y hy =>
    Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans
      (hy.trans ((unitU_ι B t₀).symm.trans (Scheme.Opens.ι_apply _ _))))
  exact ⟨N, hN, M + 1, t, fun j y hy => hinj y hy ▸ h1 j, fun y hy => h2 y fun h => hy (h ▸ unitU_ι B t₀)⟩

end GlobalTheory.RelAmpleSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModification
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLift

open _root_.CategoryTheory.Limits GlobalTheory.MixHt

theorem exists_cover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X']
    [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D →
    IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X →
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧
      IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧
      g.residueDegree (genericPoint Y') ≠ 0 := by
  intro k _ X X' Y _ _ _ p D E ρ π hX hX' hY hρ

  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hX'.isProjOver
  have : IsProper (ρ ≫ p) := hj' ▸ inferInstance
  have : IsProper ρ := IsProper.of_comp ρ p
  have hs : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← ρ.isClosedMap.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hρ⟩)
  have : Surjective ρ := ⟨hs⟩

  obtain ⟨z, hz, hdeg⟩ := exists_residueDegree_pos_of_mem_range _ _ (pullback.fst π ρ) (genericPoint Y)
    ((inferInstance : Surjective (pullback.fst π ρ)).surj _)
  set g := cloι z ≫ pullback.fst π ρ with hgdef
  have hg : g (genericPoint (clo z)) = genericPoint Y := by
    rw [hgdef, Scheme.Hom.comp_apply, cloι_genericPoint, hz]
  have hdeg' : g.residueDegree (genericPoint (clo z)) ≠ 0 := by
    rw [hgdef, CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion (cloι z), mul_one,
      cloι_genericPoint]
    exact hdeg.ne'

  have hP : IsProjOver (pullback.fst π ρ ≫ π ≫ p) :=
    FlagFamily.isProjOver_pullback_over hX.isProjOver hY.isProjOver hX'.isProjOver
  have hA : IsAmb (g ≫ π ≫ p) := by
    have := (IsAmb.mk hX.1 hX.2 hP).sub (cloι z)
    rwa [← Category.assoc] at this
  have hAY : IsAmb (π ≫ p) := isAmb_of_isArithVar hY

  obtain ⟨⟨m, hm⟩, -, -, -, -, hgen⟩ := hasDim_basic k (clo z) (g ≫ π ≫ p) hA
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo z))
  have hdY : HasDim (g (genericPoint (clo z))) (E + 1) := by
    rw [hg]
    exact (DimBasic.hasDim_genericPoint_iff Y (E + 1)).2 hY.dim_eq
  have hcmp := DimDeg.dim_le_and_residueDegree_ne_zero_iff k Y (clo z) (π ≫ p) (g ≫ π ≫ p) hAY hA g rfl
    (genericPoint (clo z)) d (E + 1) hd hdY
  have hdim : topologicalKrullDim (clo z) = (E + 1 : ℕ) := (hgen (clo z) (E + 1)).1 (hcmp.2.1 hdeg' ▸ hd)

  have hcY : CharZero Γ(Y, ⊤) := hY.charZero
  have h₁ : CharZero Y.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Y.Opens) (Opens.mem_top _))
  have h₂ : CharZero (Y.residueField (genericPoint Y)) := by
    let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue _).hom
    exact charZero_of_injective_ringHom f.injective
  have h₃ : CharZero (Y.residueField (g (genericPoint (clo z)))) := hg ▸ h₂
  have h₄ : CharZero ((clo z).residueField (genericPoint (clo z))) :=
    charZero_of_injective_ringHom (g.residueFieldMap _).hom.injective
  have h₅ : CharZero (clo z).functionField := by
    let f : (clo z).functionField →+* (clo z).residueField (genericPoint (clo z)) := ((clo z).residue _).hom
    exact (RingHom.charZero_iff f.injective).2 h₄
  have h₆ : CharZero Γ(clo z, ⊤) :=
    (RingHom.charZero_iff (fnOf_injective (⊤ : (clo z).Opens) (Opens.mem_top _))).2 h₅
  refine ⟨clo z, inferInstance, g, cloι z ≫ pullback.snd π ρ, ?_,
    ⟨hX.1, hX.2, inferInstance, hA.isProjOver, (flat_int_iff_charZero _).2 h₆, hdim⟩, hg, hdeg'⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

end GlobalTheory.CoverLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFiniteInjectiveCompleteNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep


set_option maxHeartbeats 1600000 in
theorem UMem.exists_baseChange : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'), (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → IsCN V' → Function.Injective io → io.Finite → ∃ (D' : DegData V' (maximalIdeal V')) (e₈' : (Fin 8 → X) ≃+ D'.toPre.X) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G') (ψ : A'.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G), IsSemiAbelian G' ∧ IsGrpPullback A'.A 𝔪.A.A (spMap f) ψ ∧ (∃ w : LB.Iso A'.L (𝔪.A.L.pull ψ), w.IsGen) ∧ IsMonHom bc.hom ∧ IsPullUnif io hD bc 𝔪.U U' ∧ (∀ mu, hD.xe (e₈' mu) = 𝔪.e₈ mu) ∧ U'.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) = pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ∧ (∀ E : EndU 𝔪.U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aA.left ≫ ψ = ψ ≫ E.aA.left ∧ ∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ mu, ∃ u : V'ˣ, Formalism.L2.Pj.PsiCoord D'.toPre (e₈' mu) (u * mono W (fun k => io (t k)) δ mu) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ io f hf hcn hinj hfin
  have hV := 𝔪.cn
  have aR : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have aR' : AdmBase V' (maximalIdeal V') := ⟨hcn.1, inferInstance, hcn.2.1, hcn.2.2.1⟩
  have hI : (maximalIdeal V).map io ≤ maximalIdeal V' := by
    letI := io.toAlgebra
    haveI : Algebra.IsIntegral V V' := ⟨hfin.to_isIntegral⟩
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) (algebraMap _ _) hfin.to_isIntegral (maximalIdeal V')
    rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  let G' : Over (Sp V') := (Over.pullback (spMap io)).obj 𝔪.G
  let bc : G' ≅ (Over.pullback (spMap io)).obj 𝔪.G := Iso.refl _
  have mbc : IsMonHom bc.hom := inferInstanceAs (IsMonHom (𝟙 G'))
  have semi' : IsSemiAbelian G' := IsSemiAbelian.pullback (spMap io) 𝔪.G 𝔪.semi
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap f) 𝔪.A
  have gpA : IsGrpPullback A'.A 𝔪.A.A (spMap f) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have sq : spMap f ≫ jK V = jK V' ≫ spMap io :=
    (spMap_comp _ f).symm.trans ((congrArg spMap (RingHom.ext hf)).trans (spMap_comp io _))
  have gpG : IsGrpPullback 𝔪.A.A 𝔪.G (jK V) (𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V)) := by
    have := 𝔪.U.gen_hom
    have : IsMonHom 𝔪.U.gen.symm.hom := by show IsMonHom 𝔪.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso 𝔪.U.gen.symm).comp (isGrpPullback_pullback 𝔪.G (jK V))).congr
      (Category.id_comp _) rfl
  have gp' : IsGrpPullback ((Over.pullback (jK V')).obj G') 𝔪.G (spMap f ≫ jK V)
      (pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io)) :=
    ((isGrpPullback_pullback G' (jK V')).comp (isGrpPullback_pullback 𝔪.G (spMap io))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have := 𝔪.U.gen_hom

  have hgi : 𝔪.U.gen.inv.left ≫ 𝔪.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc0 : bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io) = pullback.fst 𝔪.G.hom (spMap io) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (𝔪.U.LG.L.pull (pullback.fst G'.hom (jK V') ≫
      bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB 𝔪.A.isLB gA) eA.hom.left)
      (pull_isLB 𝔪.U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (𝔪.A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left)
      (chartPullLinComb 𝔪.A.L gA (fun _ => eA.hom.left) (fun _ => 𝔪.U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame 𝔪.U.LG.L _ (fun _ => pullback.fst 𝔪.G.hom (jK V)) _ _ fun _ => ?_) 𝔪.U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc0, ← heA]; simp only [Category.assoc]
  have hbc : IsGrpPullback G' 𝔪.G (specOf io) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) :=
    (isGrpPullback_pullback 𝔪.G (specOf io)).congr rfl hbc0.symm
  have he := GlobalTheory.PolBaseChange.eSec_comm hbc
  let L' : RigLB G' := ⟨𝔪.U.LG.L.pull (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)),
    rigPullOf (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he 𝔪.U.LG.L 𝔪.U.LG.rig,
    pull_isLB 𝔪.U.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G') (G := 𝔪.G) (bc.hom.left ≫ pullback.fst 𝔪.G.hom (specOf io)) (specOf io) he
      𝔪.U.LG.L 𝔪.U.LG.rig 𝔪.U.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf io) 𝔪.G G' _ he 𝔪.U.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB 𝔪.U.LG.isLB _))
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V _ aR 𝔪.D
  have hgen : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) ∈ Wo := by
    have : (specOf io).base (genericPoint (Spec (CommRingCat.of V'))) = genericPoint (Spec (CommRingCat.of V)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective io hinj)
    rw [this]; exact hWo
  obtain ⟨D', hD, U', hLG, hgenU, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V' _ _ aR aR' io hI 𝔪.D 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U Wo hψ hgen G' bc mbc A' dA eA mE wA L' wL he gL rL
  have hgc : U'.gen.hom.left ≫ gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
      pullback.fst G'.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) := by
    rw [hgenU, hbc0, heA]
  refine ⟨D', 𝔪.e₈.trans hD.xe.symm, G', inferInstance, inferInstance, A', U', gA, hD, bc, semi', gpA,
    LBIso.symm tA, mbc, hPU, fun mu => hD.xe.apply_symm_apply _, hgc, fun E => ?_, fun mu => ?_⟩
  · have := E.homG
    have := E.homA
    have := U'.gen_hom
    let aG' : G' ⟶ G' := (Over.pullback (spMap io)).map E.aG
    have maG : IsMonHom aG' := inferInstanceAs (IsMonHom ((Over.pullback (spMap io)).map E.aG))
    have mi : IsMonHom U'.gen.inv := by infer_instance
    let aA' : A'.A ⟶ A'.A := U'.gen.inv ≫ (Over.pullback (jK V')).map aG' ≫ U'.gen.hom
    have maA : IsMonHom aA' := by infer_instance
    have hext : (Over.pullback (jK V')).map aG' ≫ U'.gen.hom = U'.gen.hom ≫ aA' := by
      simp only [aA', Iso.hom_inv_id_assoc]
    obtain ⟨E', hG', hA'⟩ := exists_degenerationEndomorphism_of_admissibleBase V' _ aR' D' A' G' semi' U' aG' aA' maG maA hext
    have hfa : aG'.left ≫ pullback.fst 𝔪.G.hom (spMap io) = pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left :=
      pullback.lift_fst _ _ _
    have hgG : E'.aG.left ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) =
        bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) ≫ E.aG.left := by
      rw [hG', hbc0]; exact hfa
    refine ⟨E', ?_, _root_.GlobalTheory.EndPullChar.pull_char_eq V V' _ _ aR aR' io hinj hI 𝔪.D D' hD 𝔪.A A' 𝔪.G G' 𝔪.semi semi' 𝔪.U U' bc mbc hPU E E' hgG⟩
    have actA : E.aA.left ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) ≫ E.aG.left := by
      have e : E.aA ≫ 𝔪.U.gen.inv = 𝔪.U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
        rw [Iso.comp_inv_eq, Category.assoc]
        exact ((Iso.inv_comp_eq _).2 E.ext).symm
      rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _)
    have hfa' : ((Over.pullback (jK V')).map aG').left ≫ pullback.fst G'.hom (jK V') =
        pullback.fst G'.hom (jK V') ≫ aG'.left := pullback.lift_fst _ _ _
    have hgc' : U'.gen.inv.left ≫ pullback.fst G'.hom (jK V') ≫ pullback.fst 𝔪.G.hom (spMap io) =
        gA ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) := by
      have hi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
      have := hgc
      rw [hbc0] at this
      rw [← this, ← Category.assoc, hi, Category.id_comp]
    rw [hA']
    apply gpG.1.hom_ext
    · simp only [aA', Over.comp_left, Category.assoc]
      rw [hgc, hbc0, ← Category.assoc ((Over.pullback (jK V')).map aG').left, hfa', Category.assoc, hfa, actA]
      simpa only [Category.assoc] using congrArg (· ≫ E.aG.left) hgc'
    · simp only [aA', Over.comp_left, Category.assoc, Over.w, Over.w_assoc, pA.w, pA.w_assoc]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hx : hD.xe ((𝔪.e₈.trans hD.xe.symm) mu) = 𝔪.e₈ mu := hD.xe.apply_symm_apply _
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ (hx.symm ▸ hu)
    refine ⟨u' * Units.map io.toMonoidHom u, ?_⟩
    have hm : mono W (fun k => io (t k)) δ mu = io (mono W t δ mu) := by
      simp only [mono, map_prod, map_pow]
    rw [hm]
    have e : ((u' * Units.map io.toMonoidHom u : V'ˣ) : V') * io (mono W t δ mu) = u' * io (u * mono W t δ mu) := by
      rw [Units.val_mul, map_mul, ← _root_.mul_assoc]; rfl
    rw [e]; exact hu'

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChevalleyCorrectionOverProperFibre
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

theorem GlobalTheory.FibreCorr.exists_correction : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens) (D : EffCartierData M.Z), (U : Set M.Z).Nonempty → (∀ x ∈ D.idealSheaf.support, x ∉ U) → ∀ (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ k : ℕ, ∃ e : ℕ, ∀ F : M₁.O z, (∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U → ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨ ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) F‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e) → ∃ G b : M₁.O z, (F : Ω) = G + b ∧ (∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x') ∧ b ∈ Ideal.span {c : M₁.O z | ¬ IsUnit c} ^ k := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn U D hU _ z hz k
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  have key : ∀ k, ∃ e, GlobalTheory.FibreCorr.approxIdeal hπ U D z e ≤
      GlobalTheory.FibreCorr.fibreIdeal hπ D z ⊔ maximalIdeal (M₁.O z) ^ k := by
    refine _root_.GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone (M₁.O z) (GlobalTheory.FibreCorr.approxIdeal hπ U D z) (GlobalTheory.FibreCorr.fibreIdeal hπ D z)
      (GlobalTheory.FibreCorr.approxIdeal_antitone U D z) (GlobalTheory.FibreCorr.pow_le_approxIdeal U D z) ?_
    intro F a ha hK
    have ha' : ∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈
        (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n := by
      intro n
      rw [← AdicCompletion.maximalIdeal_eq_map]
      exact ha n
    refine _root_.GlobalTheory.FormalCorr.mem_map_fibreIdeal o Ω M₁ M π hπ hprop hn₁ hn D z hz F a ha' ?_
    intro x' hx' hc f' hf' e
    obtain ⟨N, hN⟩ := _root_.GlobalTheory.FibreCorr.locbound o Ω M₁ M π hπ hn U D hU z x' hx' hc f' hf' e
    exact ⟨N, fun n hn => hN n hn (a n) (hK n)⟩
  obtain ⟨e, he⟩ := key k
  refine ⟨e, fun F hF => ?_⟩
  have hF' : F ∈ GlobalTheory.FibreCorr.approxIdeal hπ U D z e := hF
  obtain ⟨G, hG, b, hb, hGb⟩ := Submodule.mem_sup.1 (he hF')
  refine ⟨G, b, ?_, fun x' hx' f' hf' => hG x' hx' f' hf', ?_⟩
  · rw [← hGb]; simp
  · have hm : Ideal.span {c : M₁.O z | ¬ IsUnit c} = maximalIdeal (M₁.O z) :=
      Ideal.span_eq (maximalIdeal (M₁.O z))
    rw [hm]
    exact hb
end

