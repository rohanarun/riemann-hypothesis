module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigCube

theorem genericPoints_subset_abLocus {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) : genericPoints (Sp R) ⊆ abLocus G := by
  have : IsProper ((Over.pullback (jK R)).obj G).hom := hp
  refine Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG
    (IsPullback.of_hasPullback G.hom (jK R)))
  rw [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]
  rintro _ rfl
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

theorem exists_gen_theta_generic {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) {M : LB G.left} (hM : M.IsLB) :
    ∃ t : ((Theta G M).pull (pullback.fst (G3 G).hom (jK R))).Gen, t.IsGen := by
  let j := jK R
  let A : Over (Spec (CommRingCat.of (FractionRing R))) := (Over.pullback j).obj G
  have gp : IsGrpPullback A G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  have hA : IsSemiAbelian A := IsSemiAbelian.pullback j G hG
  have : IsProper A.hom := hp
  have hAb : IsAbelianScheme A := AbelianSchemeGerms.isAbelianScheme_of_proper A hA
  have := hA.comm
  let P : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk (pullback.snd (G3 G).hom j)
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (gp.1.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (gp.1.lift_snd _ _ _)
  let U : Over.mk (P.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
  have hx : ∀ i, pushPt gp.1.w (x i) = U ≫ x3 G i := fun i => Over.OverMorphism.ext (gp.1.lift_fst _ _ _)
  let πA := pullback.fst G.hom j
  let pf := pullback.fst (G3 G).hom j
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.CubeTop.cubeTheorem _ A hAb (M.pull πA) (pull_isLB hM _) P (x 0) (x 1) (x 2)
  obtain ⟨t₁, ht₁⟩ := CubeDescent.exists_gen_comp M πA _ _ t₀ ht₀
  let y : Fin 3 → (Over.mk (P.hom ≫ j) ⟶ G) := fun i => U ≫ x3 G i
  have key : ∀ z : P ⟶ A, z.left ≫ πA = (pushHom gp P z).left := fun z => rfl
  have hxp : ∀ i, pushHom gp P (x i) = y i := hx
  have e : lift (y 0) (lift (y 1) (y 2)) = U := by ext <;> simp [y, x3]
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hM (φ' := fun I => pf ≫ thφ G (x3 G) I) (ε' := thε) (fun V _ h => by
    have hθ := prod_cub (y 0) (y 1) (y 2) h
    rw [e] at hθ
    refine Eq.trans ?_ hθ.symm
    simp only [Fin.prod_univ_eight, key, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_mul, map_one, hxp, zpow_one, zpow_neg_one]
    simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, key, map_mul, map_one, hxp,
      zpow_one, zpow_neg_one]) t₁ ht₁
  let c := CechPic.cls M hM
  refine (CechPic.cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hM _ _) pf)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CechPic.cls_pull (LB.isLB_linComb hM _ _), CechPic.cls_linComb hM, map_sum]
  simp only [map_zsmul, ← CechPic.pull_comp]
  have h2 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM (fun I => pf ≫ thφ G (x3 G) I) thε)).2 ⟨t₂, ht₂⟩
  rw [CechPic.cls_linComb hM] at h2
  exact h2

theorem exists_rigLB_cubicalStr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ M : LB G.left, M.IsLB → ∃ (L : RigLB G) (_ : CubicalStr G L), L.L = M := by
  intro R _ _ _ _ _ G _ _ hG hp M hM
  have hab := genericPoints_subset_abLocus G hG hp
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨a₂, b₂, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁
  obtain ⟨a₃, b₃, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := R) (M.pull (eSec G)) (pull_isLB hM _)
  let L : RigLB G := ⟨M, r, hM, hr⟩
  have hΘ : (Theta G M).IsLB := LB.isLB_linComb hM _ _
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift 1 (lift 1 1)
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (G3 G) e.left (Theta G M) (Over.w e) a₃ b₃ hΘ
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hΘ _)) (exists_gen_theta_generic G hG hp hM)
  obtain ⟨c⟩ := (CubeGen.cubical_and_symmetric (Sp R) G L hG ⟨inferInstance, hab⟩).1 ⟨t, ht⟩
  exact ⟨L, c, rfl⟩

end GlobalTheory.RigCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSquaredLengthUpperUnitriangularGramEqOfAgr
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjective
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem forget_map_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  intro p _ D R _ _ b N N' hd hc h3 M M' π hπ ⟨om⟩
  haveI := M.smooth
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, ηu, hYf, hYe, HY⟩ := _root_.GlobalTheory.UPel.HT.exists_liftScheme p D R b N N' hc hd M.X M.s M.univ
  let T0 : Over M.X := Over.mk π
  have hw : ∀ a, ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = T0.hom := fun a => by
    have w : (om.φ : M'.univ.A.left ⟶ M.univ.A.left) ≫ M.univ.A.hom = M'.univ.A.hom ≫ π := om.cart.1.w
    have w2 : (M'.univ.eta a).left ≫ M'.univ.A.hom = 𝟙 M'.X := Over.w (M'.univ.eta a)
    show ((M'.univ.eta a).left ≫ om.φ) ≫ M.univ.A.hom = π
    erw [Category.assoc, w, ← Category.assoc, w2, Category.id_comp]
  let lv0 : D.La → (T0 ⟶ M.univ.A) := fun a => Over.homMk ((M'.univ.eta a).left ≫ om.φ) (hw a)
  have hl0 : IsLift M.univ N' T0 lv0 :=
    _root_.GlobalTheory.UPel.HT.isLift_of_point p D R b N N' hd hc M.X M'.X M.s M'.s M.univ M'.univ π om T0 (𝟙 M'.X) lv0
      (Category.id_comp π) fun a => (Category.id_comp _).symm
  obtain ⟨g0, hg0, -⟩ := (HY T0 lv0).1 hl0
  have hlY : IsLift M.univ N' Y ηu := (HY Y ηu).2 ⟨𝟙 Y, fun a => Category.id_comp _⟩
  obtain ⟨h, hh, hha⟩ := _root_.GlobalTheory.UPel.HT.OfLift.ofLift p D R b N N' h3 hd hc M M' π hπ om Y ηu hlY
  have e1 : g0.left ≫ h = 𝟙 M'.X := by
    refine _root_.GlobalTheory.UPel.HT.LiftUniq.eq_of_same_image p D R b N N' hd hc M.X M.s M.univ M' π hπ om M'.X _ _ ?_ fun a => ?_
    · rw [Category.assoc, hh, Over.w g0, Category.id_comp]
      rfl
    · rw [Category.id_comp, Category.assoc, ← hha a, ← Over.comp_left, hg0 a]
      rfl
  let hY : Y ⟶ T0 := Over.homMk h hh
  have e2 : hY ≫ g0 = 𝟙 Y := by
    obtain ⟨f, -, hf⟩ := (HY Y ηu).1 hlY
    have a1 := hf (hY ≫ g0) fun a => by
      rw [Category.assoc, hg0 a]
      ext
      simp only [Over.comp_left, Over.homMk_left, hY, lv0]
      rw [hha a]
    have a2 := hf (𝟙 Y) fun a => Category.id_comp _
    rw [a1, a2]
  have e2' : h ≫ g0.left = 𝟙 Y.left := by
    have := congrArg (fun q => q.left) e2
    simpa [hY] using this
  haveI : IsIso g0.left := ⟨⟨h, e1, e2'⟩⟩
  have e : π = g0.left ≫ Y.hom := (Over.w g0).symm
  have hfe : IsFinite π ∧ Etale π := by
    rw [e]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨hfe.1, hfe.2, ⟨fun z => ?_⟩⟩

  obtain ⟨k, _, _, g, hg⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X z
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, g ≫ M.s = spMap β :=
    ⟨(Spec.preimage (g ≫ M.s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := M.univ.geom k g β hβ
  have hN' : 0 < N' := levelPos_of_coprime hc
  have hN : 0 < N := by omega
  have hk : 0 < N' / N := Nat.div_pos (Nat.le_of_dvd hN' hd) hN
  let T : Over M.X := Over.mk g
  let lv : D.La → (T ⟶ M.univ.A) := fun a => I.ev N' a
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => I.add N' x y
  have hker : ∀ x, lv (N' • x) = 1 := fun x => (I.ker N' hN' hc _).2 ⟨x, rfl⟩
  have hlin : ∀ (c : D.O) x, lv (c • x) = lv x ≫ M.univ.act.act c := fun c x => I.lin N' c x
  haveI : IsLocallyNoetherian T.left := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k))
    infer_instance
  have hlv : IsLift M.univ N' T lv := by
    refine ⟨hadd, hker, hlin, fun x => ?_, fun k' _ _ x' => ?_⟩
    · show I.ev N' ((N' / N) • x) = toUnit T ≫ M.univ.eta x
      rw [hI x, I.ev_nsmul]
      have := I.tower N (N' / N) hN hk (by rw [Nat.mul_div_cancel' hd]; exact hc) x
      rwa [Nat.mul_div_cancel' hd] at this
    · have h0 : TateAt M.univ N' g (fun a => lv a) := ⟨I, fun y => rfl⟩
      have h1 : TateAt M.univ N' (𝟙 T.left ≫ T.hom)
          (fun a => (Over.homMk (𝟙 T.left) rfl : Over.mk (𝟙 T.left ≫ T.hom) ⟶ T) ≫ lv a) :=
        tateAt_congr M.univ N' (Category.id_comp g).symm _ _ (fun a => by congr 1) h0
      exact (_root_.GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes p D R b N N' hc M.X M.s M.univ T lv hadd hker hlin (𝟙 T.left) x'
        (x'.base (⊥ : PrimeSpectrum k')) (⊥ : PrimeSpectrum k') (by
          first
          | exact specializes_rfl
          | (rw [Scheme.id.base_apply])
          | (simp only [Scheme.Hom.id_apply]; exact specializes_rfl)
          | exact (Subsingleton.elim (α := PrimeSpectrum k) _ _) ▸ specializes_rfl)).1 h1
  obtain ⟨f, -, -⟩ := (HY T lv).1 hlv
  obtain ⟨u, hu⟩ : z ∈ Set.range g := by rw [hg]; rfl
  refine ⟨(f.left ≫ h).base u, ?_⟩
  have hf : f.left ≫ h ≫ π = g := by rw [hh]; exact Over.w f
  rw [← hu, ← hf]
  rfl

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorModuliMapDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.UPel.HT.MapDesc

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def objMapCongr {S S' : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f g : S' ⟶ S} (m : ObjMap o' o f) (h : f = g) : ObjMap o' o g := h ▸ m

end GlobalTheory.UPel.HT.MapDesc


open GlobalTheory.UPel.HT.MapDesc GlobalTheory.UPel.HT.MapComp in
theorem GlobalTheory.UPel.HT.MapDesc.nonempty_objMap_of_galoisCover : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
  (S S₁ Y : Scheme.{0}) (t : S ⟶ Sp R) (sY : Y ⟶ Sp R) (π₁ : S₁ ⟶ S) (Ga : Type) [Group Ga]
  (ρ₁ : Ga → (S₁ ⟶ S₁)) (f : S ⟶ Y) (o : Obj b N t) (o' : Obj b N (π₁ ≫ t)) (u : Obj b N sY),
  3 ≤ N → N.Coprime p → GlobalTheory.ZM.IsGaloisCover Ga ρ₁ π₁ → ObjMap o' o π₁ → ObjMap o' u (π₁ ≫ f) →
  Nonempty (ObjMap o u f) := by
  intro p _ D R _ b N S S₁ Y t sY π₁ Ga _ ρ₁ f o o' u hN hNp hG m₁ m₂
  let compose : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := fun {_ _ _} {_ _ _} {o₁ o₂ o₃} {_ _} m₁ m₂ =>
    { φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := m₁.cart.comp m₂.cart
      sq := MapComp.isSquare_comp m₁.sq m₂.sq
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have uniq : ∀ {T T' : Scheme.{0}} {sT : T ⟶ Sp R} {sT' : T' ⟶ Sp R} {x : Obj b N sT} {y : Obj b N sT'}
      {g g' : T ⟶ T'} (_ : g = g') (n : ObjMap x y g) (n' : ObjMap x y g'), n.φ = n'.φ := by
    rintro T T' sT sT' x y g g' rfl n n'
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique p D R b N hN hNp T' T sT' sT x y g n n'
  have hw : ∀ a, m₁.φ ≫ o.A.hom = (o'.A.hom ≫ ρ₁ a) ≫ π₁ := fun a => by
    rw [Category.assoc, hG.inv a]; exact m₁.cart.1.w
  let σ : Ga → (o'.A.left ⟶ o'.A.left) := fun a => m₁.cart.1.lift m₁.φ (o'.A.hom ≫ ρ₁ a) (hw a)
  have hσ₁ : ∀ a, σ a ≫ m₁.φ = m₁.φ := fun a => m₁.cart.1.lift_fst _ _ _
  have hσ₂ : ∀ a, σ a ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := fun a => m₁.cart.1.lift_snd _ _ _
  have hG' : GlobalTheory.ZM.IsGaloisCover Ga σ m₁.φ := hG.of_isPullback m₁.cart.1.flip hσ₂ hσ₁
  have hinv : ∀ a, σ a ≫ m₂.φ = m₂.φ := fun a => by
    obtain ⟨n⟩ := MapComp.cancel (f := ρ₁ a) (g := π₁) (objMapCongr m₁ (hG.inv a).symm) m₁
    have hn₁ : n.φ ≫ m₁.φ = m₁.φ := uniq (hG.inv a) (compose n m₁) m₁
    have hn₂ : n.φ ≫ o'.A.hom = o'.A.hom ≫ ρ₁ a := n.cart.1.w
    have hnσ : n.φ = σ a := m₁.cart.1.hom_ext (by rw [hn₁, hσ₁]) (by rw [hn₂, hσ₂])
    rw [← hnσ]
    exact uniq (show ρ₁ a ≫ (π₁ ≫ f) = π₁ ≫ f by rw [← Category.assoc, hG.inv a]) (compose n m₂) m₂
  obtain ⟨φ, hφ, -⟩ := hG'.existsUnique_desc m₂.φ hinv
  have : Epi m₁.φ := by
    have := hG'.etale; have := hG'.onto
    exact Flat.epi_of_flat_of_surjective _
  have : Epi π₁ := by
    have := hG.etale; have := hG.onto
    exact Flat.epi_of_flat_of_surjective _
  have cart : IsGrpPullback o.A u.A f φ :=
    _root_.GlobalTheory.GaloisCartDesc.isGrpPullback_of_galoisCover S S₁ Y π₁ Ga ρ₁ f o'.A o.A u.A m₁.φ m₂.φ φ hG m₁.cart m₂.cart hφ
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare cart.1.w
  have sq₂ : IsSquare m₂.φ (m₁.φ₂ ≫ φ₂) := by rw [← hφ]; exact MapComp.isSquare_comp m₁.sq sq
  have e₂ : m₂.φ₂ = m₁.φ₂ ≫ φ₂ := MapComp.isSquare_unique m₂.sq sq₂
  have hA₂ : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have := hA₂.comm
  obtain ⟨r, hr⟩ : GlobalTheory.AbLaw.Triv (o.P.pull (eSec (G2 o.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec o.A) (GlobalTheory.SquareDescent.eSec_lift_one o.A) o.rig₁
  obtain ⟨r', hr'⟩ : GlobalTheory.AbLaw.Triv (u.P.pull (eSec (G2 u.A))) :=
    GlobalTheory.AbLaw.CubeOpen.triv_comp (eSec u.A) (GlobalTheory.SquareDescent.eSec_lift_one u.A) u.rig₁
  let PA : RigLB (G2 o.A) := ⟨o.P, r, o.isLB, hr⟩
  let PB : RigLB (G2 u.A) := ⟨u.P, r', u.isLB, hr'⟩
  have c₁ : IsGrpPullback (G2 o'.A) (G2 o.A) π₁ m₁.φ₂ :=
    GlobalTheory.ShearLift.isGrpPullback_tensor m₁.cart m₁.cart m₁.sq.1 m₁.sq.2
  have c₂ : IsGrpPullback (G2 o.A) (G2 u.A) f φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor cart cart sq.1 sq.2
  have pol₂ : LBIso o'.P (u.P.pull (m₁.φ₂ ≫ φ₂)) := by rw [← e₂]; exact m₂.pol
  have pol : LBIso o.P (u.P.pull φ₂) :=
    _root_.GlobalTheory.GaloisLBDescent.lbIso_of_galoisCover S S₁ Y π₁ Ga ρ₁ f (G2 o'.A) (G2 o.A) (G2 u.A) m₁.φ₂ φ₂ PA PB o'.P hA₂ hG c₁ c₂ o'.isLB m₁.pol pol₂
  refine ⟨{ φ := φ, φ₂ := φ₂, cart := cart, sq := sq, act := fun c => ?_, pol := pol, eta := fun y => ?_ }⟩
  · rw [← cancel_epi m₁.φ, ← Category.assoc, ← m₁.act c, Category.assoc, hφ, m₂.act c, ← hφ, Category.assoc]
  · rw [← cancel_epi π₁, ← Category.assoc, ← m₁.eta y, Category.assoc, hφ, m₂.eta y, Category.assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_similitude_fixing_point_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
  ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  first | (exact @GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (exact GlobalTheory.HTQuotRigid.eq_one_of_fixes_point) | (intros; apply GlobalTheory.HTQuotRigid.eq_one_of_fixes_point  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinValueDerivativesViaJets
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

theorem GlobalTheory.HilbFam.eValue_derivs : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I) (Ch : ℍ → ℂ), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ (2 * s * Module.finrank ℚ (FR E) + 2 * ∑ i, κ i) = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * ∑ μ ∈ Finset.Iic (fun j ↦ κ (e.symm j)), ((∏ j, rco (2 * s) (κ (e.symm j)) (μ j) : ℤ) : ℂ) * (((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - Ch τ) ^ (∑ j, (κ (e.symm j) - μ j)) * hfun (2 * s) L μ Ch τ := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u Ch hf hs hN hL hφ hθ hn hLΛ hD hu
  have h1 := _root_.GlobalTheory.HilbFam.iterD_defSum_eq_jet hE E I φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hD hu
  have h2 := _root_.GlobalTheory.HilbFam.jet_conj_expand hE (FR E) hf s N L hs hN hL τ (fun j ↦ κ (e.symm j)) Ch
  have hsum : ∑ j, κ (e.symm j) = ∑ i, κ i := Equiv.sum_comp e.symm κ
  rw [hsum] at h2
  unfold wt at h2
  rw [hsum] at h2
  rw [h1, ← h2]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertTwistedLatticeJetsModularFamily
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem isFam_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  intro hE F _ _ _ hF s N L hs hN hL ι act α Ch κ hα hC
  rw [_root_.GlobalTheory.QFam.isFam_iff_values]
  intro i γ τ
  have htw : twist N L (α (act i γ)) = mulMat (twist N L (α i)) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hα]; exact _root_.GlobalTheory.HilbFam.TwistSL.twist_mul_sl F N L (α i) γ hL.2
  have h := _root_.GlobalTheory.HilbFam.hfun_slash hE F hF s N (twist N L (α i)) hs hN (_root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L (α i) hL) κ γ (Ch i)
    (Ch (act i γ)) τ ⟨_, _root_.GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L (α (act i γ)) hL, htw⟩ (hC i γ τ)
  rw [zpow_natCast]
  beta_reduce
  rw [h, htw]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeToOmegaCanonicalExtensionBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeToOmega_canonical_extension_base_change :
    ∀ (p : ℕ) [Fact p.Prime] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
      (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
      (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A (spMap (algebraMap R R')) φ),
      IsAbelianScheme A → IsAbelianScheme A' →
    ∀ (G : PDivGroup p R) (G' : PDivGroup p R') (t : G.TorsionTower A) (t' : G'.TorsionTower A')
      (ψ : PrimitiveSubmodule A →ₗ[R] G.omega) (ψ' : PrimitiveSubmodule A' →ₗ[R'] G'.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
      (∀ c : PrimitiveSubmodule A', PtExt.IsCan t' c.1 (G'.rigOfOmega (ψ' c))) →
    ∀ (c : PrimitiveSubmodule A)
      (hc : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c.1 ∈ PrimitiveSubmodule A'),
      ψ' ⟨_, hc⟩ = (t'.semiHom t (grpMor_of_isGrpPullback h)).omega (ψ c) :=
  @GlobalTheory.PtExt.psi_baseChange
end

