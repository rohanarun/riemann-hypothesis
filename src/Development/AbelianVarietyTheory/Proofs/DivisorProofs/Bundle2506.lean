module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOfDimOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreChartPointMumfordMultiplierNonz
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumMult.exists_pt_chart_of_leadPt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, GlobalTheory.MumMult.multW U b e i i')), GlobalTheory.MumMult.LeadPt U b m → ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ GlobalTheory.MumMult.multW U b 0 i i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i') := by
  intro R _ _ _ D A G _ _ U b m hL
  obtain ⟨x, hx, H⟩ := hL

  have hne : maximalIdeal R ^ (0 + 1) ≠ ⊤ := by
    rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal R).ne_top
  haveI : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1))))
  have hp : (thick R (maximalIdeal R) 0) p = (IsLocalRing.closedPoint R : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) p.asIdeal = maximalIdeal R
    refine ((maximalIdeal.isMaximal R).eq_of_le (p.isPrime.comap _).ne_top ?_).symm
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact hr)]
    exact p.asIdeal.zero_mem
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.toPre.P.A.hom)
    (g := thick R (maximalIdeal R) 0) x p (hx.trans hp.symm)
  obtain ⟨y, hy⟩ := (U.gt 0).q_surj.surj z
  refine ⟨y, ?_, ?_⟩
  · have hc := U.LG.isLB.cover
    have hmem : (fstG (maximalIdeal R) 0 G).left y ∈ (⨆ j, U.LG.L.U j) := by rw [hc]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact ⟨fun _ => j, Set.mem_iInter.2 fun _ => hj⟩
  · intro i i' hy'
    refine H y ?_ i i' hy'
    show (D.toPre.prBe (maximalIdeal R) 0).left ((U.gt 0).q.left y) = x
    rw [hy]
    exact hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closedFibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  intro R _ _ _ hR D C Y W _ _ _ T
  haveI := T.loc
  let κ : ResidueField R →+* ResidueField W := ResidueField.map T.φ
  have hκ : κ.comp (residue R) = (residue W).comp T.φ := RingHom.ext fun r => ResidueField.map_residue T.φ r
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.FormalModel.exists_carries T.hD Y.rep (T.U.gt 0)
  have gA := _root_.GlobalTheory.FormalModel.isGrpPullback_of_carries T.hD T.U.toUnifPre Y hφ₀
  have hle : maximalIdeal W ^ (0 + 1) ≤ RingHom.ker (residue W) := by
    rw [zero_add, pow_one, ker_residue]
  let c : W ⧸ maximalIdeal W ^ (0 + 1) →+* ResidueField W :=
    Ideal.Quotient.lift _ (residue W) fun a ha => (RingHom.mem_ker).1 (hle ha)
  have hc : spMap c ≫ thick W (maximalIdeal W) 0 = spMap (residue W) := by
    rw [show thick W (maximalIdeal W) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have hc' : spMap c ≫ thick W (maximalIdeal W) 0 ≫ spMap T.φ = spMap κ ≫ spMap (residue R) := by
    rw [← Category.assoc, hc, ← spMap_comp, ← spMap_comp, hκ]
  let P := (Over.pullback (spMap c)).obj (thickObj W (maximalIdeal W) 0 T.G)
  have g1 : IsGrpPullback P T.G (spMap (residue W))
      (pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0)) :=
    ((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback T.G (thick W (maximalIdeal W) 0))).congr hc rfl
  obtain ⟨e1, he1, he1'⟩ := grpPullback_iso g1 (isGrpPullback_pullback T.G (spMap (residue W)))
  have g2 : IsGrpPullback P Y.H (spMap κ ≫ spMap (residue R)) (pullback.fst _ _ ≫ φ₀) :=
    ((isGrpPullback_pullback _ (spMap c)).comp gA).congr hc' rfl
  have g3 := (isGrpPullback_pullback ((Over.pullback (spMap (residue R))).obj Y.H) (spMap κ)).comp
    (isGrpPullback_pullback Y.H (spMap (residue R)))
  obtain ⟨e2, he2, he2'⟩ := grpPullback_iso g2 g3
  refine ⟨κ, e1.symm ≪≫ e2, hκ, ?_, ?_⟩
  · haveI := he1; haveI := he2
    show IsMonHom (e1.inv ≫ e2.hom)
    infer_instance
  · intro Z p p' y hp hy
    have i1 : e1.inv.left ≫ pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) =
        pullback.fst T.G.hom (spMap (residue W)) := by
      rw [← he1', ← Category.assoc, ← Over.comp_left, e1.inv_hom_id, Over.id_left, Category.id_comp]
    let g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left := p ≫ e1.inv.left ≫ pullback.fst _ _
    have hy' : y = g ≫ φ₀ := by
      rw [hy]
      have := he2'
      simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc, g]
      rw [this]
    subst hy'
    obtain ⟨ξ', h1, h2⟩ := _root_.GlobalTheory.Mum.isPullPt_of_carries T.hD T.U.toUnifPre Y hφ₀ Z g
    refine ⟨g, ξ', ?_, h1, h2⟩
    rw [hp]
    show (p ≫ e1.inv.left ≫ pullback.fst _ _) ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) = _
    rw [Category.assoc, Category.assoc, i1]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurface
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open _root_.CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveClosure

theorem exists_closure_arith_surface_rat : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∃ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ p) 1 ∧ z ≫ w = redι Z ≫ ratFibre.fst p ∧ IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
  intro k _ X p D hX Z hZ
  have := hX.isIntegral
  have := hX.finite
  let S : Closeds X := ⟨closure (ratFibre.fst p '' (Z : Set (ratFibre p))), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set X) :=
    (hZ.isIrreducible.image _ (ratFibre.fst p).continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (Int.castRingHom ℚ)) :=
    IsPreimmersion.of_isLocalization (R := ℤ) (S := ℚ) (nonZeroDivisors ℤ)
  haveI : IsPreimmersion (ratFibre.fst p) :=
    MorphismProperty.of_isPullback (ratFibre.isPullback p).flip inferInstance
  have hpb0 := (IsPullback.of_hasPullback w (ratFibre.fst p)).paste_vert (ratFibre.isPullback p)
  rw [← Category.assoc] at hpb0
  have hpb1 : IsPullback (pullback.fst w (ratFibre.fst p)) (pullback.snd w (ratFibre.fst p) ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := hpb0
  haveI : IsReduced (pullback ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isReduced_pullback_localization ℤ ℚ (nonZeroDivisors ℤ) _ _
  haveI : IsReduced (pullback w (ratFibre.fst p)) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w (ratFibre.fst p)) = (Z : Set (ratFibre p)) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change ratFibre.fst p ⁻¹' closure (ratFibre.fst p '' (Z : Set (ratFibre p))) = _
    rw [← (ratFibre.fst p).isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w (ratFibre.fst p)) Z hrange
  have hzw : (e.hom ≫ pullback.fst w (ratFibre.fst p)) ≫ w = redι Z ≫ ratFibre.fst p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w (ratFibre.fst p)) (redι Z ≫ ratFibre.snd p)
      ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : ℚ →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ ratFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w (ratFibre.fst p)).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  haveI : IsProper (w ≫ p) := by
    obtain ⟨N, i, _, hi⟩ := hproj
    have := isProper_str k N
    exact hi ▸ inferInstance
  haveI : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hX.finite
  haveI : Flat ((w ≫ p) ≫ spMap (Int.castRingHom k)) := (flat_int_iff_charZero _).2 hcW
  have hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal S).subscheme = (1 + 1 : ℕ) :=
    IntModel.topologicalKrullDim_eq_succ (O := ℤ) (K := ℚ) Int.not_isField hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w (ratFibre.fst p), inferInstance, hX.of_isClosedImmersion w hcW hdim,
    hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclesOmega
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.exists_cocycles_omega : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c),
    ∃ (z : G.cocycles) (w : G.omega), (∀ n, z.1 n = d.coc n) ∧ ∀ n, w.1 n = d.om n := by
  intro R _ A _ hA p G t c d
  have hs : IsSymCoc d.g := isSymCoc_of_isAdd R A hA _ _ d.add
  refine ⟨⟨fun n => d.coc n, fun n => ⟨coc_mem_symCocycles R A p G t c d hs n,
    Dat.pullTwo_res_coc R A p G t c d n⟩⟩, ⟨fun n => d.om n, fun n => OmRes.cotMap_res_om R A p G t c d n⟩,
    fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorRationalSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.Denom

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem exists_sec_tens {L M : LB Y} (hL : L.IsLB) (hM : M.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) (u : M.Sec) (hu : genericPoint Y ∈ nonzeroLocus u)
    (hE : (divOfRatSec hL hr + divOfSec hM u hu).Eff) :
    ∃ (t : (tens L M).Sec) (ht : genericPoint Y ∈ nonzeroLocus t), ∀ i j, genericPoint Y ∈ L.U i →
      genericPoint Y ∈ M.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j := by
  have P := (presents_divOfRatSec hL hr).tens (presents_divOfRatSec hM (isRatSec_ratOfSec u hu))
  obtain ⟨t, ht⟩ := P.exists_rat_eq (f := 1) (CartierDiv.mem_sections.2 fun x => hE x)
  have hη : genericPoint Y ∈ nonzeroLocus t :=
    (P.generatesAt_rat_iff t).1 (ht ▸ CartierDiv.generatesAt_genericPoint _ one_ne_zero)
  refine ⟨t, hη, fun i j hi hj => Units.ext ?_⟩
  have e := P.rat_mul t (i, j) ⟨hi, hj⟩
  rw [ht, one_mul] at e
  rw [val_ratOfSec (show genericPoint Y ∈ (tens L M).U (i, j) from ⟨hi, hj⟩), ← e]

theorem gen_mem_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m) := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  have hj : genericPoint Y ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  refine (mem_nonzeroLocus_iff _ _ hj).2 ((unitAt_fnOf_iff hj hj _).1 (unitAt_genericPoint ?_))
  show fnOf _ hj (resG Y _ (t.f i) ^ m) ≠ 0
  rw [map_pow, fnOf_resG]
  exact pow_ne_zero _ (fnOf_sec_ne_zero ht hi)

theorem divOfSec_secPow {L : LB Y} (hL : L.IsLB) (t : L.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    (m : ℕ) (hm : genericPoint Y ∈ nonzeroLocus (Cartier.secPow t m)) :
    divOfSec (isLB_lbPow hL m) (Cartier.secPow t m) hm = m • divOfSec hL t ht := by
  refine CartierDiv.ext_of_isEqn fun x => ?_
  obtain ⟨i, hi⟩ := exists_chart hL x
  have hj : x ∈ (lbPow L m).U (fun _ => i) := (lbPow_U L m _).ge hi
  have e : ratOfSec (Cartier.secPow t m) hm (fun _ => i) = ratOfSec t ht i ^ m := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hi), val_ratOfSec (gen_mem hj)]
    show fnOf _ (gen_mem hj) (resG Y _ (t.f i) ^ m) = _
    rw [map_pow, fnOf_resG]
  refine ⟨ratOfSec t ht i ^ m, ?_,
    ((presents_divOfRatSec hL (isRatSec_ratOfSec t ht)).isEqn i x hi).nsmul m⟩
  rw [← e]
  exact (presents_divOfRatSec (isLB_lbPow hL m) (isRatSec_ratOfSec _ hm)).isEqn _ x hj

theorem exists_open_regularAt {L : LB Y} (hL : L.IsLB) {r : L.ι → Y.functionFieldˣ}
    (hr : IsRatSec L r) :
    ∃ W : Y.Opens, genericPoint Y ∈ W ∧ ∀ x ∈ W, (divOfRatSec hL hr).RegularAt x 1 := by
  obtain ⟨i, hi⟩ := exists_chart hL (genericPoint Y)
  obtain ⟨U, hU, a, ha⟩ := (regAt_genericPoint (r i : Y.functionField)).exists_fnOf
  refine ⟨L.U i ⊓ U, ⟨hi, hU⟩, fun x hx => ?_⟩
  refine ((presents_divOfRatSec hL hr).isEqn i x hx.1).regularAt_iff.2 ?_
  rw [one_mul, ← ha]
  exact regAt_fnOf hx.2 _ a

end GlobalTheory.MixHt.Denom


open GlobalTheory.MixHt.Denom in
theorem GlobalTheory.MixHt.exists_common_denom : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r →
    IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec)
    (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t)
    (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i →
    genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧
      ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  intro k _ Y _ q hq N r r' hr hr'
  obtain ⟨n₀, j, hj, hjq⟩ := hq.isProjOver
  let H₀ : HermLB (PSpace.str k n₀) :=
    .fs _ (isAmple_projective_O_one k n₀).isLB (ProjSpace.coord k n₀)
      (ProjSpace.iSup_nonzeroLocus_coord k n₀) (fun _ => 1) (fun _ => by simp)
      (fun _ => ⟨1, one_mem _, by rw [mul_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩)
  let H : HermLB q := H₀.pull j hjq
  have hH : IsAmpleLB H.B := (isAmple_projective_O_one k n₀).pull_of_isClosedImmersion j
  haveI := hH.compactSpace
  obtain ⟨W, hW, hWr⟩ := exists_open_regularAt N.isLB hr
  obtain ⟨W', hW', hWr'⟩ := exists_open_regularAt N.isLB hr'
  obtain ⟨n, -, t, ht, hle, -⟩ :=
    hH.exists_affine_le (x := genericPoint Y) (U := W ⊓ W') ⟨hW, hW'⟩
  have hL := isLB_lbPow H.isLB n
  obtain ⟨N₁, h₁⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr x (hle hx).1
  obtain ⟨N₂, h₂⟩ := EffDiff.eventually_eff_add_nsmul hL t ht _ fun x hx => hWr' x (hle hx).2
  have hu := gen_mem_secPow hL t ht (max N₁ N₂)
  have hD := divOfSec_secPow hL t ht (max N₁ N₂) hu
  obtain ⟨s, hs, e⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₁ _ (le_max_left _ _))
  obtain ⟨s', hs', e'⟩ := exists_sec_tens N.isLB (isLB_lbPow hL _) hr' (Cartier.secPow t (max N₁ N₂)) hu
    (by rw [hD]; exact h₂ _ (le_max_right _ _))
  exact ⟨(H.pow n).pow (max N₁ N₂), Cartier.secPow t (max N₁ N₂), s, s', hu, hs, hs',
    fun i j hi hj => ⟨e i j hi hj, e' i j hi hj⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.HessKer

open ReciprocityTheory.L2DbarEstimates (V cHess bas)

theorem exists_vecMul_eq_zero {D D' : ℕ} (h : D' < D) (P : Matrix (Fin D) (Fin D') ℂ) :
    ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ Matrix.vecMul ξ P = 0 := by
  have hk : LinearMap.ker P.vecMulLinear ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨ξ, hξ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨ξ, h0, by simpa using hξ⟩

theorem exists_common_kernel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  intro k _ X Y p q σ D D' hD π hπ c c' y hy hy0
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D → V D' := c.e ∘ m ∘ c'.e.symm with hFdef
  set U := c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)
  have hU : IsOpen U := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c'.e y ∈ U := mem_over c'.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c' c
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c'.e y) = c.e (m y) := by
    simp only [hFdef, Function.comp_apply, c'.e.left_inv hy]
  obtain ⟨ξ, hξ, hP⟩ := exists_vecMul_eq_zero hD (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b)
  refine ⟨ξ, hξ, fun A i hi => ?_⟩
  have him : m y ∈ ptsIn p σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D' → ℂ := fun v => (A.φ.φ (i PUnit.unit) (c.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c'.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (A.cInf.contDiffAt c hy0 him)
  have e : (fun v => ((A.pull π hπ).φ.φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ A.φ π hπ i (c'.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c.e.left_inv hv.2]
    exact congrArg _ this
  have key : c'.hess (A.pull π hπ).φ i y =
      (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b) * (cHess D' g (F (c'.e y)) *
        Matrix.of fun a l => (starRingEnd ℂ) (fderiv ℂ F (c'.e y) (bas D l) a)) := by
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ← Matrix.mul_assoc]
    ext j l
    rw [GlobalTheory.HessPull.cHess_comp_apply D D' g F U hU _ hyU hF hg j l, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, ← Matrix.vecMul_vecMul, hP, Matrix.zero_vecMul]

end GlobalTheory.HessKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRLocalEmbeddingNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.CompleteNormalDvr

theorem exists_dvr_isCN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j := by
  intro R _ _ _ hR
  obtain ⟨h1, h2, h3, h4⟩ := hR
  obtain ⟨V, _, _, _, φ, hV, hφ, hloc⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating R
  obtain ⟨g1, g2, g3⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  refine ⟨V, inferInstance, inferInstance, inferInstance, g1, φ, ?_, hφ, hloc⟩
  exact ⟨inferInstance, inferInstance, g2, g3⟩

end GlobalTheory.CompleteNormalDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrWithProportionalValuations
section
open IsLocalRing

namespace GlobalTheory.PropDvr

theorem exists_cdvr_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (I : Type) [Finite I] (a : I → R) (k : I → ℕ), (∀ i, Associated (ψ (a i)) (ϖ ^ k i)) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W) (ψ' : R →+* W) (m m' : ℕ) (k' : I → ℕ), IsAdicComplete (maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧ IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧ ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  first
  | exact @_root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | (apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main ..)

end GlobalTheory.PropDvr
end

