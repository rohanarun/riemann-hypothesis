module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRefinedDegenerationDataFiniteExtensionLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.SharpExt

theorem spMap_comp_ext {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_refined_ext_lift : ∀ g n : ℕ, ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), Module.finrank ℤ Q.X ≤ g → (∀ k, t k ∈ maximalIdeal V ∧ t k ≠ 0) → (∀ k a b, δ k a b = δ k b a) → (∀ k a, 0 ≤ δ k a a) → (∀ a, a ≠ 0 → ∃ k, 0 < δ k a a) → Q.IsMonomialTau t δ → ∀ ξ : Sp V ⟶ Z, UnifOver F i ξ Q → ∀ (Y : Scheme.{0}) (q : Y ⟶ F.X), IsFinite q → Surjective q → ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V →+* V₁) (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X) (y : Sp (FractionRing V₁) ⟶ F.X) (y' : Sp (FractionRing V₁) ⟶ Y), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ Refines Q ρ D₀.toPre e₀ ∧ y ≫ i = jK V₁ ≫ spMap ρ ≫ ξ ∧ y' ≫ q = y := by
  intro g n F Z i W hW V _ _ _ Q m t δ hrk ht hsym hnn hpos hmono ξ hU Y q hq hs
  obtain ⟨V₀, _, _, _, ρ₀, r, D₀, e₀, hCN₀, hinj₀, hfin₀, -, -, hRef₀, -⟩ :=
    GlobalTheory.PolDeg.refine_monomial_of_polarised V Q m t δ hU.1 hmono (fun k => (ht k).1) (fun k => (ht k).2) hsym hnn hpos
  obtain ⟨G', _, _, A', U', y₀, α, α₂, -, hy₀, -⟩ := hU.2 V₀ ρ₀ hCN₀ hinj₀ hfin₀ D₀ e₀ hRef₀
  obtain ⟨L, _, _, _, yL, hyL⟩ := _root_.GlobalTheory.FinLift.lift_point_finite_surjective (FractionRing V₀) F.X Y y₀ q hq hs
  obtain ⟨V₁, _, _, _, ρ, σ, hCN₁, hinj, hfin, hloc, hσ⟩ := _root_.GlobalTheory.Poinc.exists_integralClosure_isCN_finite_local V₀ hCN₀ L
  haveI : IsNoetherianRing V₀ := hCN₀.1
  have hR : AdmBase V₀ (maximalIdeal V₀) := ⟨hCN₀.1, inferInstance, hCN₀.2.1, hCN₀.2.2.1⟩
  obtain ⟨Wo, hWo, hψ⟩ := GlobalTheory.psiOnExists V₀ _ hR D₀
  have hgen : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) ∈ Wo := by
    have : (specOf ρ).base (genericPoint (Spec (CommRingCat.of V₁))) = genericPoint (Spec (CommRingCat.of V₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective ρ hinj)
    rw [this]; exact hWo
  obtain ⟨D₁, hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg GlobalTheory.polBaseChange_holds GlobalTheory.globalFns_holds V₀ V₁ _ _ ρ
    (map_maximalIdeal_le ρ) D₀ Wo hψ hgen
  have hfr : GlobalTheory.Mum.GenDesc.fracMap ρ hinj = σ.comp (algebraMap (FractionRing V₀) L) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V₀) (RingHom.ext fun x => ?_)
    simp [GlobalTheory.Mum.GenDesc.fracMap_algebraMap, hσ]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, ρ.comp ρ₀, D₁, hD.xe.trans e₀,
    spMap (GlobalTheory.Mum.GenDesc.fracMap ρ hinj) ≫ y₀, spMap σ ≫ yL, hCN₁, hinj.comp hinj₀, hfin.comp hfin₀,
    _root_.GlobalTheory.RefPull.refines_pull Q ρ₀ D₀.toPre e₀ hinj₀ hRef₀ ρ D₁.toPre hD hinj, ?_, ?_⟩
  · rw [Category.assoc, hy₀, spMap_comp_ext ρ₀ ρ]
    simp only [Category.assoc]
    rw [← Category.assoc (jK V₁) (spMap ρ), GlobalTheory.Mum.GenDesc.jK_comp_spMap ρ hinj]
    simp only [Category.assoc]
  · rw [Category.assoc, hyL, hfr, spMap_comp_ext]
    simp only [Category.assoc]

end GlobalTheory.Poinc.Sep.SharpExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOrigin
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_left_origin {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) : f.hom.left A.origin = B.origin := by
  have e : (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X) ≫ f.hom = 1 := by
    rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  unfold origin
  rw [← e, Over.comp_left]
  rfl

theorem exists_sec_pull_ample_vanish_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧
      cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  intro K _ A B f d hd hf
  obtain ⟨L, hL, amp, rfl⟩ := hd
  obtain ⟨N, hN, M, t, h0, h1⟩ := GlobalTheory.T.exists_ampleSections_vanishing_origin_separating K B L hL amp
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.AV.AbVar.exists_apply_ne_origin K A B f hf
  let ιB := (B.X.hom ⁻¹ᵁ ⊤).ι
  let h : A.X.left ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift ιB f.hom.left (by
    rw [Scheme.Opens.range_ι]; intro x _; trivial)
  have hh : h ≫ ιB = f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ x, ιB (h x) = f.hom.left x := fun x => by rw [← hh]; rfl
  obtain ⟨j, hj⟩ := h1 (h a) (by rw [hpt]; exact ha)
  let s := ReciprocityTheory.ChartRestriction.G.DVR.pullSec L (fun _ : Fin N => ιB) (fun _ => 1) (t j) h
  have hs : Out.nonzeroLocus s = h ⁻¹ᵁ Out.nonzeroLocus (t j) := GlobalTheory.nonzeroLocus_pullSec _ _ (t j) h
  refine ⟨N, _, LB.isLB_linComb hL _ _, s, hN, ?_, ?_, ?_⟩
  · rw [cls_linComb hL]
    simp only [hh, one_zsmul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro e
    have : a ∈ Out.nonzeroLocus s := by rw [hs]; exact hj
    rw [e] at this; exact this
  · intro ho
    rw [hs] at ho
    exact h0 j (h A.origin) (by rw [hpt, hom_left_origin]) ho

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.GenFibreGen

theorem nefFib_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ), NefFib L → NefFib (L.pow n) := by
  intro k _ X _ p D hX L n hL
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have htriv : NefFib (HermLB.triv p) := by
      intro Z i _ _ κ _ _ _ _
      exact (interNum_eq_zero_of_cls_eq_zero κ _
        (fun _ => LB.isLB_pull (LB.isLB_triv X) i) 0
        (by rw [CechPic.cls_pull (LB.isLB_triv X)]; exact map_zero _)).ge
    refine AmpleTwistNef.nefFib_of_cls_eq ?_ htriv
    erw [CechPic.cls_lbPow L.isLB 0, zero_smul]
    rfl
  · have := hX.finite
    exact (nefFib_pow_iff k X p hX.isProjOver L n hn).2 hL

theorem exists_fst_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (x : X), CharZero (X.residueField x) → ∃ y : ↥(Limits.pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))), Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) y = x :=
  fun k _ X p x hx => RatDegZeros.mem_range_fst k X p x hx

theorem isProjOver_snd {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) : IsProjOver (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) := by
  have := h.finite
  have := h.isIntegral
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 h.finite
  obtain ⟨_, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 h.isProjOver
  have hP : IsProjOver (p ≫ spMap (Int.castRingHom k)) := hL.isProjOver _
  exact ProjSpace.isProjOver_pullback_snd (Int.castRingHom ℚ) hP

theorem exists_secs_generic : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → IsAmpleLB A.B → ∃ (m : ℕ) (N : ℕ) (s : Fin N → (((L.pow n).tens A).pow m).B.Sec), 1 ≤ m ∧ ∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro hNN k _ X _ p D hX L A n hL hA
  have hN := GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres k X p D hX (L.pow n) (nefFib_pow k X p D hX L n hL)
  have : IsAffineHom (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hA' : IsAmpleLB (A.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))) :=
    hA.pull_of_isAffineHom _
  have hK := IsAmpleLB.tens_of_isNef hNN ℚ _ _ (isProjOver_snd hX) _ _ hA' hN
  obtain ⟨m, hm, N, t, ht⟩ := hK.exists_isGenerated_pow
  have hM := pull_isLB (((L.pow n).tens A).pow m).isLB (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq _ _ _ (isLB_lbPow hK.isLB m) hM (by
      rw [CechPic.cls_lbPow hK.isLB m, CechPic.cls_pull (((L.pow n).tens A).pow m).isLB _ hM]
      erw [CechPic.cls_lbPow ((L.pow n).tens A).isLB m]
      rw [map_nsmul]
      congr 1
      erw [CechPic.cls_tens (pull_isLB A.isLB _) (pull_isLB (L.pow n).isLB _), CechPic.cls_tens (L.pow n).isLB A.isLB]
      rw [map_add (f := _), CechPic.cls_pull A.isLB, CechPic.cls_pull (L.pow n).isLB, add_comm]) (Fin N) t ht
  choose s hs using fun i => _root_.GlobalTheory.GenSecInt.main k X p D hX _ (((L.pow n).tens A).pow m).isLB (v i)
  refine ⟨m, N, s, hm, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := exists_fst_eq k X p x hx
  have hy : y ∈ ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (v i) := hv ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  exact ⟨i, (hs i y).2 hi⟩

end GlobalTheory.GenFibreGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_symE_pCrd : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∃ e : Fin (N + 1) → Ω, SymE ρ m e ∧ ∀ (h : Sp Ω ⟶ PSpace (cycAway n) N), h = spMap (algebraMap S.R Ω) ≫ u ≫ f → PCrd h e := by
  intro g n _ _ _ F W _ P rig m N f hT o Ω _ _ _ hA β S ρ u hS
  obtain ⟨hPg, hPs, hrig, hm, -, hmu, hN, -, hf, -⟩ := hT
  obtain ⟨-, -, hSg, hρs, -⟩ := hS
  haveI : CharZero Ω := hA.char
  have hSB : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  let v : S.R →+* Ω := S.R.val.toRingHom

  obtain ⟨P₀, φ, hg₀, hφ, hL₀⟩ := exists_isPolFibre polBaseChange_holds v ρ.P
  have hφ' : IsGrpPullback P₀.A ρ.P.A (spMap v ≫ 𝟙 (Sp S.R)) φ := by
    simpa using hφ
  have hL₀' : LBIso P₀.L (ρ.P.L.pull φ) := hL₀.symm
  have hfib : PolFib ρ.P.A ρ.P.L (8 * g) (spMap v ≫ 𝟙 (Sp S.R)) :=
    ⟨P₀, φ, by rw [hg₀, ρ.g_eq, hSg], hφ', hL₀'⟩

  have hth : IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := fun s =>
    (ρ.th₁_basis s).exists.elim fun r h => ⟨r 0, fun j => (h j).trans (Fin.sum_univ_one _)⟩
  let θ : SecAt ρ.P.A ρ.P.L (spMap v ≫ 𝟙 (Sp S.R)) := SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ v
  have : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap v ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Spec _))
  have hθ : IsGenSec ρ.P.A ρ.P.L _ θ := GlobalTheory.EmbPull.isGenSec_pullS ρ.P hSB _ hth

  obtain ⟨e, he⟩ := _root_.GlobalTheory.UMin.SymRat.symAt_exists (Sp S.R) ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen (8 * g) m (N + 1) Ω
    (spMap v ≫ 𝟙 (Sp S.R)) θ hm hN hfib
  have hmΩ : (m : Ω) ≠ 0 := by
    let κ : cycAway n →+* S.R := (Spec.preimage (u ≫ F.s)).hom
    have := (hmu.map κ).map v
    rw [map_natCast, map_natCast] at this
    exact this.ne_zero
  refine ⟨e, ⟨by rw [hSg]; exact hN, hmΩ, he⟩, fun h hh => ?_⟩

  obtain ⟨ψ, hψ, hLψ⟩ := _root_.GlobalTheory.Poinc.sharpOver_unique g n F W ρ.P P u (𝟙 F.X) u (Category.comp_id u) hρs hPs
  have hα : IsGrpPullback P₀.A P.A ((spMap v ≫ u) ≫ 𝟙 F.X) (φ ≫ ψ) := by
    simpa using hφ.comp hψ
  have hLα : LBIso P₀.L (P.L.pull (φ ≫ ψ)) :=
    LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB φ) (pull_isLB P.isLB _) hL₀'
      (LBIso.trans (pull_isLB ρ.P.isLB φ) (pull_isLB (pull_isLB P.isLB ψ) φ) (pull_isLB P.isLB _)
        (RigidBundleGlue.LBIso.pull hLψ φ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp P.isLB ψ φ).symm)
  have key := _root_.GlobalTheory.UMin.pCrd_of_symAt F.X P.A P.L rig P.isLB hrig (8 * g) m N (cycAway n) F.X (𝟙 F.X) f (Sp S.R) ρ.P.A ρ.P.L ρ.rig
    Ω (spMap v ≫ u) (spMap v ≫ 𝟙 (Sp S.R)) P₀ (φ ≫ ψ) φ θ e hm hN hf ρ.P.isLB ρ.rig_gen
    (by rw [hg₀, ρ.g_eq, hSg]) hα hLα hφ' hL₀' hθ he
  rw [hh, show algebraMap S.R Ω = v from RingHom.ext fun _ => rfl]
  simpa [Category.assoc] using key

end GlobalTheory.SiegTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.MapAff

theorem theta_map_aff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  intro S G _ _ L ρ hL hρ g m n o R _ _ _ _ _ _ β x θ hm hm3 hmu hn hpol hgen
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UMin.SymRing.sym_ring S G L ρ hL hρ g m (n + 1) R x θ hm hmu hn hpol
  have hpolK : ∀ (K : Type) [Field K] (i : R →+* K), PolFib G L g (spMap i ≫ x) := fun K _ i =>
    (_root_.GlobalTheory.UMin.FibMove.polFib_move S S G L G L (𝟙 S) (𝟙 G.left) hL hL (GlobalTheory.SiegLower.isGrpPullback_id G)
      (GlobalTheory.SiegLower.lbIso_pull_id hL) g R x).2 K i hpol
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    letI := Ideal.Quotient.field M
    let i : R →+* AlgebraicClosure (R ⧸ M) := (algebraMap (R ⧸ M) (AlgebraicClosure (R ⧸ M))).comp (Ideal.Quotient.mk M)
    have hmK : ((m : ℕ) : AlgebraicClosure (R ⧸ M)) ≠ 0 := by
      have := hmu.map i
      rw [map_natCast] at this
      exact this.ne_zero
    have hpK := hpolK _ i
    obtain ⟨pt, c, hl⟩ := _root_.GlobalTheory.UMin.exists_thList S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) (SecAt.pull G L θ i) hm hmK hn hpK
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.UMin.ThNe.th_ne_zero S G L ρ hL hρ g m (n + 1) _ (spMap i ≫ x) c hm hm3 hmK hpK ⟨_, pt, hgen _ i, hl⟩
    obtain ⟨j, hj⟩ := GlobalTheory.UMin.symTup_basic.2.2.2 _ (n + 1) c ⟨a, ha⟩
    apply hj
    rw [← he _ i pt c hl j]
    have hM' : e j ∈ M := hle (Ideal.subset_span ⟨j, rfl⟩)
    simp [i, Ideal.Quotient.eq_zero_iff_mem.2 hM']
  have hstr : GlobalTheory.ProjSpace.pt β e hspan ≫ PSpace.str o n = spMap β := by
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C β e r
  have hf : PCrd (GlobalTheory.ProjSpace.pt β e hspan) e := (GlobalTheory.UMin.CrdUniq.pCrd_iff _ β hstr e).2 ⟨hspan, rfl⟩
  refine ⟨GlobalTheory.ProjSpace.pt β e hspan, hstr, ?_⟩
  intro K _ x' c ⟨θ', pt, hθ', hl⟩
  obtain ⟨i, rfl⟩ := GlobalTheory.UMin.CrdUniq.exists_spMap' x'
  obtain ⟨r, hr⟩ := hθ' (SecAt.pull G L θ i)
  have hsm : SecM.ofSec G (SecAt.pull G L θ i) = r • SecM.ofSec G θ' := Subtype.ext (funext hr)
  set a : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r with ha
  have hra : GlobalTheory.ZH.fn a = r := by
    simp [GlobalTheory.ZH.fn, a]
  have hl0 : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => a * c b) := by
    refine ⟨hl.1, fun b => ?_, hl.2.2⟩
    have h1 := GlobalTheory.Ex.OneGen.ThG.smul hL hsm (hl.2.1 b)
    convert h1 using 1
    rw [← hra]
    exact map_mul _ _ _
  have h2 : PCrd (spMap i ≫ GlobalTheory.ProjSpace.pt β e hspan) (fun j => a ^ (n + 1).factorial * symTup c j) := by
    have := _root_.GlobalTheory.UMin.CrdBasic.pCrd_basic.1 o R K n _ e i hf
    convert this using 2 with j
    rw [he K i pt _ hl0 j, GlobalTheory.UMin.symTup_basic.1]
  have ha0 : a ≠ 0 := by
    rintro h0
    obtain ⟨j, hj⟩ := (_root_.GlobalTheory.UMin.CrdBasic.pCrd_basic.2.2 o K n _).2 _ h2
    apply hj
    simp [h0, Nat.factorial_ne_zero]
  have h3 := _root_.GlobalTheory.UMin.CrdBasic.pCrd_basic.2.1 o K n _ _ ((a ^ (n + 1).factorial)⁻¹) (isUnit_iff_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ha0))) h2
  convert h3 using 1
  funext j
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha0)]

end GlobalTheory.UMin.MapAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaWitnessesBaseChangeMemberStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep.BaseTerms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_witnesses_baseChange_member : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z)
    (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X]
      (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type)
      (lab : C → X₁.S.Gam)
      (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1)
      (w₀ : W0 𝔪.U.toUnifPre) (s : Fam 𝔪.D.toPre (FractionRing V) 1) (g' : C → GtPtF 𝔪.D.toPre (FractionRing V))
      (w : ∀ c, GlobalTheory.UT.Frm 𝔪.D.toPre (FractionRing V) 1 (g' c).b),
      (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
      (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
        Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
          val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
      (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
      𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
      (∀ c, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero) ∧ (w c).IsGen ∧
        𝔪.Over' w₀ (g' c) (w c) (x (lab c)) (fr (lab c))) →
    ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V') (f : FractionRing V →+* FractionRing V'),
      (∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v)) → Function.Injective io → io.Finite →
    ∀ (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (𝔪₂ : UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ)
      (ψ : 𝔪₂.A.A.left ⟶ 𝔪.A.A.left) (hD : IsPullDeg io 𝔪.D.toPre 𝔪₂.D.toPre)
      (bc : 𝔪₂.G ≅ (Over.pullback (spMap io)).obj 𝔪.G), 𝔗.Ext ev io ev₂ → 𝔪₂.yK.comp 𝔗.om = f.comp 𝔪.yK →
      IsGrpPullback 𝔪₂.A.A 𝔪.A.A (spMap f) ψ → ∀ (wψ : LB.Iso 𝔪₂.A.L (𝔪.A.L.pull ψ)), wψ.IsGen →
      𝔪₂.φ ≫ 𝔗.φ = ψ ≫ 𝔪.φ → IsMonHom bc.hom → IsPullUnif io hD bc 𝔪.U 𝔪₂.U →
      (∀ mu, hD.xe (𝔪₂.e₈ mu) = 𝔪.e₈ mu) →
      𝔪₂.U.gen.hom.left ≫ ψ ≫ 𝔪.U.gen.inv.left ≫ pullback.fst 𝔪.G.hom (jK V) =
        pullback.fst 𝔪₂.G.hom (jK V') ≫ bc.hom.left ≫ pullback.fst 𝔪.G.hom (spMap io) →
    ∀ (x₂ : 𝔗.X₂.S.Gam → (TFK (R := V') (FractionRing V') ⟶ 𝔪₂.A.A)) (fr₂ : ∀ a, FrAt (x₂ a)),
      (∀ a, (x₂ a).left ≫ 𝔪₂.φ = spMap 𝔪₂.yK ≫ (𝔗.X₂.ρ.pt a).left) →
      (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good 𝔗.X₂.ρ.P.L z J → Good 𝔪₂.A.L z J' →
        Geo.Tor.gw 𝔪₂.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪₂.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
          val (𝔗.X₂.ρ.fr a) (show (TFK (R := V') (FractionRing V')).left ⟶ (baseOver (Sp 𝔗.X₂.S.R)).left from spMap 𝔪₂.yK) z J) →
    ∀ ρ : X₁.S.Gam → (FractionRing V')ˣ, (∀ b, FrPull wψ f (x₂ (𝔗.lam b)) (fr₂ (𝔗.lam b)) (x b) (fr b) (ρ b)) →
    ∃ (th₂ : SecA 𝔪₂.A (FractionRing V') 1) (w₀₂ : W0 𝔪₂.U.toUnifPre) (s₂ : Fam 𝔪₂.D.toPre (FractionRing V') 1)
      (g'₂ : C → GtPtF 𝔪₂.D.toPre (FractionRing V')) (w₂ : ∀ c, GlobalTheory.UT.Frm 𝔪₂.D.toPre (FractionRing V') 1 (g'₂ c).b)
      (K : FractionRing V'),
      (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪₂.yK ⟨𝔗.X₂.S.th a, 𝔗.X₂.S.th_mem a⟩)) ∧ w₀₂.IsGen ∧
      𝔪₂.U.ExpandsF (FractionRing V') 1 w₀₂ th₂ s₂ ∧
      (∀ c, (∃ o, GtPtF.IsNsmul (𝔗.X₂.S.r * 𝔗.X₂.S.N) (g'₂ c) o ∧ o.IsZero) ∧ (w₂ c).IsGen ∧
        𝔪₂.Over' w₀₂ (g'₂ c) (w₂ c) (x₂ (𝔗.lam (lab c))) (fr₂ (𝔗.lam (lab c)))) ∧
      (∀ mu c, coef s₂ (g'₂ c) (w₂ c) (𝔪₂.e₈ mu) * (ρ (lab c) : FractionRing V') = K * f (coef s (g' c) (w c) (𝔪.e₈ mu))) ∧
      ∀ b, 𝔪₂.yK ⟨𝔗.X₂.S.th (𝔗.lam b), 𝔗.X₂.S.th_mem _⟩ * (ρ b : FractionRing V') = K * f (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩) := by
  first | exact @GlobalTheory.TermsMove.exists_witnesses | exact GlobalTheory.TermsMove.exists_witnesses | (intros; apply GlobalTheory.TermsMove.exists_witnesses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToroidalCanonicalBundleWeightLineStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toroidalCanonicalBundle_weight_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (K : CanonLB (s₀ TF.Y Z) Dw.dim), ∃ (κ : LB (X₀ TF.Y Z)) (hκ : κ.IsLB), CechPic.pull (π₀ TF.X Z) (cls κ hκ) = cls (L₀ TF.X Z (kapBase Dw)) (isLB_L₀ TF.X Z _) ∧ ∃ θ : (LB.div κ K.bundle).Sec, nonzeroLocus θ = (j₀ TF.Y Z).opensRange := by
  first | exact @GlobalTheory.LogCanon.exists_kap_theta | exact GlobalTheory.LogCanon.exists_kap_theta | (intros; apply GlobalTheory.LogCanon.exists_kap_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameEqConstMulIntegralGeneratorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ N : ℕ, 1 ≤ N → ∃ l : FractionRing V, l ≠ 0 ∧ ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp V)) ⟶ G), IsTorsFrame A ρ N x e → h ^ N = 1 → IntTerm.Ext U.toUnifPre x h → IntTerm.FrRel U.toUnifPre w₀ x e h l := by
  first | exact @GlobalTheory.Poinc.IntTerm.FrameInt.exists_frRel | exact GlobalTheory.Poinc.IntTerm.FrameInt.exists_frRel | (intros; apply GlobalTheory.Poinc.IntTerm.FrameInt.exists_frRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := _root_.GlobalTheory.MumCmp.SamePolIso.exists_iso R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := _root_.GlobalTheory.MumCmp.exists_translate_of_lam R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := _root_.GlobalTheory.MumCmp.Point.exists_point R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
end

