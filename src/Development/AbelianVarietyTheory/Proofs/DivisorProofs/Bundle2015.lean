module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I →
    Alg (i ≫ f) I := by
  intro R _ I W W' f i hf hi hA t ht hp
  obtain ⟨hs, hsp, hc⟩ := _root_.GlobalTheory.FormalAlg.mapSystem R I W W' f i hf inferInstance t ht hp
  obtain ⟨T, hT, hred⟩ := hA _ hs hsp
  refine ⟨T.comap i, ?_, fun e => ?_⟩
  · have h1 : (T.comap i).subschemeι ≫ i ≫ f =
        (T.comapIso i).hom ≫ pullback.snd i T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← T.comapIso_hom_fst_assoc i, pullback.condition_assoc]
    rw [h1]
    infer_instance
  · rw [← (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1 R W W' f i, ← Scheme.IdealSheafData.comap_sup, hred e]
    exact hc e

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOpenImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_comp_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ →
    ∀ (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (j : W' ⟶ W), IsSeparated f →
      IsOpenImmersion j → Alg f I → Alg (j ≫ f) I := by
  intro R _ I hI W W' f j hf hj hA t ht hp
  obtain ⟨hs, hsp, hsc⟩ := _root_.GlobalTheory.FormalAlg.mapSystem R I W W' f j hf inferInstance t ht hp
  obtain ⟨T, hTp, hTr⟩ := hA _ hs hsp

  have hs0 : ((((t 0).map j).support : Set W)) ⊆ Set.range j := by
    haveI : IsProper ((t 0).subschemeι ≫ j ≫ f) := hp 0
    haveI : IsProper (((t 0).subschemeι ≫ j) ≫ f) := by rw [Category.assoc]; infer_instance
    haveI : UniversallyClosed ((t 0).subschemeι ≫ j) := UniversallyClosed.of_comp_of_isSeparated _ f
    haveI : QuasiCompact ((t 0).subschemeι ≫ j) := QuasiCompact.of_comp _ f
    have hker : (t 0).map j = Scheme.Hom.ker ((t 0).subschemeι ≫ j) := by
      rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    rw [hker, Scheme.Hom.support_ker,
      (((t 0).subschemeι ≫ j).isClosedMap.isClosed_range).closure_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨(t 0).subschemeι x, by simp⟩

  have hT : ((T.support : Set W)) ⊆ Set.range j := by
    haveI : UniversallyClosed (T.subschemeι ≫ f) := inferInstance
    have hZ : IsClosed (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) :=
      (j.isOpenEmbedding.isOpen_range.isClosed_compl).preimage T.subschemeι.continuous
    have hE := _root_.GlobalTheory.closed_empty_of_universallyClosed_of_le_jacobson R I hI T.subscheme (T.subschemeι ≫ f) inferInstance _ hZ (by
      intro x hx hIx
      apply hx
      apply hs0
      have h0 : T ⊔ baseIdeal f (I ^ (0 + 1)) = (t 0).map j := hTr 0
      rw [← h0, Scheme.IdealSheafData.support_sup]
      refine ⟨?_, ?_⟩
      · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
      · refine ((_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).2.2 R W f (I ^ (0 + 1)) (T.subschemeι x)).2 ?_
        rw [zero_add, pow_one]
        simpa using hIx)
    intro y hy
    rw [← Scheme.IdealSheafData.range_subschemeι] at hy
    obtain ⟨x, rfl⟩ := hy
    by_contra hc
    have : x ∈ (T.subschemeι.base ⁻¹' (Set.range j)ᶜ) := hc
    rw [hE] at this
    exact this
  refine ⟨T.comap j, ?_, fun e => ?_⟩
  · have hsurj : Function.Surjective (pullback.snd j T.subschemeι) := by
      intro x
      obtain ⟨w, hw⟩ := hT (by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩)
      obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
      exact ⟨z, hz⟩
    haveI : IsIso (pullback.snd j T.subschemeι) :=
      (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨hsurj⟩⟩
    have he : (T.comap j).subschemeι ≫ j ≫ f =
        (T.comapIso j).hom ≫ pullback.snd j T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [he]
    infer_instance
  · rw [← (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1 R W W' f j, ← Scheme.IdealSheafData.comap_sup, show T ⊔ baseIdeal f (I ^ (e + 1)) = (t e).map j from hTr e, hsc e]

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameEqUnitSmulDForm
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.TopForm

theorem frame_eq_unit_smul_dForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ (g : Fin Dw.dim → (X₀ TF.Y Z).presheaf.stalk x) (bΩ : Module.Basis (Fin Dw.dim) ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) (u : (X₀ TF.Y Z).presheaf.stalk x), (∀ i, bΩ i = KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) (g i)) ∧ IsUnit u ∧ formOf U' (gen_mem hx) ω = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField u • TopForm.dForm (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) (fun i => algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (g i)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U' ω hω hx
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨U, y, b, hUU', hxU, hU, hb⟩ :=
    GlobalTheory.AdaptedFrame.exists_basis_dFun (s₀ TF.Y Z) Dw.dim hx
  have hy : IsFreeGen Γ(X₀ TF.Y Z, U) (dOn (s₀ TF.Y Z) y) := isFreeGen_dForm y b hb
  have hres : IsFrame (resForm hUU' ω) := hω.res hU hUU'
  obtain ⟨a, ha⟩ := hy.2 (resForm hUU' ω)
  have hau : IsUnit a := by
    have := hres.gen
    rw [← ha] at this
    exact hy.smul_iff.1 this
  have hgU : genericPoint (X₀ TF.Y Z) ∈ U := gen_mem hxU
  have hform : formOf U' (gen_mem hx) ω =
      fnOf U hgU a • dForm (constFn (s₀ TF.Y Z)) (fun i => fnOf U hgU (y i)) := by
    rw [← formOf_resForm hUU' hgU ω, ← ha, map_smulₛₗ]
    congr 1
    exact formMap_dForm _ _ _
  letI iΓ : Algebra c.F Γ(X₀ TF.Y Z, U) := (algX (s₀ TF.Y Z) U).toAlgebra
  letI iΓA : Algebra Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom.toAlgebra
  have hsc : algebraMap c.F ((X₀ TF.Y Z).presheaf.stalk x) =
      (algebraMap Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x)).comp
        (algebraMap c.F Γ(X₀ TF.Y Z, U)) := by
    ext t
    change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (algX (s₀ TF.Y Z) ⊤ t) =
      ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (algX (s₀ TF.Y Z) U t)
    rw [← resG_comp_algX (s₀ TF.Y Z) (le_top : U ≤ ⊤), RingHom.comp_apply, germ_resG]
  haveI : IsScalarTower c.F Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' hsc
  haveI : IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale c.F Γ(X₀ TF.Y Z, U)
    ((X₀ TF.Y Z).presheaf.stalk x)
  refine ⟨fun i => ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (y i), hbc.basis b,
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom a, fun i => ?_, hau.map _, ?_⟩
  · rw [IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D c.F c.F _ _ (y i)
  · rw [hform]
    simp only [algebraMap_germ]
end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffBoundedByDeterminants
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.FrameCoeffLoc

theorem coeff_mul_prod_mem_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∀ (p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → a ≠ 0 → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → GlobalTheory.LamT.SecInt T M.m1 M.m2 y'.s →
        ∀ cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr,
          (∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
        ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, ∃ w : T.V, iK (AddMonoidAlgebra.coeff G μ) * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
          (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he0 p T iK hT hiK M
  intro φ yT y' g a hφ hyT hy' ha hg hL hS cl hcl F hF hv G hG μ
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  have hτ : (∏ b, (g b).det ^ k b) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hg b).ne_zero
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hφ, hz.2.2.2.1]
  have main : ∃ w : T.V, AddMonoidAlgebra.coeff (MvPolynomial.map iK G) μ * ∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v =
      (∏ b, (g b).det ^ k b) * algebraMap T.V T.Fr w := by
    refine Formalism.L2.LamCM.coeff_integral_local T.V T.Fr _ Dw.mult (MvPolynomial.map iK G) (fun b => (g b)⁻¹) cl _
      inferInstance hT hτ (fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero) hcl ?_ μ
    intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
    have hinj : Function.Injective (algebraMap T.V W) := by
      intro x y h
      apply IsFractionRing.injective T.V T.Fr
      apply fW.injective
      rw [hfW, hfW, h]
    haveI : CharZero W := charZero_of_injective_ringHom hinj
    let T' : Formalism.L2.Pj.CDVR := ⟨W⟩
    let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
    have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
      (FractionRing.algEquiv W KW).symm.commutes w
    let i : T.Fr →+* T'.Fr := κ.comp fW
    have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
      ext x
      show _ = κ (fW _)
      rw [hfW, hκ]
      rfl
    letI := (i.comp io).toAlgebra
    let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
    obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
    obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
    have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g a hy' hyW).1 hy''
    have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
      rw [Matrix.det_transpose]; exact hX b
    have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
      have := (hXt b).map (algebraMap T'.V T'.Fr)
      rwa [RingHom.map_det] at this
    obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
    have hint := GlobalTheory.LamT.LocClause.integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
      (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
    obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
    have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
      rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul _ (hg b)]
      simp
    have hYX' : ∀ b, ((Y b).map κ).transpose =
        ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
      rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
      congr 1
      ext j k
      exact hκ _
    have hdet : ∀ b, ((Y b).map κ).det = algebraMap T'.V T'.Fr (X b).det * i (g b).det := fun b => by
      rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
      congr 1
      · rw [← Matrix.det_transpose (X b)]; exact (RingHom.map_det _ _).symm
      · exact (RingHom.map_det i (g b)).symm
    have hYd : ∀ b, ((Y b).map κ).det ≠ 0 := fun b => by
      rw [hdet b]
      exact mul_ne_zero ((hX b).map (algebraMap T'.V T'.Fr)).ne_zero ((map_ne_zero i).2 (hg b).ne_zero)
    have hsn : (iA a : T'.Fr) ≠ 0 := (map_ne_zero iA).2 ha
    have hc' : GlobalTheory.Frames.FrChg (fun b => ((Y b).map κ).transpose) ((Units.mk0 (iA a) hsn : T'.Frˣ) : T'.Fr) yW w := by
      have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c T'.Fr yW y'' w).2 _ _ _ _ hc hw
      simpa [hYX'] using c2
    have hbc := _root_.GlobalTheory.FrameRelBC.relation_baseChange_field E H Dw l Xo c z.K z.y e k he0 F hF G hG T'.Fr (iA.comp φ) yW w (fun b => (Y b).map κ)
      (Units.mk0 (iA a) hsn) hYd (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW) hc'
    refine ⟨(∏ b, (X b).det ^ k b) * w₀, κ.injective ?_⟩
    have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.map iK G)) =
        MvPolynomial.map (iA.comp φ).toRingHom G := by
      rw [MvPolynomial.map_map, MvPolynomial.map_map, ← hφ]
      rfl
    rw [GlobalTheory.LamT.LocClause.map_evalFr, hP, ← hbc, ← hw₀]
    simp only [hdet, map_mul, map_prod, map_pow, hκ, Finset.prod_mul_distrib, mul_pow]
    show _ = (∏ b, i (g b).det ^ k b) * _
    ring
  obtain ⟨w, hw⟩ := main
  exact ⟨w, by rw [← hw, MvPolynomial.coeff_map]⟩

end GlobalTheory.FrameCoeffLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointVectorsVerticalDeformationEigenbasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

section Chg

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frVec_of_frChg {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Type} [CommRing S]
    [Algebra c.F S] {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S} (hC : GlobalTheory.Frames.FrChg g a P P')
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    frVec Y P' hx' σ i = ∑ j, g σ i j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := hC.1
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1
      (hC.2.1 σ i)
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end Chg

end GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory

theorem frVec_isVert_isCombAtG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), GlobalTheory.Frames.FrChg G 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (x : Sp (DualNumber K) ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (M : GlobalTheory.Reg.MChart TF.Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U), IsVert P N' w → ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (GlobalTheory.FlagTan.unip K N' σ * (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF U n e v _hv K _ _ P₀ P hU G hG hB N' w x hx hUx M hM hV σ i
  obtain ⟨y₀, hy₀, hS⟩ := hV
  obtain ⟨P₀', h0⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) P₀
  have hC := (GlobalTheory.FlagTan.frMap_iff_frChg hG h0).1 hy₀
  have ew : frX w = frX y₀ := FlagMod.eq_frX y₀ ((FlagMod.frX_fst w).trans hS.1) (FlagMod.frX_snd w)
  have ey : frX y₀ = frX P₀' := FlagMod.eq_frX P₀' ((FlagMod.frX_fst y₀).trans hC.1) (FlagMod.frX_snd y₀)
  have hx₀ : frX y₀ ≫ TF.Y.j = x := ew ▸ hx
  have hx' : frX P₀' ≫ TF.Y.j = x := ey ▸ hx₀
  have e1 := frVec_of_frChg hM hx₀ hx hS σ i
  have e2 := fun j => frVec_of_frChg hM hx' hx₀ hC σ j
  have ecst : spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P₀ ≫ TF.Y.j) = x := by
    rw [← Category.assoc, FlagMod.frX_frMap h0, hx']
  have eev : ev x U.1 hUx = (GlobalTheory.FlagTan.cst c K).toRingHom.comp (ev (frX P₀ ≫ TF.Y.j) U.1 hU) := by
    rw [FlagMod.ev_congr ecst.symm U.1 hUx (ecst ▸ hUx), FlagMod.ev_spMap]
  have e3 : ∀ k, (tv (frVec TF.Y P₀' hx' σ k)).left = spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, k⟩) := by
    intro k
    rw [← FlagMod.tanPull_frVec h0 rfl hx' ecst, FlagMod.tanPull_left, hB σ k, ← Category.assoc, spMap_comp',
      ← dualMap_comp, eev]
  open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections in
  have key : frVec TF.Y w hx σ i = ∑ k, (GlobalTheory.FlagTan.unip K N' σ *
      (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i k • frVec TF.Y P₀' hx' σ k := by
    rw [e1]
    simp_rw [e2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    rfl
  have hv' : (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) =
      fun j => (tv (frVec TF.Y P₀' hx' σ j)).left := funext fun j => (e3 j).symm
  rw [hv', GlobalTheory.LieMet.isComb_iff]
  exact key

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.Unique

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    Nonempty (GObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _
     φ₂ := 𝟙 _
     cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
     sq := ⟨by simp, by simp⟩
     act := fun c => by simp
     pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
     eta := fun y => by simp }⟩

private theorem lbIso_pull_comp_of_lbIso {X Y Z : Scheme.{0}} {M : LB X} {P : LB Y} {Q : LB Z} {a : X ⟶ Y} {c : Y ⟶ Z}
    (H₁ : LBIso M (P.pull a)) (H₂ : LBIso P (Q.pull c)) (hM : M.IsLB) (hP : P.IsLB) (hQ : Q.IsLB) :
    LBIso M (Q.pull (a ≫ c)) := by
  have E : LBIso (P.pull a) ((Q.pull c).pull a) := SiegelDescent.lbIso_square hP hQ H₂ rfl
  have F : LBIso ((Q.pull c).pull a) ((Q.pull (a ≫ c)).pull (𝟙 X)) :=
    GlobalTheory.FiniteAmple.lbIso_pull_pull c hQ (g := a) (g' := 𝟙 X) (f' := a ≫ c) (by rw [Category.id_comp])
  have hPa := pull_isLB hP a
  have hQc := pull_isLB hQ (a ≫ c)
  exact LBIso.trans hM hPa hQc H₁ (LBIso.trans hPa (pull_isLB (pull_isLB hQ c) a) hQc E
    (LBIso.trans (pull_isLB (pull_isLB hQ c) a) (pull_isLB hQc (𝟙 X)) hQc F (GlobalTheory.SiegLower.lbIso_pull_id hQc).symm))

theorem gObjMap_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₃ (f ≫ g)) :=
  ⟨{ φ := h₁.φ ≫ h₂.φ
     φ₂ := h₁.φ₂ ≫ h₂.φ₂
     cart := IsGrpPullback.comp h₁.cart h₂.cart
     sq := ⟨by rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc],
       by rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]⟩
     act := fun c => by rw [← Category.assoc, h₁.act c, Category.assoc, h₂.act c, ← Category.assoc]
     pol := lbIso_pull_comp_of_lbIso h₁.pol h₂.pol o₁.isLB o₂.isLB o₃.isLB
     eta := fun y => by rw [← Category.assoc, h₁.eta y, Category.assoc, h₂.eta y, ← Category.assoc] }⟩

end GlobalTheory.UPel.HT.Gen.Unique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineCharStatement
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
theorem _root_.GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧ ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  first | exact @GlobalTheory.GenFracChart.isFractionRing_and_const | exact GlobalTheory.GenFracChart.isFractionRing_and_const | (intros; apply GlobalTheory.GenFracChart.isFractionRing_and_const <;> assumption)
end

