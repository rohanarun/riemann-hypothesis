module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFETranslateFeTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HeckeCharacterFamilyConductor
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionWeightZeroNonzero
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SquareSectionWeightZero

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), ∃ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) ∧ ¬ ∀ j, (f 0).f j = 0 := by
  intro R _ _ _ _ G _ _ _ D A U
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨E, hE⟩ := GlobalTheory.FamFree.exists_fam_support (F := FractionRing R) h1.globalFns h2.secTwist
    D.tau_bimult (k := 2) (by norm_num) (0 : D.toPre.X)
  have hE0 : ¬ ∀ j, (E.s 0).f j = 0 := (hE 0).2 ⟨0, by simp⟩
  obtain ⟨s, hs, -⟩ := (U.expand 2 (by norm_num)).2 E
  obtain ⟨r, hr, σ, f, -, hf, hexp⟩ := hs
  refine ⟨σ, f, hexp, fun h0 => hE0 ?_⟩
  have key := (GlobalTheory.ConstFam.secScal_iff_resF D.toPre (FractionRing R) (E.s 0) (f 0) r).1 (hf 0)
  have hf0 : (f 0 : GlobalTheory.ConstFam.SecBMod D.toPre 2 0) = 0 := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext h0
  rw [hf0] at key
  erw [map_zero] at key
  have hr' : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r ≠ 0 := by
    intro h
    apply hr
    have hinj : Function.Injective (GlobalTheory.ConstFam.toF (R := R) (FractionRing R)) :=
      (algebraMap (FractionRing R) (FractionRing R)).injective.comp (IsFractionRing.injective R _)
    exact hinj (h.trans (map_zero _).symm)
  let t : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 := E.s 0
  have k2 : GlobalTheory.ConstFam.toF (R := R) (FractionRing R) r • t = 0 := key.symm
  have e0 : t = 0 := by rw [← inv_smul_smul₀ hr' t, k2, smul_zero]
  intro j
  exact congrArg (fun q : GlobalTheory.ConstFam.SecFMod D.toPre (FractionRing R) 2 0 => LB.Sec.f q j) e0

end GlobalTheory.SquareSectionWeightZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCartierOnNormalizedBlowup
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
open Cartier

theorem EffCartierData.keepsRegular_of_dense {X' N : Scheme.{0}} (D : EffCartierData X')
    (ν : N ⟶ X') (hN : ∀ y : N, IsDomain (N.presheaf.stalk y))
    (hd : Dense {z : N | ν z ∉ D.idealSheaf.support}) : D.KeepsRegular ν := by
  intro i
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  haveI := hN y
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom ((ν.app (D.U i)).hom (D.f i)) =
      (N.presheaf.germ (ν ⁻¹ᵁ D.U i) y hy).hom 0 := by rw [h0, map_zero]
  obtain ⟨W, hW, i₁, i₂, e'⟩ := N.presheaf.germ_eq y hy hy _ _ e
  obtain ⟨z, hzW, hzO⟩ := hd.inter_open_nonempty W W.isOpen ⟨y, hW⟩
  haveI := hN z
  have hzU : z ∈ ν ⁻¹ᵁ D.U i := i₁.le hzW
  have hz0 : (N.presheaf.germ _ z hzU).hom ((ν.app (D.U i)).hom (D.f i)) = 0 := by
    have := congrArg (N.presheaf.germ W z hzW).hom e'
    simpa using this
  have hunit : IsUnit ((X'.presheaf.germ (D.U i) (ν z) hzU).hom (D.f i)) := by
    have h1 : ν z ∈ X'.basicOpen (D.f i) := by
      by_contra h
      exact hzO ((D.mem_support_iff i hzU).2 h)
    exact (X'.mem_basicOpen _ _ hzU).1 h1
  have hu := hunit.map (ν.stalkMap z).hom
  rw [← EffCartierData.germ_app ν (D.f i) z hzU, hz0] at hu
  exact not_isUnit_zero hu

end GlobalTheory

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFieldExtension
section
open TensorProduct
namespace GlobalTheory.FieldExtensionExists

theorem exists_field_extension {R R' K : Type} [CommRing R] [CommRing R'] [Field K]
    (ρ : R →+* R') (hinj : Function.Injective ρ) (hfin : ρ.Finite) (φ : R →+* K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (χ : R' →+* L),
      χ.comp ρ = (algebraMap K L).comp φ := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal R') (by
    intro x hx
    have : ρ x = 0 := hx
    have h0 : x = 0 := hinj (this.trans (map_zero ρ).symm)
    rw [h0]; exact Ideal.zero_mem _)
  have hqc' : q.comap ρ = RingHom.ker φ := hqc
  let j : (R ⧸ RingHom.ker φ) →+* (R' ⧸ q) := Ideal.quotientMap q ρ hqc'.ge
  have hj : Function.Injective j := Ideal.quotientMap_injective' hqc'.le
  have hjf : j.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker φ))
    have : j.comp (Ideal.Quotient.mk (RingHom.ker φ)) = (Ideal.Quotient.mk q).comp ρ := by
      ext x; simp [j]
    rw [this]
    exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
  letI : Algebra (R ⧸ RingHom.ker φ) (R' ⧸ q) := j.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.Finite (R ⧸ RingHom.ker φ) (R' ⧸ q) := hjf
  haveI : Nontrivial (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.kerLift_injective φ) hj
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q))
  refine ⟨(K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M, Ideal.Quotient.field M, inferInstance,
    (inferInstance : Module.Finite K ((K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M)),
    (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q)).toRingHom.comp (Ideal.Quotient.mk q)), ?_⟩
  ext r
  change Ideal.Quotient.mk M (Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q) (algebraMap (R ⧸ RingHom.ker φ) (R' ⧸ q) (Ideal.Quotient.mk _ r))) =
    Ideal.Quotient.mk M ((φ r) ⊗ₜ 1)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem exists_extension : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'),
    Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (ψ : R →+* V), IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
      (f : V →+* V') (ψ' : R' →+* V'), GlobalTheory.LN.CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧
      ψ'.comp ρ = f.comp ψ := by
  intro R R' _ _ _ _ ρ hinj hfin V _ _ _ hV ψ hψ
  obtain ⟨h1, h2, h3⟩ := hV
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨L, _, _, _, χ, hχ⟩ := exists_field_extension ρ hinj hfin ((algebraMap V (FractionRing V)).comp ψ)
  obtain ⟨W, _, _, hW1, hW2, _, _, _, hc, -, hf, hl, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hmem : ∀ x : R', ∃ w : W, algebraMap W L w = χ x := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hfin.to_isIntegral x
    refine hint (χ x) ⟨P.map ψ, hP.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hχ, ← Polynomial.hom_eval₂, hPx, map_zero]
  choose g hg using hmem
  let ψ' : R' →+* W :=
    { toFun := g
      map_one' := hWL (by simp [hg])
      map_mul' := fun x y => hWL (by simp [hg])
      map_zero' := hWL (by simp [hg])
      map_add' := fun x y => hWL (by simp [hg]) }
  have hcomp : ψ'.comp ρ = (algebraMap V W).comp ψ := by
    ext r
    apply hWL
    have e1 := RingHom.congr_fun hχ r
    have e2 := RingHom.congr_fun hc (ψ r)
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e2, ← e1]
    exact hg _
  have hloc : IsLocalHom (ψ'.comp ρ) := by rw [hcomp]; infer_instance
  have hmax : ((IsLocalRing.maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hfin.to_isIntegral
    have e : (IsLocalRing.maximalIdeal W).comap (ψ'.comp ρ) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_tfae (ψ'.comp ρ)).out 1 5).1 hloc
    rw [Ideal.comap_comap, e]
    infer_instance
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨hW1, hW2, charZero_of_injective_algebraMap hf⟩, hf, hl, ?_, hcomp⟩
  exact ((IsLocalRing.local_hom_tfae ψ').out 1 5).2 (IsLocalRing.eq_maximalIdeal hmax)

end GlobalTheory.FieldExtensionExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundary
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

namespace GlobalTheory.ShFam

theorem exists_frPt_cxPt_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ), ¬ LiesIn y (genBd Z) → ∀ f : EigFrame Z σ (y.1 ≫ genι Z), ∃ q : FrPt Xo c (CAt σ), cxPt Z q = y ∧ ∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ y hy f
  have hr : Set.range y.1 ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    exact not_not.1 hy
  have := Z.jQ_open
  let zF := IsOpenImmersion.lift Z.jQ y.1 hr
  have hzF : zF ≫ Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : zF ≫ pullback.snd _ _ = spMap σ := by
    have h2 := y.2
    rw [← hzF, Category.assoc, Z.jQ_over] at h2
    exact h2
  obtain ⟨q, hq, hv⟩ := exists_frPt_ptF_of_eigFrame E H Dw l Xo c O β Z ℂ σ zF (y.1 ≫ genι Z) f hs
    (by rw [← Category.assoc, hzF])
  refine ⟨q, Subtype.ext ?_, hv⟩
  exact (congrArg (· ≫ Z.jQ) hq).trans hzF

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreExact

theorem locK_mem_of_values : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : IntermediateField ℚ ℂ), GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ), ((χ.locK P k : ℂˣ) : ℂ) ∈ M :=
  fun _ _ _ χ _ hv hi P _ => GlobalTheory.HeckeValField.mem_unitsIn.1 (GlobalTheory.HeckeValField.loc_mem χ hv hi P _)

theorem char_mem_of_values : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ M : IntermediateField ℚ ℂ, GlobalTheory.Mem.Fld.valueField χ 0 ≤ M → (∀ k : D.host.Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ M := by
  intro D c χ hc M hv hi x hx
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom x)
  rw [hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => locK_mem_of_values D.host.E χ M hv hi P (k P)

theorem KsC_eq (X : Stages) : X.B.KsC = FO X.toD7 := by
  ext z
  rw [Base.mem_KsC, mem_FO_assembled_iff]

theorem exists_core_exact : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  intro X f hch hv _
  obtain ⟨J, hJ, hC, hCan, hp, hpq, -⟩ := GlobalTheory.FinalJoin2.exists_coreJ_of_chiOK_noVol X.toD7 (hermitianCodeWordStages_ringOfIntegers_full X)
    (hermitianCodeWordStages_has_rootOfUnity X) f.P.pb f.P.pb_over _ (GlobalTheory.FinalJoin.chiOK_one X.toD7)
  have hP : J.Q.PinField := hJ.pins.2.2.1
  letI := Formalism.IndefR.FWT.algTop J hP
  have ha : Formalism.IndefR.FWT.AlgTie J := Formalism.IndefR.FWT.algTie_algTop J hP

  have hemb : ∀ y : J.Q.c.F, X.toD7.what₂.embLL (algebraMap J.Q.c.F X.toD7.what₂.LL y) = (y : ℂ) := by
    have h : X.toD7.what₂.embLL.comp (algebraMap J.Q.c.F X.toD7.what₂.LL) = J.Q.c.F.val.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 J.Q.c.F)) (RingHom.ext fun x =>
        (congrArg X.toD7.what₂.embLL (ha x)).trans (hP x))
    exact fun y => RingHom.congr_fun h y

  have hle : ∀ y : J.Q.c.F, (y : ℂ) ∈ FO X.toD7 := by
    intro y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 J.Q.c.F) y
    have hi : ∀ a : 𝓞 J.Q.c.F, ((a : J.Q.c.F) : ℂ) ∈ FO X.toD7 := fun a => by
      rw [← hP a]
      exact phiO_mem_FO _ _
    rw [IntermediateField.coe_div]
    exact div_mem (hi a) (hi b)
  have hge : ∀ z ∈ FO X.toD7, ∃ y : J.Q.c.F, (y : ℂ) = z := by
    intro z hz
    have hle' : FO X.toD7 ≤ J.Q.c.F := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, rfl⟩ := J.Q.eO.surjective w
      have h : X.toD7.what₂.phiO (J.Q.eO x) = ((x : J.Q.c.F) : ℂ) := hP x
      rw [h]
      exact (x : J.Q.c.F).2
    exact ⟨⟨z, hle' hz⟩, rfl⟩

  have hback : ∀ z : X.toD7.what₂.LL, X.toD7.what₂.embLL z ∈ FO X.toD7 →
      ∃ y : J.Q.c.F, algebraMap J.Q.c.F X.toD7.what₂.LL y = z := by
    intro z hz
    obtain ⟨y, hy⟩ := hge _ hz
    exact ⟨y, X.toD7.what₂.embLL.injective ((hemb y).trans hy)⟩
  refine ⟨J, inferInstance, ⟨hC, hCan, hpq, hp⟩, hemb, fun y => ?_, fun x hx => hback x ?_, fun x => hback _ ?_,
    hJ, ha, hv.toLL, ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (mem_FO_assembled_iff X _).1 (hle y)
    have : algebraMap J.Q.c.F X.toD7.what₂.LL y = x := X.toD7.what₂.embLL.injective (((hemb y).trans hx'.symm))
    rw [this]
    exact X.B.Ks_le hx
  · exact (mem_FO_assembled_iff X _).2 ⟨x, hx, rfl⟩
  · rw [show X.toD7.what₂.embLL (X.toD7.embE x) = X.toD7.host.φ₀ x from RingHom.congr_fun X.toD7.embE_φ₀ x]
    exact phi0_mem_coeff_field _ x
  · intro T' L μ hL hLC i x hx
    have hmem : ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ FO X.toD7 := by
      refine char_mem_of_values X.toD7 _ _ (hL.mu0 i) (FO X.toD7) ?_ ?_ x hx
      · rw [hLC, ← KsC_eq]
        exact (le_iSup (fun j => Fld.valueField (f.mu0 j) 0) i).trans
          (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans hch))))
      · intro k
        obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
        choose z hz using fun g => (X.toD7.hc (X.toD7.eTau.symm g)).e_int i
        have hnz : n = fun g => 2 * -z g := funext fun g => by
          have h1 := hn g
          simp only [Formalism.L2.Host.eExp, hz] at h1
          exact_mod_cast h1
        rw [hnz] at hi
        rw [hi k]
        refine prod_mem fun g _ => ?_
        rw [GlobalTheory.RefCharValues.sign_zpow_even _ ((map_ne_zero _).2 k.ne_zero)]
        exact zpow_mem (div_mem (conj_mem_FO _ _ _) (conj_mem_FO _ ((starRingEnd ℂ).comp _) _)) _
    obtain ⟨y, hy⟩ := hge _ hmem
    exact ⟨y, by rw [hemb, hy]⟩

end GlobalTheory.CoreExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.MonPeriods

theorem exists_isMonomial_levelOne : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {W : Type}
    [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (t : SAB H (Sp W))
    (P : PELUnif (maximalIdeal W) t), ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] := by
  intro E _ _ _ H W _ _ _ hW ϖ hϖ t P
  obtain ⟨hdvr, hcomp, hchar⟩ := hW
  haveI := hdvr
  haveI := hcomp
  haveI := hchar
  letI := H.starRing
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hQ' : QForm.IsQ P.D.toPre ϖ Q := hQ
  have hex : ∀ χ, ∃ r, PsiCoord P.D.toPre χ r := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main W P.D inferInstance χ).1).imp fun _ h => h.1
  have hv : ∀ χ, HasVal ϖ (algebraMap W (FractionRing W) (hex χ).choose) (Q χ) := fun χ =>
    GlobalTheory.ValForm.hasVal_coord (hQ χ) (hex χ).choose_spec
  have h0 : ∀ a, 0 ≤ Q a := fun a => by
    by_cases ha : a = 0
    · rw [ha, QForm.Q_zero hϖ P.D hQ']
    · exact zero_le_one.trans (QForm.Q_pos hϖ P.D hQ' ha)
  have hbal : ∀ (x : 𝓞 E) a b, QForm.bOf P.D.toPre Q (x • a) b = QForm.bOf P.D.toPre Q a (H.bar x • b) := by
    intro x a b
    obtain ⟨u, hu⟩ := GlobalTheory.PeriodBalance.coord_balance P.D.toPre P.oD x a b (hex (x • a + b)).choose_spec
      (hex (x • a)).choose_spec (hex b).choose_spec (hex (a + H.bar x • b)).choose_spec (hex a).choose_spec
      (hex (H.bar x • b)).choose_spec
    have h1 := hasVal_mul_unit (GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (x • a + b)) (hv a))
      (hv (H.bar x • b))) u
    have h2 := GlobalTheory.ValForm.hasVal_mul hϖ (GlobalTheory.ValForm.hasVal_mul hϖ (hv (a + H.bar x • b)) (hv (x • a))) (hv b)
    rw [← map_mul, _root_.mul_comm, hu] at h1
    have := hasVal_unique hϖ h1 h2
    simp only [QForm.bOf]
    linarith
  let be : LinearMap.BilinForm ℤ P.D.toPre.X :=
    LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ P.D hQ' a b)
      (fun a a' b => by simp only [map_add (f := _), AddMonoidHom.add_apply])
      (fun c a b => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun a b b' => by simp only [map_add (f := _)])
      (fun c a b => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ a b, be a b = QForm.bOf P.D.toPre Q a b := fun _ _ => rfl
  refine ⟨be, ⟨fun y z => ?_, fun a y z => ?_, fun y z => by simp⟩, fun y => ?_⟩
  · rw [hbe, hbe, QForm.bOf_comm]
  · rw [hbe, hbe]
    exact hbal a y z
  · obtain ⟨u, hu⟩ := hv y
    set r := (hex y).choose with hr
    have hn : (((Q y).toNat : ℕ) : ℤ) = Q y := Int.toNat_of_nonneg (h0 y)
    have e : r = ↑u * ϖ ^ (Q y).toNat := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [hu, map_mul, map_pow, _root_.mul_comm, ← zpow_natCast, hn]
    refine ⟨u, fun _ => (Q y).toNat, fun i => ?_, ?_⟩
    · fin_cases i
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hbe, ← QForm.two_Q_eq hϖ P.D hQ', hn]
    · have hc : PsiCoord P.D.toPre y r := (hex y).choose_spec
      rw [e] at hc
      simpa using hc

end GlobalTheory.MonPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormImRealCombinationEqDotProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → ∀ u v : Fin r → ℝ, (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  first | exact @GlobalTheory.hermForm_im_real_comb | exact GlobalTheory.hermForm_im_real_comb | (intros; apply GlobalTheory.hermForm_im_real_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRealCombinationsOfIndependentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  first | exact @GlobalTheory.linearIndependent_real_combination | exact GlobalTheory.linearIndependent_real_combination | (intros; apply GlobalTheory.linearIndependent_real_combination <;> assumption)
end

