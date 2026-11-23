module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGood

theorem hom_spQ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℚ) : f = g := by
  have key : ∀ h : X ⟶ Sp ℚ, h = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ h.appTop) := by
    intro h
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key f, key g]
  congr 2
  ext1
  exact RingHom.ext_rat _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_objMap_lower' {l l₂ : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B'} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj Dw l b' s} {o₂ : Obj Dw l₂ b₂ s₂} {o' : Obj Dw l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    Nonempty (ObjMap (GlobalTheory.ObjLower.lower o' h hρ hζ) o (g ≫ π)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₁ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.eta_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₂ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.etaA_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

theorem eq_of_levelMaps {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} (hd : l.Dvd l₂)
    (jK : KA l →+* KA l₂) (hjK : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {r r' : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (m' : SABMap Xo₂.univ.t Xo.univ.t r')
    (he : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (heA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (he' : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = r' ≫ (Xo.univ.eta a).left)
    (heA' : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = r' ≫ (Xo.univ.etaA a).left)
    {T : Scheme.{0}} [IsReduced T] (iU : T ⟶ Xo₂.X) (h : iU ≫ r ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK)
    (h' : iU ≫ r' ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK) : iU ≫ r = iU ≫ r' := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o', ⟨u⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) (KA l₂) (baseKA l₂) (baseKA l₂) (RingHom.id _) Xo₂.X T Xo₂.s
    (iU ≫ Xo₂.s) iU rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨w⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m he heA u
  obtain ⟨w'⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m' he' heA' u
  have hρ : jK (baseKA l).ρ = (GlobalTheory.baseOfFinerLevel hA).ρ :=
    Subtype.ext ((hjK _).trans ((GlobalTheory.coe_baseKA_rho l).trans (GlobalTheory.coe_baseKA_rho l₂).symm))
  have hζ : jK (baseKA l).ζ = (GlobalTheory.baseOfFinerLevel hA).ζ :=
    Subtype.ext ((hjK _).trans (GlobalTheory.coe_levelFieldIncl hA _).symm)
  have hu := GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H Dw l Xo (KA l₂) (GlobalTheory.baseOfFinerLevel hA) jK T
    (iU ≫ Xo₂.s) (GlobalTheory.ObjLower.lower o' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA))
    inferInstance hρ hζ
  exact hu.unique ⟨by rw [Category.assoc, h, Category.assoc], ⟨w⟩⟩ ⟨by rw [Category.assoc, h', Category.assoc], ⟨w'⟩⟩

theorem formallyUnramified_spQ (l : Level H) : FormallyUnramified (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.formallyUnramified_algebraMap.mpr (Algebra.FormallyUnramified.of_isSeparable ℚ (KA l))

theorem locallyOfFiniteType_spQ (l : Level H) : LocallyOfFiniteType (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end GlobalTheory.CoverGood

theorem GlobalTheory.CoverGood.exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  intro E _ _ _ H Dw l Xo c d hpq hl
  obtain ⟨hdvd, hM, -, -, -, ⟨he, heA⟩, hlift, -, -⟩ := hl
  obtain ⟨r₀, jK, m₀, hjK, hr₀s, he₀, heA₀, -, hrF⟩ := (_root_.GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h₁, h₂, hfin, het, -, -⟩ := hrF c d.c₂ d.hF.symm
  have hdiv : d.l₂.M / l.M = d.pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  rw [← hdiv] at he

  have hab : (d.r ≫ Xo.s) ≫ spMap (algebraMap ℚ (KA l)) = (d.Xo₂.s ≫ spMap jK) ≫ spMap (algebraMap ℚ (KA l)) :=
    GlobalTheory.CoverGood.hom_spQ_ext _ _
  have := GlobalTheory.CoverGood.formallyUnramified_spQ l
  have := GlobalTheory.CoverGood.locallyOfFiniteType_spQ l
  have hop : IsOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified _ hab
  have hcl : IsClosedImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  have hred₂ : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim d.Xo₂.s)).1
  have hredU : IsReduced (equalizer (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    isReduced_of_isOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
  have hagree : equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ d.r =
      equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ r₀ :=
    GlobalTheory.CoverGood.eq_of_levelMaps hdvd jK hjK d.m m₀ he heA he₀ heA₀ _
      (equalizer.condition (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
      (by rw [hr₀s])

  obtain ⟨U, iU, hop', hcl', hagree', hlU⟩ : ∃ (U : Scheme.{0}) (iU : U ⟶ d.Xo₂.X), IsOpenImmersion iU ∧
      IsClosedImmersion iU ∧ iU ≫ d.r = iU ≫ r₀ ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ d.Xo₂.X),
        x ≫ d.r ≫ Xo.s = x ≫ d.Xo₂.s ≫ spMap jK → ∃ u : Sp K ⟶ U, u ≫ iU = x :=
    ⟨_, _, hop, hcl, hagree, fun K _ x hx =>
      ⟨equalizer.lift x (by simpa only [Category.assoc] using hx), equalizer.lift_ι _ _⟩⟩
  clear hop hcl hagree hredU
  haveI := hop'; haveI := hcl'; haveI := hfin; haveI := het
  have hsp : spMap (IntermediateField.inclusion d.hF.symm.le).toRingHom ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) =
      spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨pullback iU (pullback.fst d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)),
    pullback.snd _ _ ≫ rF, pullback.fst _ _ ≫ iU, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, _, _, j, ⟨k0, hk0⟩⟩ := GlobalTheory.ZM.IsGaloisCover.exists_algClosed_point (Xo.XF c) x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ pullback.snd _ _ : Sp K ⟶ Sp c.F)
    letI : Algebra c.F K := φ.hom.toAlgebra
    letI : Algebra d.c₂.F K := ((algebraMap c.F K).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a := fun a => by
      show algebraMap c.F K (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    have hjs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := hφ.symm
    have hx₀ : (j ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, sOf, spMap, spMap, ← Spec.map_comp]
      rfl
    have hex : ∃ y : FrPt Xo c K, y.x = j ≫ pullback.fst _ _ := by
      choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx₀ τ
      obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist (j ≫ pullback.fst _ _)
      exact ⟨⟨_, hx₀, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩
    obtain ⟨y, hy⟩ := hex
    obtain ⟨y₂, hy₂⟩ := hlift K hk y
    have hyr : y₂.x ≫ d.r = y.x := hy₂.1
    have hgood : y₂.x ≫ d.r ≫ Xo.s = y₂.x ≫ d.Xo₂.s ≫ spMap jK := by
      rw [reassoc_of% hyr, y.x_over, reassoc_of% y₂.x_over, sOf, sOf]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext t
      show algebraMap c.F K (IntermediateField.inclusion c.le t) =
        algebraMap c.F K (d.eF.symm (IntermediateField.inclusion d.c₂.le (jK t)))
      exact congrArg (algebraMap c.F K) (Subtype.ext (hjK t).symm)
    obtain ⟨u, hu⟩ := hlU K y₂.x hgood
    have hw : y₂.x ≫ d.Xo₂.s =
        spMap (algebraMap d.c₂.F K) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
      rw [y₂.x_over, sOf, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have hr₀ : y₂.x ≫ r₀ = y.x := by
      rw [← hu, Category.assoc, ← hagree', ← Category.assoc, hu, hyr]
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Sp K ⟶ d.Xo₂.XF d.c₂, w ≫ pullback.fst _ _ = y₂.x ∧
        w ≫ pullback.snd _ _ = spMap (algebraMap d.c₂.F K) :=
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨z, hz⟩ : ∃ z : Sp K ⟶ pullback iU (pullback.fst d.Xo₂.s
        (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)), z ≫ pullback.snd _ _ = w :=
      ⟨pullback.lift u w (by rw [hu, hw₁]), pullback.lift_snd _ _ _⟩
    have e : z ≫ pullback.snd _ _ ≫ rF = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, reassoc_of% hz, reassoc_of% hw₁, hr₀, hy]
      · rw [Category.assoc, Category.assoc, h₂, reassoc_of% hz, reassoc_of% hw₂, hjs, spMap, spMap,
          spMap, ← Spec.map_comp]
        rfl
    exact ⟨z k0, by rw [← Scheme.Hom.comp_apply, e, hk0]⟩
  · simp only [Category.assoc]
    rw [hagree', h₁, pullback.condition_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% h₂, hsp, pullback.condition]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
section
open Polynomial

namespace GlobalTheory.InvariantSpecialisation

theorem exists_extension {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    [Field Ω] [IsAlgClosed Ω] (e : A →+* Ω) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = e := by
  haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥
    (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h := l.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem exists_smul_of_comp_eq {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Field Ω] [CharZero Ω] (φ ψ : B →+* Ω)
    (h : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  classical
  letI := Fintype.ofFinite G
  have h1 : ∀ b, ∃ g : G, ψ b = φ (g • b) := by
    intro b
    obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
    have hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b := hp
    have e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
      rw [← hp', Polynomial.map_map, Polynomial.map_map, h]
    have e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]
    rw [e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at e2
    obtain ⟨g, -, hg⟩ := e2
    refine ⟨g, ?_⟩
    simpa [sub_eq_zero] using hg
  let H : G → AddSubgroup B := fun g =>
    { carrier := {b | ψ b = φ (g • b)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add (f := _), smul_add, map_add (f := _), ha, hb]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, smul_neg, map_neg, ha] }
  obtain ⟨g, -, hg⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover
    (H := H) (g := fun _ => 0) (s := Finset.univ) (by
      rw [Set.eq_univ_iff_forall]
      intro b
      obtain ⟨g, hg⟩ := h1 b
      simp only [Set.mem_iUnion]
      exact ⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)
  refine ⟨g, fun b => ?_⟩
  have h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b)) := (H g).nsmul_index_mem b
  rw [smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2

theorem exists_finite_extension_finrank_dvd :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G]
      [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G],
      Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k),
      ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧
        Module.finrank k K' ∣ Nat.card G ∧
        β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  intro A B _ _ _ G _ _ _ _ _ hinj k _ _ ev
  haveI := Algebra.IsInvariant.isIntegral A B G
  let Ω := AlgebraicClosure k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨φ, hφ⟩ := exists_extension hinj ((algebraMap k Ω).comp ev)
  let K : IntermediateField k Ω := IntermediateField.adjoin k (Set.range φ)
  let P : Subgroup ((Ω ≃ₐ[k] Ω) × G) :=
    { carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)}
      one_mem' := by intro b; simp
      mul_mem' := by
        intro x y hx hy b
        simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]
        rw [hy, hx, mul_smul]
      inv_mem' := by
        intro x hx b
        apply x.1.injective
        rw [hx]
        simp }
  let p₁ : P →* (Ω ≃ₐ[k] Ω) := (MonoidHom.fst _ _).comp P.subtype
  let p₂ : P →* G := (MonoidHom.snd _ _).comp P.subtype
  have hsurj : Function.Surjective p₁ := by
    intro σ
    obtain ⟨g, hg⟩ := exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by
      rw [RingHom.comp_assoc, hφ]
      ext a
      simp)
    exact ⟨⟨(σ, g), hg⟩, rfl⟩
  have hle : p₂.ker ≤ K.fixingSubgroup.comap p₁ := by
    rintro ⟨⟨σ, g⟩, hx⟩ hg
    have hg1 : g = 1 := hg
    subst hg1
    change σ ∈ K.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hxK
    induction hxK using IntermediateField.adjoin_induction with
    | mem x hx' =>
      obtain ⟨b, rfl⟩ := hx'
      simpa using hx b
    | algebraMap c => exact σ.commutes c
    | add x y _ _ h1 h2 => rw [map_add (f := _), h1, h2]
    | inv x _ h1 => rw [map_inv₀, h1]
    | mul x y _ _ h1 h2 => rw [map_mul, h1, h2]
  have hdvd : Module.finrank k K ∣ Nat.card G := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      ← Subgroup.index_comap_of_surjective _ hsurj]
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨K, inferInstance, inferInstance,
    φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩
  · exact Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)
  · ext a
    exact RingHom.congr_fun hφ a

end GlobalTheory.InvariantSpecialisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActions
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.FockData

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, inclR, compInf, infEmb_tmul]

theorem det_map_ne_zero {E : Type} [Field E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (h : J.det ≠ 0) :
    (J.map τ).det ≠ 0 := by
  rw [show J.map τ = τ.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero τ).2 h

theorem exists_fock_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) , IsCMExt F E σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W), IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 → M.IsWeil ψ χX χW om → ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) → (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) → ∃ (P Q R S : InfinitePlace F → ℕ) (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c c' : InfinitePlace F → ℂ), FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C ∧ Function.Injective Φ ∧ LinearMap.range Φ = M.Pol ψ τ ∧ ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c ∧ ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c' := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hXh hXd hWs hWd hW τ hXc hWc

  have hX : ∀ w, ∃ (r s : ℕ) (A : Matrix (Fin n) (Ix r s) ℂ),
      IsFrame (X.J.map (τ w).1) A ∧ X.θ w * A = A * Jm r s := by
    intro w
    refine _root_.GlobalTheory.HoweD.FrameCartan.frame_of_cartan n _ _ ?_ (det_map_ne_zero _ _ hXd) (hXc w)
    intro i j
    simp only [Matrix.map_apply]
    rw [← hCM.2.2.2 (τ w).1, hXh]
  have hW' : ∀ w, ∃ (r s : ℕ) (C : Matrix (Fin d) (Ix r s) ℂ),
      IsFrame (Complex.I • W.J.map (τ w).1) C ∧ W.θ w * C = C * Jm r s := by
    intro w
    refine _root_.GlobalTheory.HoweD.FrameCartan.frame_of_cartan d _ _ ?_ ?_ (hWc w)
    · intro i j
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul']
      rw [← hCM.2.2.2 (τ w).1, hWs, map_neg, show star Complex.I = -Complex.I from Complex.conj_I]
      ring
    · rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (det_map_ne_zero _ _ hWd)
  choose P Q A hA hθA using hX
  choose R S C hC hθC using hW'

  have hF : FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C := by
    refine ⟨one_mul _, fun w => ?_, fun w => ?_⟩
    · rw [one_smul, incM_map_piInf]
      exact hA w
    · rw [incM_map_piInf]
      exact hC w
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_fockMap_signatures_depend_on_place F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C
    hCM hψ hF

  obtain ⟨hB, ⟨d', hd', hA'⟩, -⟩ := hW
  obtain ⟨c, hc⟩ := GlobalTheory.T.firstMember_lieAction_fock_plus_trace F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co d' 1 Complex.I A C Φ
    (om.comp (MonoidHom.inl _ _)) hCM hψ hF hΦ hd' hA'.1
  obtain ⟨c', hc'⟩ := GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ _ _ M.co 1 Complex.I A C Φ
    (om.comp (MonoidHom.inr _ _)) hCM hψ hF hΦ hB.1
  exact ⟨P, Q, R, S, A, C, Φ, c, c', hF, hΦ.1,
    _root_.GlobalTheory.HoweD.PolRangeD.polRangeD F E σ n d P Q R S X W M ψ τ A C Φ hCM hψ hF hθA hθC hΦ, hc, hc'⟩

end GlobalTheory.HoweD.FockData

end
end

