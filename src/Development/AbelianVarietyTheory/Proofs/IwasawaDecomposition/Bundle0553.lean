module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuples
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_der_of_rsp {k R : Type} [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Algebra.FormallySmooth k (ResidueField R)] (ψ : R →+* ℂ) [IsLocalHom ψ] (m : ℕ)
    (f : Fin m → R) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m f) (l : Fin m → ℂ) (hl : l ≠ 0) :
    ∃ D : R →+ ℂ, (∀ a : k, D (algebraMap k R a) = 0) ∧
      (∀ x y, D (x * y) = ψ x * D y + ψ y * D x) ∧ ∑ i, l i * D (f i) ≠ 0 := by
  classical
  obtain ⟨hspan, hdim⟩ := hf
  have hfm : ∀ i, f i ∈ maximalIdeal R := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩
  have hv : Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    have e : Set.range v = (maximalIdeal R).toCotangent '' Set.range
        (fun i => (⟨f i, hfm i⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]; rfl
    rw [e, CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hspan
  have hfr : Module.finrank (ResidueField R) (CotangentSpace R) = m := by
    apply le_antisymm
    · rw [← finrank_top (ResidueField R) (CotangentSpace R), ← hv]
      exact (finrank_range_le_card v).trans (by simp)
    · have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
      rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hdim] at h1
      exact_mod_cast h1
  have hli : LinearIndependent (ResidueField R) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hfr])
  let b := Module.Basis.mk hli hv.ge
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hl

  let emb : ResidueField R →+* ℂ := ResidueField.lift ψ
  have hemb : ∀ r : R, emb (residue R r) = ψ r := fun r => ResidueField.lift_residue_apply ψ r
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[k] ResidueField R :=
    Ideal.Quotient.liftₐ (maximalIdeal R ^ 2) (IsScalarTower.toAlgHom k R (ResidueField R))
      (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha))
  have hgr : ∀ r : R, g (Ideal.Quotient.mk _ r) = residue R r := fun r => rfl
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨Ideal.Quotient.mk _ r, hgr r⟩
  have hnil : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, le_bot_iff.1 ?_⟩
    rw [pow_two (RingHom.ker g), Ideal.mul_le]
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).1 ((hgr r).symm.trans (RingHom.mem_ker.1 hx))
    have hs : s ∈ maximalIdeal R := (residue_eq_zero_iff s).1 ((hgr s).symm.trans (RingHom.mem_ker.1 hy))
    rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hr hs
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil
  have hs : ∀ c, g (s c) = c := fun c =>
    congrArg (fun φ : ResidueField R →ₐ[k] ResidueField R => φ c)
      (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil)
  let t : ResidueField R → R := fun c => Function.surjInv Ideal.Quotient.mk_surjective (s c)
  have ht : ∀ c, Ideal.Quotient.mk (maximalIdeal R ^ 2) (t c) = s c := fun c =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (s c)
  have hrt : ∀ c, residue R (t c) = c := fun c => by rw [← hgr, ht, hs]
  let e : R → R := fun r => r - t (residue R r)
  have he : ∀ r, e r ∈ maximalIdeal R := fun r =>
    (residue_eq_zero_iff _).1 (by simp only [e, map_sub, hrt, sub_self])
  have hmk : ∀ a : R, Ideal.Quotient.mk (maximalIdeal R ^ 2) a = 0 → a ∈ maximalIdeal R ^ 2 :=
    fun a h => Ideal.Quotient.eq_zero_iff_mem.1 h
  have hcot : ∀ (a a' : R) (ha : a ∈ maximalIdeal R) (ha' : a' ∈ maximalIdeal R),
      a - a' ∈ maximalIdeal R ^ 2 →
      (maximalIdeal R).toCotangent ⟨a, ha⟩ = (maximalIdeal R).toCotangent ⟨a', ha'⟩ :=
    fun a a' ha ha' h => (Ideal.toCotangent_eq _).2 h
  let D0 : R → ℂ := fun r => emb (b.repr ((maximalIdeal R).toCotangent ⟨e r, he r⟩) j)
  have hadd : ∀ x y, D0 (x + y) = D0 x + D0 y := by
    intro x y
    have h1 : (maximalIdeal R).toCotangent ⟨e (x + y), he (x + y)⟩ =
        (maximalIdeal R).toCotangent ⟨e x + e y, add_mem (he x) (he y)⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      simp only [e, map_sub, map_add (f := _), ht]
      ring
    have h2 := map_add (maximalIdeal R).toCotangent ⟨e x, he x⟩ ⟨e y, he y⟩
    simp only [D0, h1]
    rw [show (⟨e x + e y, add_mem (he x) (he y)⟩ : maximalIdeal R) = ⟨e x, he x⟩ + ⟨e y, he y⟩ from rfl,
      h2, map_add, Finsupp.add_apply, map_add]
  have hmul : ∀ x y, D0 (x * y) = ψ x * D0 y + ψ y * D0 x := by
    intro x y
    have hm2 : ∀ a b : R, a ∈ maximalIdeal R → b ∈ maximalIdeal R → a * b ∈ maximalIdeal R ^ 2 :=
      fun a b ha hb => by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    have h1 : (maximalIdeal R).toCotangent ⟨e (x * y), he (x * y)⟩ =
        (maximalIdeal R).toCotangent (t (residue R x) • (⟨e y, he y⟩ : maximalIdeal R) +
          t (residue R y) • (⟨e x, he x⟩ : maximalIdeal R)) := by
      refine hcot _ _ _ _ ?_
      have q : e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) =
          e x * e y + (t (residue R x) * t (residue R y) - t (residue R (x * y))) := by
        simp only [e]; ring
      change e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) ∈ _
      rw [q]
      refine add_mem (hm2 _ _ (he x) (he y)) (hmk _ ?_)
      rw [map_sub, map_mul, ht, ht, ht, map_mul, map_mul, sub_self]
    simp only [D0, h1, map_add (f := _), map_smul]
    rw [← algebraMap_smul (ResidueField R) (t (residue R x)),
      ← algebraMap_smul (ResidueField R) (t (residue R y)), map_smul, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, ResidueField.algebraMap_eq, hrt, hrt, hemb, hemb]
  let D : R →+ ℂ := AddMonoidHom.mk' D0 hadd
  refine ⟨D, fun a => ?_, hmul, ?_⟩
  · change D0 _ = 0
    have h1 : (maximalIdeal R).toCotangent ⟨e (algebraMap k R a), he _⟩ =
        (maximalIdeal R).toCotangent ⟨0, zero_mem _⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      have r1 : residue R (algebraMap k R a) = algebraMap k (ResidueField R) a :=
        (IsScalarTower.algebraMap_apply k R (ResidueField R) a).symm
      show Ideal.Quotient.mk _ (algebraMap k R a - t (residue R (algebraMap k R a)) - 0) = 0
      rw [sub_zero, map_sub, ht, r1, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, sub_self]
    simp only [D0, h1]
    rw [show (⟨0, zero_mem _⟩ : maximalIdeal R) = 0 from rfl, map_zero, map_zero, Finsupp.zero_apply,
      map_zero]
  · have hfi : ∀ i, D0 (f i) = emb (Finsupp.single i 1 j) := by
      intro i
      have h1 : (maximalIdeal R).toCotangent ⟨e (f i), he _⟩ = b i := by
        rw [Module.Basis.mk_apply]
        refine hcot _ _ _ _ (hmk _ ?_)
        have r0 : residue R (f i) = 0 := (residue_eq_zero_iff _).2 (hfm i)
        show Ideal.Quotient.mk _ (f i - t (residue R (f i)) - f i) = 0
        rw [r0, sub_sub_cancel_left, map_neg, ht, map_zero, neg_zero]
      simp only [D0, h1, Module.Basis.repr_self]
    change ∑ i, l i * D0 (f i) ≠ 0
    simp only [hfi]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_apply, if_neg hi, map_zero, mul_zero])
      (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, map_one, _root_.mul_one]
    exact hj

end GlobalTheory.PtDerivSep

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_ptDer_sep : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  intro k _ _ Y p n σ hsm x₀ U hy m f hR l hl
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  let c : k →+* Γ(Y, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1
  have hft : c.FiniteType := (p.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let germ : Γ(Y, U.1) →+* Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    (Y.presheaf.germ U.1 _ hy).hom
  have hloc : germ.EssFiniteType := by
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk _)
      (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl
  have hnoeth : IsNoetherianRing (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := by
    letI := c.toAlgebra
    haveI : Algebra.FiniteType k Γ(Y, U.1) := hft
    haveI : IsNoetherianRing Γ(Y, U.1) := Algebra.FiniteType.isNoetherianRing k _
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl _ inferInstance
  letI : Algebra k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := (germ.comp c).toAlgebra
  haveI : Algebra.EssFiniteType k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) :=
    RingHom.essFiniteType_algebraMap.1 (hft.essFiniteType.comp hloc)
  haveI : Algebra.EssFiniteType k (ResidueField (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))) :=
    .of_surjective (IsScalarTower.toAlgHom k _ _) residue_surjective
  let ψ := (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x₀.1).hom
  obtain ⟨D, h1, h2, h3⟩ := exists_der_of_rsp (k := k) ψ m _ hR l hl
  have hx : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have hψ : ∀ g, ψ (germ g) = CxPts.ev p σ U.1 g x₀ := by
    intro g
    rw [CxPts.ev_eq hx, CxPts.evHom, ← GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x₀.1 U.1 hx]
    rfl
  refine ⟨D.comp germ.toAddMonoidHom, fun a => h1 a, fun g h => ?_, h3⟩
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, h2, hψ]

end GlobalTheory.PtDerivSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TransportLimit

theorem val_frame {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} (t : Frame L p) (ht : t.IsGen) {j₀ : L.ι}
    (h₀ : ⊤ ≤ LB.wchart L (K := PUnit) (fun _ => p) (fun _ => j₀)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t r z J = gm (r ≫ p) z _ (L.g (J (r ≫ p)) j₀) * gm r z ⊤ (res h₀ (t.s (fun _ => j₀))) := by
  refine (gen_trans ht r z (hJ.mem _ r) (h₀ (show r z ∈ (⊤ : Y.Opens) from trivial))).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z h₀ (show r z ∈ (⊤ : Y.Opens) from trivial) _).symm)
  simp only [trF, Fintype.prod_unique, zpow_one]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem gw_change (U : UnifPre I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.toPre.P.A.left} (hp : xe ≫ (fstG I e G).left = p)
    (hq : xe ≫ (U.gt e).pG.left = q) {j j' : D.toPre.P.L.ι} {k k' : U.LG.L.ι} (hj : q z ∈ D.toPre.P.L.U j)
    (hj' : q z ∈ D.toPre.P.L.U j') (hk : p z ∈ U.LG.L.U k) (hk' : p z ∈ U.LG.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.toPre.P.L.g j j') * (gm p z _ (U.LG.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk)
    (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_limit_unit (U : UnifPre I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.toPre.P.A.left)
    (hb : Lies U x b) {jL : U.LG.L.ι} {jM : D.toPre.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.LG.L.U jL)
    (hM : ⊤ ≤ b ⁻¹ᵁ D.toPre.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using GlobalTheory.FormalValue.exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.LG.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.LG.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.toPre.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.toPre.P.L.U jM) (hb e Z r xe h)).mpr
      (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from GlobalTheory.thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (GlobalTheory.FormalValue.toStkA_map_valR _ _ _ _ (ht _) _).trans
      (Eq.trans ?_ (GlobalTheory.FormalValue.toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact GlobalTheory.FormalValue.wv_comp_thickMap e (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := GlobalTheory.FormalValue.exists_unit_limit (I.map φ) _ hc fun e =>
    GlobalTheory.FormalValue.isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := GlobalTheory.NormGen.exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := GlobalTheory.FormalValue.fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, GlobalTheory.NormGen.gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1,
    map_one, map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← GlobalTheory.NormGen.gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := GlobalTheory.FormalValue.valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [GlobalTheory.NormGen.valR_id, Category.comp_id] at k
  exact k

theorem exists_frRel : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (W : Type) [CommRing W] [IsLocalRing W] (φ : R →+* W) [IsAdicComplete (I.map φ) W] (x' : Sp W ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ b : Sp W ⟶ D.toPre.P.A.left, Lies U x' b → ∃ (g' : Frame U.LG.L x') (g : Frame D.toPre.P.L b), g'.IsGen ∧ g.IsGen ∧ FrRel U x' b g' g := by
  intro R _ _ I D A G _ _ U W _ _ φ _ x' hx b hb
  obtain ⟨jL, hjL⟩ := exists_chart U.LG.isLB (x' (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.toPre.P.isLB (b (cpt W))
  replace hjL := (top_le_iff_cpt (A := W) x' _).2 hjL
  replace hjM := (top_le_iff_cpt (A := W) b _).2 hjM
  obtain ⟨a, ha⟩ := exists_limit_unit U φ x' hx b hb hjL hjM
  obtain ⟨ν', hν'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) U.LG.L U.LG.isLB (K := PUnit) (fun _ => x') (fun _ => 1)
  obtain ⟨ν, hν⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := W) D.toPre.P.L D.toPre.P.isLB (K := PUnit) (fun _ => b) (fun _ => 1)
  have tL : ⊤ ≤ LB.wchart U.LG.L (K := PUnit) (fun _ => x') (fun _ => jL) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjL (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  have tM : ⊤ ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => b) (fun _ => jM) := fun y _ =>
    Set.mem_iInter.2 fun _ => hjM (show y ∈ (⊤ : (Sp W).Opens) from trivial)
  refine ⟨GlobalTheory.UU.scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν', GlobalTheory.UU.scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν,
    GlobalTheory.UU.scaleGen_isGen _ hν', GlobalTheory.UU.scaleGen_isGen _ hν, ?_⟩
  intro e Z r y hy z JM JL hJM hJL
  have hyb := hb e Z r y hy
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h =>
    h (show r z ∈ (⊤ : (Sp W).Opens) from trivial)
  have v₁ := GlobalTheory.UU.val_scaleGen (res tL (ν'.s fun _ => jL))⁻¹ ν' r hJL
  rw [val_frame ν' hν' tL r z hJL] at v₁
  have v₂ := GlobalTheory.UU.val_scaleGen (a⁻¹ * (res tM (ν.s fun _ => jM))⁻¹) ν r hJM
  rw [val_frame ν hν tM r z hJM] at v₂
  have w₁ : wVal U e z JM JL y = gm (r ≫ b) z _ (D.toPre.P.L.g (JM (r ≫ b)) jM) *
      (gm (r ≫ x') z _ (U.LG.L.g (JL (r ≫ x')) jL))⁻¹ * gw (U.w e) y z jM (fun _ => jL) :=
    (congrArg₂ (fun j k => gw (U.w e) y z (JM j) (fun _ => JL k)) hyb hy).trans
      (gw_change U e y z hy hyb (hJM _) (m hjM) (hJL _) (m hjL))
  rw [eq_inv_of_mul_eq_one_right (ha e Z r y hy z)] at w₁
  rw [v₁, v₂, w₁]
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TransportLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCore
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoHalfTop

theorem exists_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  intro hC D G _ _ Pl0 T0 A T _ R hvol hJ hcore halg hpb hpre hval hfr hLL hfin hQ hstd hn
  obtain ⟨dict, mu, chiW, x₀, htie, hcore₁⟩ := _root_.GlobalTheory.RealGeo.exists_tieIn_reCore D G Pl0 T0 A T R hvol hJ hcore halg hpre.lev hval hfr
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hpre.lev hpre.fam hpre.models hpre.thP
  obtain ⟨O, hO⟩ := _root_.GlobalTheory.RefPins.exists_omPins D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) hpre hLL htie hpb hQ hstd
  choose cc hcc0 hcc using fun i => _root_.GlobalTheory.RealGeo.exists_const_oneMapOf_all D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O hpre htie
    hpb hfin hQ hio i (hstd i) (hO i)
  obtain ⟨cE, hcE, htie₂, hO₂, hF⟩ := GlobalTheory.T.exists_core_constants_base_solution_equivariant D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O cc
    hpre.lev htie hpb hO hcc0
  obtain ⟨B, hκ, hv, hFB, hpre₂, hchi⟩ := _root_.GlobalTheory.RealGeo.exists_geoHalf_geoR D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O
    (fun _ => 1) hpre htie₂ hO₂ hF
  obtain ⟨hin, hU, hI⟩ := _root_.GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hC D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) _ (fun _ => 1) B hpre₂ hchi hpb hn
  refine ⟨dict, mu, chiW, x₀, cE, _, _, B, hκ, hin, hFB, fun i => ⟨⟨_, _, hFB.1 i⟩, fun _ => ?_⟩,
    GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ _ hpre₂.lev hpre₂.fam hpre₂.models hpre₂.thP, hpre₂, hchi, hU, hI, hcore₁⟩
  obtain ⟨O', h1, h2, h3⟩ := hcc i
  obtain ⟨O'', e1, -, p1, p2⟩ := _root_.GlobalTheory.RealGeo.omDat_updFW D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R)
    (nTop (reCore T dict mu chiW x₀ cE) (kapTop D)) (formsGeo (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O) i T0 id O'
  rw [hκ, hv]
  refine ⟨O'', ?_, p1 h2, ?_⟩
  · rw [e1]; exact h1
  · rw [← hcE i] at h3
    exact p2 _ _ h3

end GlobalTheory.GeoHalfTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem span_plk_uvec_eq_top {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
    {c D : Let m → Fin (M + 1) → Γ(X, U.1)} (h : LeftInv D c) (w : Pm m) (en : En m) :
    Ideal.span (Set.range (plk (uvec c w) en.2.1)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2 ⟨_,
    (_root_.GlobalTheory.FlagEmb.CauchyBinet.main.2 T m (CR m U) M _ _ w MvPolynomial.X
      (h.map (MvPolynomial.C : Γ(X, U.1) →+* CR m U))).1 en.1 en.2.1 en.2.2⟩)

theorem exists_isPlk : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D →
    ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
      (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  intro O K _ _ β X s T _ m M B V α c D hs hC
  obtain ⟨P, p0, p, hP, hp, univ⟩ := _root_.GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod O (En m) X s (fun en => PSpace O (plN M en.1))
    (fun en => PSpace.str O _) hs fun en => ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hb : ∀ b, cbase m (V b) ≫ s =
      spMap ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) := fun b => by
    rw [cbase, Category.assoc, hC.ovr b, ← Spec.map_comp]
    rfl
  have pt_str : ∀ {A : Type} [CommRing A] {N : ℕ} (c : O →+* A)
      (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro A _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  choose h hh using fun (b : B) (w : Pm m) => (univ _ (cbase m (V b))
    (fun en => pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1)
      (span_plk_uvec_eq_top (hC.inv b) w en))
    fun en => (pt_str _ _ _).trans (hb b).symm).exists
  refine ⟨P, p0, p, h, ⟨fun b w => (hh b w).1, fun b w en => ⟨_, (hh b w).2 en⟩⟩, hP, hp, fun Z a a' h0 h1 => ?_⟩
  exact (univ Z (a ≫ p0) (fun en => a ≫ p en) fun en => by
    rw [Category.assoc, hp, Category.assoc]).unique ⟨rfl, fun _ => rfl⟩ ⟨h0.symm, fun en => (h1 en).symm⟩

end GlobalTheory.FlagEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open GlobalTheory.LineNorm GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.LineNorm.Glue

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

variable {Δ : Y.Dv} {t : Y.X → Y.Fnˣ} {φ : PtFn Y}

theorem below_mem (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    N.j (below y.1) ∈ W := by
  change (y.1 ≫ N.j) _ ∈ W
  rw [← h]
  exact hW (x := spMap e.O.subtype _) trivial

theorem w_le_one (N : TrueGeo.Model Y) {v : HeightOneSpectrum (𝓞 F)} {e : Ext v} {y : AlgPt Y}
    {yt : Sp e.O ⟶ N.X} (h : spMap e.O.subtype ≫ yt = y.1 ≫ N.j) {W : N.X.Opens} (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    (g : Γ(N.X, W)) (hg : genericPoint Y.X ∈ N.j ⁻¹ᵁ W) :
    e.w (valAt y.1 (fnOf (N.j ⁻¹ᵁ W) hg (N.j.app W g))) ≤ 1 := by
  have hb : below y.1 ∈ N.j ⁻¹ᵁ W := below_mem N h hW
  have ht : ⊤ ≤ y.1 ⁻¹ᵁ (N.j ⁻¹ᵁ W) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W
    rw [← h]
    exact hW (x := spMap e.O.subtype p) trivial
  have hev := OfModel.eval_pull e.O.subtype N.j y.1 yt h (U := W) (W := N.j ⁻¹ᵁ W) le_rfl ht hW g
  rw [OfModel.valAt_fnOf _ hb ht, Scheme.Hom.app_eq_appLE, hev, ← e.mem_O]
  exact Subtype.prop _

end GlobalTheory.LineNorm.Glue
end
end

