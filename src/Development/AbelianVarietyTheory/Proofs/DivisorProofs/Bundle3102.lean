module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkew
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTSkew


set_option maxHeartbeats 1000000 in
theorem skew_of_isFilLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  intro p _ D R _ b N k _ t o₀ φ hφ o' m' x _ y _ x₁ y₁ hx hy
  have HR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have HD : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  obtain ⟨g', hg'⟩ := GlobalTheory.KSGraph.exists_dim o'.A o'.ab
  obtain ⟨l₁, l₂⟩ := m'.sq
  have C : GlobalTheory.AbDual.CupSquare (epsDP k) (GlobalTheory.DeRham.epsRed k) (o₀.A ⊗ o₀.A) :=
    GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod HR.1 HD.2 (isDPNilpotent_squareZero (SqExt.dual k).sq)
    (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl o'.ab hg' o'.ab hg' m'.cart m'.cart
  have iso : LBIso (o₀.P.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A)))) o₀.P :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₀.isLB _) o₀.isLB).1
      (by
        calc
          _ = GlobalTheory.CechPic.pull (Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (GlobalTheory.CechPic.cls o₀.P o₀.isLB) := GlobalTheory.CechPic.cls_pull o₀.isLB _ _
          _ = _ := by rw [Over.id_left, GlobalTheory.CechPic.pull_id])
  obtain ⟨φ', hφ', e'⟩ := hφ.pull o₀.isLB (constMor o₀.A) (constMor o₀.A)
    (h := Over.Hom.left (𝟙 (o₀.A ⊗ o₀.A))) (by simp) (by simp) o₀.isLB iso
  have van := GlobalTheory.BirigidLift.vanish_of_lift HR o'.ab hg' o'.ab hg' m'.cart m'.cart l₁ l₂ C o'.isLB o'.rig₁
    o'.rig₂ o₀.isLB (LBIso.symm m'.pol) hφ'
  have hm := GlobalTheory.HTRealise.isBC_constMor o₀.ab
  obtain ⟨xc, hxc⟩ := hm.exists x
  obtain ⟨yc, hyc⟩ := hm.exists y
  obtain ⟨x₁c, hx₁c⟩ := hm.exists x₁
  obtain ⟨y₁c, hy₁c⟩ := hm.exists y₁
  obtain ⟨d, hd, ed⟩ := hx
  obtain ⟨d', hd', ed'⟩ := hy
  have dx : d = xc + (DualNumber.eps : DualNumber k) • x₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed c, LinearMap.add_apply, LinearMap.smul_apply, hxc c, hx₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have dy : d' = yc + (DualNumber.eps : DualNumber k) • y₁c := GlobalTheory.HTRealise.crys_ext o₀.ab fun c ↦ by
    rw [ed' c, LinearMap.add_apply, LinearMap.smul_apply, hyc c, hy₁c c]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have z : φ' d d' = 0 := van d hd d' hd'
  rw [dx, dy] at z
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    e' _ _ _ _ hxc hyc, e' _ _ _ _ hx₁c hyc, e' _ _ _ _ hxc hy₁c, e' _ _ _ _ hx₁c hy₁c] at z
  have z2 := congrArg TrivSqZeroExt.snd z
  simp [TrivSqZeroExt.algebraMap_eq_inl] at z2
  linear_combination z2

end GlobalTheory.HTSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandAdmissibleStable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform


open GlobalTheory.Published.GrothendieckMessing in
theorem liftFil_isCompl_red_stable : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl (liftFil (divided₂ hsq) m.cart) M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ liftFil (divided₂ hsq) m.cart, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ liftFil (divided₂ hsq) m.cart, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ liftFil (divided₂ hsq) m.cart) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m _ _
  have HC := canonical_of_abelianDeRham _root_.GlobalTheory.abelianDeRham (isDPNilpotent_squareZero hsq) hπ rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  obtain ⟨bij, ⟨M, hM⟩, hAdm⟩ := HC g o₀.A o.A m.φ m.cart o.ab hg
  have bijD := HC.crysToDR_bijective m.cart o.ab hg
  let e := LinearEquiv.ofBijective (crysToDR (divided₂ hsq) m.cart) bijD
  refine ⟨⟨M.comap (crysToDR (divided₂ hsq) m.cart), (Submodule.orderIsoMapComap e).symm.isCompl hM⟩,
    fun y ↦ ?_, fun c d hd ↦ ?_⟩
  · rw [hAdm y]
    constructor
    · rintro ⟨x, hx, ex⟩
      obtain ⟨d, rfl⟩ := bijD.2 x
      exact ⟨d, hx, (corr_crysToDR_iff rfl m.cart bij.2 d y).1 ex⟩
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, hd, (corr_crysToDR_iff rfl m.cart bij.2 d y).2 ed⟩
  · haveI := o₀.act.hom c
    haveI := o.act.hom c
    exact push_mem_liftFil (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm hd

end GlobalTheory.HTDeform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftHodgeSummandCrystallineLie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

namespace GlobalTheory.HTLiftLie

theorem lie_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (s : Sp C ⟶ Sp R) (s₀ : Sp C₀ ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), s = spMap tR → s₀ = spMap π ≫ spMap tR → ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) m.cart → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) m.cart) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) m.cart := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR s s₀ o₀ o m hs _ d hd
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C o.A o.ab
  have bij : Function.Bijective (crysToDR (divided₂ hsq) m.cart) :=
    GlobalTheory.Published.AbelianDeRham.Rigid.crysToDR_bijective GlobalTheory.abelianDeRham.2.2.2.1 o.ab hg (isDPNilpotent_squareZero hsq) hπ rfl
      m.cart
  have key : ∀ (c : D.O) (x : Crys (divided₂ hsq) (spMap π) o₀.A),
      crysToDR (divided₂ hsq) m.cart (haveI := o₀.act.hom c; push (divided₂ hsq) (spMap π) (o₀.act.act c) x) =
        GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act c (crysToDR (divided₂ hsq) m.cart x) := by
    intro c x
    haveI := o₀.act.hom c
    haveI := o.act.hom c
    rw [GlobalTheory.HTSummand.crysAct_apply]
    exact crysToDR_push (divided₂ hsq) m.cart m.cart (o₀.act.act c) (o.act.act c) (m.act c).symm x
  have hy : GlobalTheory.HTSummand.crysAct (dp0 C) (𝟙 _) o.act (algebraMap (𝓞 D.F) D.O D.ω) (crysToDR (divided₂ hsq) m.cart d) -
      tR b.ρ • crysToDR (divided₂ hsq) m.cart d ∈ Fil o.A := by
    have h' := hd
    rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key] at h'
    exact h'
  obtain ⟨w', hw', hsum⟩ := GlobalTheory.HTSummand.lie_mod_fil p D R b N C tR s hs o _ hy
  choose w hw using fun i => bij.2 (w' i)
  refine ⟨w, fun i c => ?_, ?_⟩
  · rw [liftFil, Submodule.mem_comap, map_sub, map_smul, key, hw i]
    exact hw' i c
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [liftFil, Submodule.mem_comap, map_sub, map_sum]
      simp only [hw]
      exact hsum

end GlobalTheory.HTLiftLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTDefLift

theorem lie_of_liftFil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ liftFil (divided₂ hsq) h → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → ∀ v : GlobalTheory.UPel.HT.epsPtR x ⟶ A, GlobalTheory.UPel.HT.IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (GlobalTheory.UPel.HT.epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, GlobalTheory.UPel.HT.IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hL R' _ β x hx
  exact _root_.GlobalTheory.HTLieSpread.lieAt_spread p D R b C tR A hA.smooth act
    (GlobalTheory.T.harrisTaylor_lie_condition_identity_of_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hL) R' β x hx

end GlobalTheory.HTDefLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeformaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  first | (exact @GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (exact GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (intros; apply GlobalTheory.UPel.HT.PolIsoLift.pol_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem isMonHom_id_npow {Y : Scheme.{0}} (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  have h := Grp.Hom.hom_hom_zpow (G := Grp.mk A) (H := Grp.mk A) (𝟙 _) (n : ℤ)
  have h' : IsMonHom ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (n : ℤ)).hom.hom := inferInstance
  rw [h, zpow_natCast] at h'
  exact h'

theorem polKer_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, hc⟩ hB hq
  have hpY : IsUnit ((p : ℕ) : Γ(Y, ⊤)) := by
    have := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  have hn : IsUnit ((c ^ 3 : ℕ) : Γ(Y, ⊤)) := by
    rw [hc, ← pow_mul, Nat.cast_pow]
    exact hpY.pow _
  obtain ⟨C, _, Q, h, hC, -, -, hh, -, hT⟩ := GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom p D R b N Y s o B ψ' hB hq.2.1
  haveI := isMonHom_id_npow B c
  have hcomp : ∀ {T : Over Y} (x : T ⟶ B), x ≫ (𝟙 B) ^ c = x ^ c := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨W₁, o₁, c₁, H₁, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => C) (fun _ => h) B ((𝟙 B) ^ c) hB
    (fun _ => hC) hB (fun _ => hh) inferInstance hn
  obtain ⟨W₂, o₂, c₂, H₂, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => B) (fun _ => (𝟙 B) ^ c) C h hB
    (fun _ => hB) hC (fun _ => inferInstance) hh hn
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t => ?_⟩
  rw [Set.subset_inter_iff, H₁, H₂]
  constructor
  · rintro ⟨h₁, h₂⟩ T σ hσ x hx
    rw [hT]
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · rw [← hcomp]; exact h₁ T σ hσ x hx fun _ => hx'
    · exact h₂ T σ hσ x hx fun _ => by rw [hcomp]; exact hx'
  · intro H
    refine ⟨fun T σ hσ x hx hx' => ?_, fun T σ hσ x hx hx' => ?_⟩
    · rw [hcomp]; exact ((H T σ hσ x hx).1 ((hT T x).2 (hx' ())))
    · exact (hT T x).1 ((H T σ hσ x hx).2 (by rw [← hcomp]; exact hx' ()))

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentable
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem relRep_htPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (Z : Scheme.{0}) (π : Z ⟶ S) (u : Obj b N (π ≫ t)) (φu : u.A.left ⟶ c.A.left) (φ₂u : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A c.A π φu ∧ IsSquare φu φ₂u ∧ LBIso u.P (c.P.pull φ₂u) ∧ IsFinite π ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (t' : T ⟶ Sp R) (o : Obj b N t') (φ : o.A.left ⟶ c.A.left) (φ₂ : (G2 o.A).left ⟶ (G2 c.A).left), g ≫ t = t' → IsGrpPullback o.A c.A g φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → ∃! z : T ⟶ Z, z ≫ π = g ∧ ∃ m : ObjMap o u z, m.φ ≫ φu = φ := by
  intro p _ D R _ b N hN hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨E, πE, AE, _, _, φE, φ₂E, actE, ηE, hEn, hEf, pbE, sqE, rosE, etaE, univE⟩ :=
    GlobalTheory.T.exists_rep_adjointAction_level_siegelPullback p D R b N hNp h M B ζ S s₁ t c e he hc
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE φE φ₂E actE ηE
    pbE sqE rosE etaE
  have hZj := (hZ Z j).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨u, ψ, ψ₂, pbu, squ, isou, actu, etau⟩ := GlobalTheory.T.exists_harrisTaylorObject_over_lieTate_locus p D R b N hN hNp h M B ζ S s₁ t c e he hc E πE AE
    φE φ₂E actE ηE pbE sqE rosE etaE Z j hZj.1 hZj.2
  haveI : IsFinite πE := hEf
  haveI : Mono j := inferInstance
  refine ⟨Z, j ≫ πE, u, ψ ≫ φE, ψ₂, pbu.comp pbE, squ, isou, inferInstance, ?_⟩
  intro T g t' o φ φ₂ hgt pbo sqo isoo
  have rosO : RosatiFor D o.act (c.P.pull φ₂) :=
    RosatiFor.of_iso o.isLB (pull_isLB c.isLB _) isoo o.rosatiFor
  obtain ⟨z₀, ⟨hz₀, ψ₀, pb₀, hψ₀, act₀, eta₀⟩, uniq₀⟩ := univE T g o.A φ φ₂ o.act o.eta pbo sqo rosO o.etaOK
  have pbo' : IsGrpPullback o.A c.A (z₀ ≫ πE) φ := by rw [hz₀]; exact pbo
  have tr := GlobalTheory.T.harrisTaylorLie_tate_conditions_iff_pullbacks p D R b N S c.A c.P c.isLB E T πE z₀ AE o.A φE φ₂E φ φ₂ ψ₀ actE o.act ηE o.eta o.P
    o.isLB pbE sqE pbo' sqo pb₀ hψ₀ isoo act₀ eta₀
  have hpt : ∀ {R' : Type} [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ z₀ ≫ πE ≫ t = spMap β →
      x ≫ t' = spMap β := fun β x hx => by
    rw [← hgt, ← hz₀]; simpa [Category.assoc] using hx
  obtain ⟨z, hz⟩ := (hZ T z₀).2 ⟨fun R' _ β x hx => (tr.1 R' β x).1 (o.lieHer R' β x (hpt β x hx)),
    fun k _ _ x β hx => (tr.2 k x).1 (o.geomAt k x β (hpt β x hx))⟩
  have w : ψ₀ ≫ AE.hom = (o.A.hom ≫ z) ≫ j := by rw [pb₀.1.w, Category.assoc, hz]
  let ψ' := pbu.1.lift ψ₀ (o.A.hom ≫ z) w
  have h1 : ψ' ≫ ψ = ψ₀ := pbu.1.lift_fst _ _ _
  have h2 : ψ' ≫ u.A.hom = o.A.hom ≫ z := pbu.1.lift_snd _ _ _
  have hact : ∀ a : D.O, (o.act.act a).left ≫ ψ' = ψ' ≫ (u.act.act a).left := fun a => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, act₀, Category.assoc, actu, ← Category.assoc, h1]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.act.act a), h2, ← Category.assoc,
        Over.w (o.act.act a)]
  have heta : ∀ y, (o.eta y).left ≫ ψ' = z ≫ (u.eta y).left := fun y => by
    apply pbu.1.hom_ext
    · rw [Category.assoc, h1, eta₀, Category.assoc, etau, ← Category.assoc, hz]
    · rw [Category.assoc, h2, Category.assoc, Over.w (u.eta y), ← Category.assoc, Over.w (o.eta y)]
      simp
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_harrisTaylorObjectMap_of_common_pullback p D R b N S c.A c.P c.isLB T Z t' ((j ≫ πE) ≫ t) o u g (j ≫ πE) z φ φ₂
    (ψ ≫ φE) ψ₂ ψ' pbo sqo isoo (pbu.comp pbE) squ isou (by rw [← Category.assoc, hz, hz₀])
    (by rw [← Category.assoc, h1, hψ₀]) h2 hact heta
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₀], m, by rw [hm, ← Category.assoc, h1, hψ₀]⟩, ?_⟩
  rintro z' ⟨hz', m', hm'⟩
  have e₀ : z' ≫ j = z₀ := uniq₀ (z' ≫ j) ⟨by rw [Category.assoc]; exact hz', m'.φ ≫ ψ, m'.cart.comp pbu,
    by rw [Category.assoc]; exact hm',
    fun a => by rw [← Category.assoc, m'.act a, Category.assoc, actu]; exact (Category.assoc _ _ _).symm,
    fun y => by rw [← Category.assoc, m'.eta y, Category.assoc, etau]; exact (Category.assoc _ _ _).symm⟩
  exact (cancel_mono j).1 (e₀.trans hz.symm)

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValues
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

theorem heat_values_of_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ → ∃ (iota : Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) →+* (FractionRing Ω)) (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, iota (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = (algebraMap Ω (FractionRing Ω)) (φ r)) ∧ (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (iota.mapMatrix Θ₁) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' D Ω _ _ _ φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL
    Θ₁ DV hDV hKS
  have hc : (∏ i, tt i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  obtain ⟨iota, hiota⟩ := _root_.GlobalTheory.HeatV.fracIotaBasicOpen E H R t (∏ i, tt i) hc Ω φ x' hx' hinj
  obtain ⟨J, W, j, d, u, pf, pf', hW, hcov, hle, hfld, hlift, hglue⟩ :=
    _root_.GlobalTheory.HeatV.exists_heat_abLocus E H R t P m tt gam hmon htt hab _ rfl n v' D dd' hinv Θ₁ DV hDV hKS
  obtain ⟨dt, u', p, p', hdt, hval⟩ := _root_.GlobalTheory.HeatVal.value_opV_ringOp E H R t _ hc n v' D Ω φ x' δ dd' hcomp hx' hinv hδ hdd hinj g hg δL hδL Θ₁ DV hDV
    iota hiota J W j d u pf pf' hW hcov hle hfld hlift hglue
  refine ⟨iota, dt, u', p, p', hiota, hdt, ?_⟩
  rintro k hk s ⟨r0, σ, ω, hr0, hv, hω⟩
  obtain ⟨r, σ', hr, hσ'⟩ := _root_.GlobalTheory.HeatVExt.heat_section E H R t _ hc n dd' (fun a => (hinv a).1) D Θ₁ DV hDV J W j d u pf pf' hW hcov hle hfld
    hlift hglue k σ r0
  obtain ⟨ω', hv', hω'⟩ := hval k hk σ σ' r r0 ω hσ' hv
  refine ⟨r * r0 ^ 2, σ', ω', mul_ne_zero hr (pow_ne_zero _ hr0), hv', ?_⟩
  have hz : ∀ a, δL a ((algebraMap Ω (FractionRing Ω)) (φ r0)) = 0 := fun a => by rw [hδL, hδ, map_zero]
  have hdc := hdt r0
  rw [hω', hω]
  simp only [map_mul, map_pow]
  generalize (algebraMap Ω (FractionRing Ω)) (φ r0) = c at hz hdc ⊢
  have h1 : ∀ a x, δL a (c * x) = c * δL a x := fun a x => by
    rw [Derivation.leibniz, hz, smul_zero, add_zero, smul_eq_mul]
  have h2 : dt (c * s) = c * dt s + s * dt c := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  simp only [ringOp, h1, h2, hdc, Finset.mul_sum]
  have e1 : ∀ a b, iota.mapMatrix Θ₁ a b * (c * δL a (δL b s)) = c * (iota.mapMatrix Θ₁ a b * δL a (δL b s)) :=
    fun a b => by ring
  have e2 : ∀ a, u' a * (c * δL a s) = c * (u' a * δL a s) := fun a => by ring
  simp only [e1, e2, ← Finset.mul_sum]
  ring

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteEtaleSurjectiveOfIsQuasiInv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem isFinite_etale_surjective_of_isQuasiInv : ∀ (Y : Scheme.{0}) (A B : Over Y) [GrpObj A] [GrpObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → IsUnit (k : Γ(Y, ⊤)) → IsQuasiInv k ψ ψ' → IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left := by
  intro Y A B _ _ k ψ ψ' hA hB hk hq
  obtain ⟨-, -, h1, h2⟩ := hq
  obtain ⟨⟨hAf, hAe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hk
  obtain ⟨⟨-, hBe⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B (hG := hB) hk
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h1, Over.comp_left] at hAf hAe
  rw [GlobalTheory.GrpTangent.mulN_eq_pow, ← h2, Over.comp_left] at hBe
  haveI := hB.proper
  haveI : IsSeparated (ψ'.left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI := IsSeparated.of_comp ψ'.left A.hom
  haveI := FormallyUnramified.of_comp ψ'.left ψ.left
  haveI := locallyOfFiniteType_of_comp ψ'.left ψ.left
  refine ⟨IsFinite.of_comp ψ.left ψ'.left, Etale.of_comp ψ.left ψ'.left, ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · refine ⟨fun b => ?_⟩
    have hu := hk.map (Y.evaluation ⊤ (B.hom.base b) trivial).hom
    rw [map_natCast, Nat.cast_zero] at hu
    exact absurd hu not_isUnit_zero
  · obtain ⟨-, hs, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB k hk0
    rw [← h2, Over.comp_left] at hs
    exact Surjective.of_comp ψ'.left ψ.left

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedHodgeFiltrationEqOfSameLiftsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A₁ A₂ : Over (Sp (DualNumber k))) [GrpObj A₁] [GrpObj A₂] (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₀.left ⟶ A₂.left) (h₁ : IsGrpPullback A₀ A₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₁) (h₂ : IsGrpPullback A₀ A₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i₂), IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ g : HdR A₀ → HdR A₀, (∀ x ∈ Fil A₀, IsFilLift h₁ x (g x)) → (∀ x ∈ Fil A₀, IsFilLift h₂ x (g x)) → liftFil (epsDP k) h₁ = liftFil (epsDP k) h₂ := by
  first | (exact @GlobalTheory.LiftFilEq.liftFil_eq) | (exact GlobalTheory.LiftFilEq.liftFil_eq) | (intros; apply GlobalTheory.LiftFilEq.liftFil_eq  <;> assumption)
end

