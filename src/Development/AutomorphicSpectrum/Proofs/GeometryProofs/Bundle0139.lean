module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0123

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenAtComponentStalk
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem mem_eigSp_iff_forall {R V O : Type} [CommRing R] [AddCommGroup V] [Module R V] [CommRing O]
    (ρ : O →+* Module.End R V) (τ : O →+* R) (u : V) :
    u ∈ eigSp ρ τ ↔ ∀ a, ρ a u = τ a • u := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem spMap_dualMap_id {A : Type} [CommRing A] : spMap (dualMap (RingHom.id A)) = 𝟙 _ := by
  have h : dualMap (RingHom.id A) = RingHom.id _ := RingHom.ext fun a => by
    show TrivSqZeroExt.inl (TrivSqZeroExt.fst a) + TrivSqZeroExt.inr (TrivSqZeroExt.snd a) = a
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq a
  rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem frame_of_stableEig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (σ : E →+* ℂ) (r : ℕ) (e : Fin r → (epsAt (Y.X.fromSpecStalk p.1) ⟶ Y.t.G)), (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc → StableEig Y.t (Y.X.fromSpecStalk p.1) κ σ e → ∃ b : Fin r → Z.V, (∀ i, Z.M.Extends p (b i) (e i)) ∧ (Z.eig σ).IsFrameAt b p := by
  classical
  intro E _ _ _ H D l Xo c U O _ β Y Z p κ σ r e hκ hs
  obtain ⟨F, _, _, ⟨MA⟩⟩ := lieModel_exists Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1)
  obtain ⟨ρA, hρA, -⟩ := lieModel_exists_unique_act Y.X Y.t.G (Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) F MA (𝓞 E)
    Y.t.act.act Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  have hg : spMap (genMap (Z.ξ₀ ≫ Y.j) p) ≫ Y.X.fromSpecStalk p.1 = Z.ξ₀ ≫ Y.j := LieTangent.spec_genMap _ p
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := Y.X.presheaf.stalk p.1) (Y.X.fromSpecStalk p.1) (Z.ξ₀ ≫ Y.j) (genMap (Z.ξ₀ ≫ Y.j) p) hg MA Z.M
  have h0 : IsEigFrame Y.t.act (Y.X.fromSpecStalk p.1) (((RingHom.id _).comp κ).comp (tauIn c σ)) e :=
    hs _ (RingHom.id _) _ (by simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]; exact Category.id_comp _) e (fun i => by rw [spMap_dualMap_id, Category.id_comp])
  choose f hf using fun i => MA.onto (e i) (h0.1 i).1
  have hfe : (fun k => MA.pt (f k)) = e := funext hf
  have hfr := ((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame Y.X (Y.X.presheaf.stalk p.1) Y.t.G (Y.X.fromSpecStalk p.1) F MA).2 (𝓞 E) Y.t.act ρA
    (((RingHom.id _).comp κ).comp (tauIn c σ)) hρA).2 r f
  rw [hfe] at hfr
  obtain ⟨-, hfs⟩ := hfr.1 h0
  have hb : ∀ i, (Z.M.pt (j (f i))).left = spMap (dualMap (genMap (Z.ξ₀ ≫ Y.j) p)) ≫ (e i).left :=
    fun i => by rw [hj, hf]
  have hext : ∀ i, Z.M.Extends p (j (f i)) (e i) := fun i => ⟨(h0.1 i).1, hb i⟩
  have h1 : IsEigFrame Y.t.act (Z.ξ₀ ≫ Y.j) (((genMap (Z.ξ₀ ≫ Y.j) p).comp κ).comp (tauIn c σ))
      (fun i => Z.M.pt (j (f i))) := hs _ _ _ hg _ hb
  rw [hκ] at h1
  obtain ⟨hbi, hbs⟩ := (((_root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame Y.X Z.Ω Y.t.G (Z.ξ₀ ≫ Y.j) Z.V Z.M).2 (𝓞 E) Y.t.act Z.ρ
    (Z.inc.comp (tauIn c σ)) Z.act).2 r fun i => j (f i)).1 h1
  refine ⟨fun i => j (f i), hext, hbi, le_antisymm ?_ (Submodule.span_le.2 ?_)⟩
  · intro e' he'
    obtain ⟨hl, hE⟩ : e' ∈ Z.M.lat p ∧ e' ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)) := he'
    obtain ⟨v, hv⟩ := (Z.M.mem_lat_iff p e').1 hl
    obtain ⟨w, rfl⟩ := MA.onto v hv.1
    have hw : e' = j w := LieVB.pt_left_inj Z.M (hv.2.trans (hj w).symm)
    letI : Algebra c.F (Y.X.presheaf.stalk p.1) := κ.toAlgebra
    letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
    obtain ⟨ft, ⟨hft1, hft2⟩, -⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c (Y.X.presheaf.stalk p.1) F ρA w
    have hint : ∀ a y, Z.ρ a (j y) = j (ρA a y) := fun a y => LieVB.pt_left_inj Z.M (by
      have h2 := congrArg (fun q => q.left) (Z.act a (j y))
      have h3 := congrArg (fun q => q.left) (hρA a y)
      simp only [Over.comp_left] at h2 h3
      rw [h2, hj, hj, h3, Category.assoc])
    obtain ⟨_, -, huq⟩ := GlobalTheory.Frames.existsUnique_eigen_sum E H l c Z.Ω Z.V Z.ρ e'
    have e1 := huq (fun τ => j (ft τ)) ⟨fun τ a => by
      show Z.ρ a (j (ft τ)) = _
      rw [hint, hft1, j.map_smulₛₗ]
      show (genMap (Z.ξ₀ ≫ Y.j) p) (κ _) • _ = Z.inc _ • _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hκ]; rfl, by rw [← map_sum, hft2, hw]⟩
    have e2 := huq (fun τ => if τ = σ then e' else 0) ⟨fun τ a => by
      by_cases h : τ = σ
      · subst h
        simp only [if_true]
        exact (mem_eigSp_iff_forall _ _ _).1 hE a
      · simp [h], by simp⟩
    have e3 : j (ft σ) = e' := by simpa using congrFun (e1.trans e2.symm) σ
    have hmem : ft σ ∈ eigSp ρA (((RingHom.id _).comp κ).comp (tauIn c σ)) :=
      (mem_eigSp_iff_forall _ _ _).2 fun a => hft1 σ a
    rw [← hfs] at hmem
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e3, ← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [j.map_smulₛₗ]
    exact Submodule.smul_mem _ (⟨genMap (Z.ξ₀ ≫ Y.j) p (a i), _, rfl⟩ : regAt (Z.ξ₀ ≫ Y.j) p)
      (Submodule.subset_span ⟨i, rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact ⟨(Z.M.mem_lat_iff p _).2 ⟨_, hext i⟩, hbs ▸ Submodule.subset_span ⟨i, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorsSpreadFromStalk
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_ringHom {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    (z : Sp B ⟶ X) (hr : Set.range z ⊆ Set.range x) : ∃ a : A →+* B, spMap a ≫ x = z := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem ringHom_ext {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    {a b : A →+* B} (h : spMap a ≫ x = spMap b ≫ x) : a = b := by
  have h2 := Spec.map_injective ((cancel_mono x).1 h)
  exact congrArg (fun g => g.hom) h2

theorem exists_frac {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] (P : X)
    (hP : P ∈ x.opensRange) (θ : R →+* X.presheaf.stalk P) (hθ : spMap θ ≫ x = X.fromSpecStalk P)
    (a : X.presheaf.stalk P) : ∃ r s : R, IsUnit (θ s) ∧ a * θ s = θ r := by
  have hU : IsAffineOpen x.opensRange := isAffineOpen_opensRange x
  let R₂ : Type := Γ(X, x.opensRange)
  let x₂ : Sp R₂ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₂ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range x₂ = Set.range x := by
    change Set.range hU.fromSpec = _
    rw [hU.range_fromSpec]
    rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom x x₂ hrange.le
  obtain ⟨φ', hφ'⟩ := exists_ringHom x₂ x hrange.ge
  have hcomp : φ.comp φ' = RingHom.id R₂ := ringHom_ext x₂ (by
    rw [spMap_comp, Category.assoc, hφ', hφ]
    simp [spMap])
  let g : R₂ →+* X.presheaf.stalk P := (X.presheaf.germ x.opensRange P hP).hom
  have hg : spMap g ≫ x₂ = X.fromSpecStalk P := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]
    rfl
  have hgφ : g.comp φ = θ := ringHom_ext x (by
    rw [spMap_comp, Category.assoc, hφ, hg, hθ])
  have hgs : ∀ t, θ (φ' t) = g t := fun t => by
    rw [← hgφ]
    exact congrArg g (RingHom.congr_fun hcomp t)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)
  haveI := hU.isLocalization_stalk ⟨P, hP⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a
  refine ⟨φ' r, φ' s, ?_, ?_⟩
  · rw [hgs]
    exact IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s
  · rw [hgs, hgs]
    exact hrs

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem exists_chart_spread : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  intro X G _ _ _ P ι _ e f he
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩ := LieVB.exists_chart G P
  have hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  obtain ⟨θ₁, hθ₁⟩ := LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'
  obtain ⟨Fs, _, _, ⟨Ms⟩⟩ := lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)
  obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b
  choose s hs using fun i => Ms.onto (e i) (he i)
  let c : ι → Fin n → X.presheaf.stalk P := fun i k => B.repr (s i) k
  choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁
  let h : R₁ := den f * ∏ i, ∏ k, den (c i k)
  have hunit : IsUnit (θ₁ h) := by
    simp only [h, map_mul, map_prod]
    exact (hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)
  let R : Type := Localization.Away h
  let θ : R →+* X.presheaf.stalk P := IsLocalization.Away.lift h hunit
  have hθc : θ.comp (algebraMap R₁ R) = θ₁ := IsLocalization.Away.lift_comp h hunit
  let x : Sp R ⟶ X := spMap (algebraMap R₁ R) ≫ x₁
  have hopen : IsOpenImmersion (spMap (algebraMap R₁ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))
  have hx : IsOpenImmersion x := inferInstance
  have hxθ : spMap θ ≫ x = X.fromSpecStalk P := by
    change spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _
    rw [← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]
  have hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a := fun a hd => by
    have hu : IsUnit (algebraMap R₁ R (den a)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)
    obtain ⟨u, hu⟩ := hu
    have hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a) := RingHom.congr_fun hθc _
    refine ⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩
    have h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1 := by
      rw [← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a) := RingHom.congr_fun hθc _
    rw [map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]
  have hdvd : ∀ i k, den (c i k) ∣ h := fun i k =>
    Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _
  choose c' hc' using fun i k => hlift (c i k) (hdvd i k)
  obtain ⟨f', hf'⟩ := hlift f (Dvd.intro _ rfl)
  obtain ⟨F', _, _, ⟨MR⟩⟩ := lieModel_exists X G R x
  obtain ⟨β₁, B₁, hB₁, hβ₁⟩ := LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms
  have hjB : ∀ k, j (B₁ k) = B k := fun k => LieVB.pt_left_inj Ms (by
    rw [hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])
  refine ⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf',
    fun i => MR.tan _, fun i => ?_⟩
  · refine ⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hxθ]
    exact Scheme.fromSpecStalk_closedPoint
  · have hsum : j (∑ k, c' i k • B₁ k) = s i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))
      rw [j.map_smulₛₗ, hc', hjB]
    rw [← hj, hsum, hs]

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusEmbeddingLieInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusSat

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.GlobalTheory.CompanionTheory.Ar

theorem pt_zero {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem exists_div {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] {π : R}
    (hπ : Irreducible π) (δ : X →+ R) (h : ∀ χ, IsLocalRing.residue R (δ χ) = 0) :
    ∃ δ' : X →+ R, δ = π • δ' := by
  have hd : ∀ χ, ∃ r, δ χ = π * r := fun χ => by
    have hm : δ χ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff _).mp (h χ)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at hm
    exact Ideal.mem_span_singleton'.mp hm |>.imp fun r hr => by rw [← hr, mul_comm]
  choose f hf using hd
  refine ⟨AddMonoidHom.mk' f fun a b => ?_, ?_⟩
  · apply mul_left_cancel₀ hπ.ne_zero
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · ext χ
    simp [hf]

theorem lie_torus_saturated : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  intro R K _ _ _ _ _ _ S b G _ _ _ _ X _ _ _ u _ hgen MT hMT E _ _ M A hA
  obtain ⟨hEf, hEp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective S G R b E M
  obtain ⟨Mk, hMk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TorusLie.exists_lieModel_splitTorus S X (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨Ek, i1, i2, ⟨MG⟩⟩ := lieModel_exists S G (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R _ (IsLocalRing.residue R) b E Ek M MG
  obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S (splitTorus S X) R _
    (IsLocalRing.residue R) b (X →+ R) (X →+ IsLocalRing.ResidueField R) MT Mk
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hcπ : IsLocalRing.residue R π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have key : ∀ δ, A δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (X →+ R)) := by
    intro δ hδ
    obtain ⟨z, hz⟩ := (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mp hδ
    have h0 : j (A δ) = 0 := by
      rw [hz, map_smulₛₗ, hcπ, zero_smul]
    have a1 := hj (A δ)
    have a2 := hjT δ
    rw [Category.comp_id] at a1 a2
    rw [h0, pt_zero, hA, Over.comp_left] at a1
    have h1 : Mk.pt (jT δ) ≫ u = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, a2, Category.assoc, a1]
    have h2 : jT δ = 0 := _root_.GlobalTheory.CompanionTheory.Ar.TsClosed.diff_injective_mod_pi R K S b G X u hgen Mk hMk _ h1
    have h3 : ∀ χ, IsLocalRing.residue R (δ χ) = 0 := by
      intro χ
      have e := GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_comp (dualMap (IsLocalRing.residue R)) (MT.pt δ) (Mk.pt (jT δ)) a2 χ
      rw [hMk, hMT, h2] at e
      have e2 := congrArg TrivSqZeroExt.snd e
      simpa [dualMap] using e2.symm
    obtain ⟨δ', rfl⟩ := exists_div hπ δ h3
    exact (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mpr ⟨δ', rfl⟩
  have e := addMonoidHomLequivInt (A := X) (B := R) R
  haveI : Module.Free R (X →+ R) := Module.Free.of_equiv e.symm
  haveI : Module.Finite R (X →+ R) := Module.Finite.equiv e.symm
  haveI : Module.IsTorsionFree R E := inferInstance
  exact GlobalTheory.CompanionTheory.CommAlg.SatOfInj.sat_of_inj_mod R (X →+ R) E A key

end GlobalTheory.CompanionTheory.Ar.TorusSat
end
end

