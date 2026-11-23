module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotient
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothBasicOpen
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem hom_to_spQ_ext {X : Scheme.{0}} (a b : X ⟶ Sp ℚ) : a = b := by
  haveI : IsAffine (Sp ℚ) := inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ)))
  apply ext_of_isAffine
  apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv).mp
  apply CommRingCat.hom_ext
  exact RingHom.ext_rat _ _

theorem smoothOfRelativeDimension_spMap (B : Type) [CommRing B] [Algebra ℚ B] (e : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ B] :
    SmoothOfRelativeDimension e (spMap (algebraMap ℚ B)) := by
  show SmoothOfRelativeDimension e (Spec.map (CommRingCat.ofHom (algebraMap ℚ B)))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension e)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap e).mpr inferInstance)

def valEquiv {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z]
    (W : Z.Opens) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) :
    Γ(Z, W) ≃+* A :=
  RingEquiv.ofBijective
    ((valMap ζ W h).hom.codRestrict A.toSubring (fun x => by
      have : (valMap ζ W h).hom x ∈ (A : Set Ω) := hA ▸ Set.mem_range_self x
      exact this))
    ⟨fun x y hxy => valMap_injective ζ h (congrArg Subtype.val hxy), fun y => by
      have : (y : Ω) ∈ Set.range (valMap ζ W h).hom := hA ▸ y.2
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩⟩

theorem smoothOfRelativeDimension_basicOpen_of_away : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z) [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (W : Z.Opens) (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W)) (g₀ : A) (hg : (g₀ : Ω) = valR ζ W σ) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)], SmoothOfRelativeDimension e ((Z.basicOpen σ).ι ≫ g) := by
  intro Ω _ _ Z ζ _ _ g e W hW h A hA σ g₀ hg _
  haveI := hW.isLocalization_basicOpen σ
  have hE : valEquiv ζ W h A hA σ = g₀ := by
    apply Subtype.ext
    rw [hg]
    show (valMap ζ W h).hom σ = valR ζ W σ
    simp only [valR, valMap, dif_pos h]
    rfl
  let ψ : Γ(Z, Z.basicOpen σ) ≃+* Localization.Away g₀ :=
    IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers σ) (T := Submonoid.powers g₀) _ _ (valEquiv ζ W h A hA)
      (by rw [Submonoid.map_powers]; exact congrArg Submonoid.powers hE)
  have hiso : IsIso (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ))) :=
    ⟨⟨CommRingCat.ofHom (ψ : Γ(Z, Z.basicOpen σ) →+* Localization.Away g₀),
      by ext x; simp, by ext x; simp⟩⟩
  let f2 : Spec Γ(Z, Z.basicOpen σ) ⟶ Sp (Localization.Away g₀) :=
    Spec.map (CommRingCat.ofHom (ψ.symm : Localization.Away g₀ →+* Γ(Z, Z.basicOpen σ)))
  haveI : IsIso f2 := by dsimp only [f2]; infer_instance
  have key : (Z.basicOpen σ).ι ≫ g =
      ((hW.basicOpen σ).isoSpec.hom ≫ f2) ≫ spMap (algebraMap ℚ (Localization.Away g₀)) :=
    hom_to_spQ_ext _ _
  rw [key]
  haveI := smoothOfRelativeDimension_spMap (Localization.Away g₀) e
  have := smoothOfRelativeDimension_comp 0 e ((hW.basicOpen σ).isoSpec.hom ≫ f2)
    (spMap (algebraMap ℚ (Localization.Away g₀)))
  rwa [zero_add] at this

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TBijective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular
open scoped Matrix ComplexOrder

def basePoint (n a : ℕ) : Fin n → ℂ := fun k => if k.val < a then -1 else 0

theorem basePoint_mem {n a : ℕ} (h : a ≤ n) : basePoint n a ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have : (Fin.castLE h i).val < a := i.isLt
    simp [basePoint, this]
  · have : ¬ k.val < a := by omega
    simp [basePoint, this]

theorem shift_mem {n a : ℕ} (h : a ≤ n) (i : Fin a) :
    basePoint n a + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · have hj : (Fin.castLE h j).val < a := j.isLt
    by_cases hji : Fin.castLE h j = Fin.castLE h i
    · simp [basePoint, hj, hji, Pi.single_apply]
    · simp [basePoint, hj, Pi.single_apply, hji]
  · have hk' : ¬ k.val < a := by omega
    have hne : k ≠ Fin.castLE h i := by
      intro e
      apply hk'
      rw [e]
      exact i.isLt
    simp [basePoint, hk', Pi.single_apply, hne]

theorem expCover_shift {n a : ℕ} (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have : (Fin.castLE h i).val < a := i.isLt
    simp [expCover, this, Complex.exp_add, Complex.exp_two_pi_mul_I]
  · simp [expCover, Pi.single_apply, hk]

theorem monodromy_preserves_form {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  have hw := basePoint_mem L.a_le
  have h1 := L.im _ (shift_mem L.a_le i) x y
  rw [expCover_shift, L.mono i _ hw x, L.mono i _ hw y] at h1
  have h2 := L.im _ hw (L.T i x) (L.T i y)
  exact_mod_cast h2.symm.trans h1

theorem T_bijective : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a),
    Function.Bijective (L.T i) := by
  intro n a g Λ _ L i
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hS : ∀ x, S (L.T i x) = x := by
    intro x
    apply e.injective
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    ext y
    simpa [e, LinearMap.dualMap_apply] using monodromy_preserves_form L i x y
  have hSsurj : Function.Surjective S := fun x => ⟨_, hS x⟩
  have hSinj : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSsurj
  refine ⟨Function.LeftInverse.injective hS, fun y => ⟨S y, hSinj (hS (S y))⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLiftsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ggeo.DOpen

theorem isDerivAt0_lift_of_isOpenImmersion :
    ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A))
      (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T),
      IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  intro A T φ _ g W y v hv
  have hcl : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ φ.opensRange := by
    have h0 : ⊤ ≤ (W 0 ≫ φ) ⁻¹ᵁ φ.opensRange := fun p _ =>
      (show (W 0 ≫ φ) p ∈ Set.range φ from ⟨W 0 p, by simp⟩)
    have hpt : v (IsLocalRing.closedPoint _) = (W 0 ≫ φ) ReciprocityTheory.ChartRestriction.G.PullbackSections.cpt := by
      have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = W 0 ≫ φ := hv.1
      rw [← hcomp, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
    show v (IsLocalRing.closedPoint _) ∈ φ.opensRange
    rw [hpt]
    exact h0 trivial
  have htop : ⊤ ≤ v ⁻¹ᵁ φ.opensRange := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le _ hcl
  have hrange : Set.range v ⊆ Set.range φ := by
    rintro _ ⟨p, rfl⟩
    exact htop (show p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  obtain ⟨v', rfl⟩ : ∃ v', v' ≫ φ = v := ⟨IsOpenImmersion.lift φ v hrange, IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨v', rfl, ?_, fun U' h f' => ?_⟩
  · rw [← cancel_mono φ, Category.assoc]
    exact hv.1
  · have key : ∀ (U : T.Opens) (U' : A.Opens) (e : φ ⁻¹ᵁ U = U') (h : ⊤ ≤ v' ⁻¹ᵁ U') (f : Γ(T, U)),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
            ((v'.appLE U' ⊤ h).hom (φ.appLE U U' e.ge f))) =
          fderiv ℂ (fun z => valAt' (W z) U' (φ.appLE U U' e.ge f)) 0 y := by
      intro U U' e h f
      subst e
      have hU : ⊤ ≤ (v' ≫ φ) ⁻¹ᵁ U := h
      have happ : φ.appLE U (φ ⁻¹ᵁ U) (le_refl (φ ⁻¹ᵁ U)) f = φ.app U f := by
        rw [Scheme.Hom.app_eq_appLE]
      have hfun : (fun z => valAt' (W z) (φ ⁻¹ᵁ U) (φ.app U f)) =
          fun z => valAt' ((fun x => W x ≫ φ) z) U f :=
        funext fun z => ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp (W z) φ U f
      erw [happ]
      rw [hfun, ← hv.2 U hU f, Scheme.Hom.comp_appLE]
      rfl
    have hpre : φ ⁻¹ᵁ (φ ''ᵁ U') = U' := φ.preimage_image_eq U'
    have := key (φ ''ᵁ U') U' hpre h ((φ.appIso U').inv f')
    have hf : φ.appLE (φ ''ᵁ U') U' hpre.ge ((φ.appIso U').inv f') = f' := by
      have hh : φ.appLE (φ ''ᵁ U') U' hpre.ge = (φ.appIso U').hom := (Scheme.Hom.appIso_hom' φ U').symm
      rw [hh]
      exact ConcreteCategory.congr_hom (φ.appIso U').inv_hom_id f'
    rwa [hf] at this

end GlobalTheory.CompanionTheory.Ggeo.DOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveLieMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsClosed

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem exists_transport (u : splitTorus S X ⟶ G) {A : Type} [CommRing A] {a a' : Sp A ⟶ S} (e : a = a')
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ t' : Over.mk a' ⟶ splitTorus S X, (∀ χ, charVal t' χ = charVal t χ) ∧ (t' ≫ u = 1 → t ≫ u = 1) := by
  subst e
  exact ⟨t, fun _ => rfl, id⟩

theorem killsOver_comp (u : splitTorus S X ⟶ G) (Y : AddSubgroup X) {B B' : Type} [CommRing B] [CommRing B']
    (b : Sp B ⟶ S) (c : B →+* B') (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  have e : spMap g ≫ spMap c ≫ b = spMap (g.comp c) ≫ b := by
    rw [← Category.assoc, spMap_comp_eq]
  obtain ⟨t', h1, h2⟩ := exists_transport u e t
  exact h2 (h A (g.comp c) t' fun y hy => by rw [h1]; exact ht y hy)

theorem killsOver_pow (u : splitTorus S X ⟶ G) [IsMonHom u] (Y : AddSubgroup X) {R : Type} [CommRing R]
    [IsLocalRing R] (b : Sp R ⟶ S) (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) (n : ℕ) :
    KillsOver u Y (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1))) ≫ b) := by
  induction n with
  | zero =>
    let c : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _)
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha))
    have hc : c.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext x; rfl
    have key := killsOver_comp u Y _ c h
    rw [← Category.assoc, spMap_comp_eq, hc] at key
    exact key
  | succ n ih =>
    have hJ : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≠ ⊤ := by
      intro e
      have h1 : IsLocalRing.maximalIdeal R ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal R :=
        Ideal.pow_le_self (by omega)
      rw [e] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.1 h1)
    haveI : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      Ideal.Quotient.nontrivial_iff.2 hJ
    haveI : IsLocalRing (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) :=
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk _)
    have hI : I ^ 2 = ⊥ := by
      simp only [I]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact Ideal.pow_le_pow_right (by omega)
    refine _root_.GlobalTheory.CompanionTheory.Ar.killsOver_of_sq_zero S G X u Y _ _ I hI ?_
    let c : R ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)) →+*
        (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _))
        (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))
    have hc : c.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk I).comp (Ideal.Quotient.mk _) := by
      ext x; rfl
    have key := killsOver_comp u Y _ c ih
    rw [← Category.assoc, spMap_comp_eq, hc, ← spMap_comp_eq, Category.assoc] at key
    exact key

theorem diff_injective_mod_pi : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ M : LieModel (splitTorus S X) (spMap (IsLocalRing.residue R) ≫ b) (X →+ IsLocalRing.ResidueField R), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro R K _ _ _ _ _ _ S b G _ _ X _ _ u _ hK M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed S G X u (IsLocalRing.ResidueField R)
    (spMap (IsLocalRing.residue R) ≫ b) M hM δ hne hδ
  have hR := _root_.GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow S G X u ψ.ker R b (killsOver_pow u ψ.ker b hk)
  have hKk := killsOver_comp u ψ.ker b (algebraMap R K) hR
  haveI := Fact.mk hl
  obtain ⟨-, -, h1, -, hex, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TorusPoints.main S X (AddMonoidAlgebra K (ZMod l))
    (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ spMap (algebraMap R K) ≫ b)
  let w : Multiplicative X →* AddMonoidAlgebra K (ZMod l) :=
    (AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)
  obtain ⟨t, ht⟩ := hex w
  have hu : t ≫ u = 1 := hKk _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t fun y hy => by
    rw [ht]
    have hy0 : ψ y = 0 := hy
    simp [w, hy0, AddMonoidAlgebra.one_def]
  have ht1 := hK _ (algebraMap K (AddMonoidAlgebra K (ZMod l))) t hu
  obtain ⟨χ, hχ⟩ := hψ 1
  have key := ht χ
  rw [ht1, h1] at key
  simp only [w, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, hχ] at key
  rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_left_inj one_ne_zero] at key
  exact zero_ne_one key

end GlobalTheory.CompanionTheory.Ar.TsClosed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StratLie

open GlobalTheory.CompanionTheory.Ar.TorusModel

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem killed_of_eq {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B : Type} [CommRing B] {b : Sp B ⟶ S}
    (h : KillsOver u Y b) {A : Type} [CommRing A] (g : B →+* A) {a : Sp A ⟶ S} (ha : a = spMap g ≫ b)
    (t : Over.mk a ⟶ splitTorus S X) (ht : ∀ y ∈ Y, charVal t y = 1) : t ≫ u = 1 := by
  subst ha
  exact h A g t ht

theorem killsOver_comp {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {B C : Type} [CommRing B] [CommRing C]
    (c : B →+* C) {b : Sp B ⟶ S} (h : KillsOver u Y b) : KillsOver u Y (spMap c ≫ b) := by
  intro A _ g t ht
  refine killed_of_eq h (g.comp c) ?_ t ht
  rw [← Category.assoc, spMap_comp_spMap]

theorem killsOver_descent [IsSeparated G.hom] {u : splitTorus S X ⟶ G} {Y : AddSubgroup X} {κ k : Type}
    [Field κ] [Field k] (c : κ →+* k) {b : Sp κ ⟶ S} (h : KillsOver u Y (spMap c ≫ b)) : KillsOver u Y b := by
  intro A _ g t ht
  letI := g.toAlgebra
  letI := c.toAlgebra
  let i : A →+* (A ⊗[κ] k) := Algebra.TensorProduct.includeLeftRingHom
  let j : k →+* (A ⊗[κ] k) := (Algebra.TensorProduct.includeRight : k →ₐ[κ] (A ⊗[κ] k)).toRingHom
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeLeft_injective (R := κ) (S := κ) (A := A) (B := k) c.injective
  have hij : i.comp g = j.comp c := by
    ext a
    change (algebraMap κ A a) ⊗ₜ[κ] (1 : k) = (1 : A) ⊗ₜ[κ] (algebraMap κ k a)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hw : spMap i ≫ spMap g ≫ b = spMap j ≫ spMap c ≫ b := by
    simp only [← Category.assoc, spMap_comp_spMap, hij]
  let φ : Over.mk (spMap j ≫ spMap c ≫ b) ⟶ Over.mk (spMap g ≫ b) := Over.homMk (spMap i) hw
  have h1 := h _ j (φ ≫ t) (fun y hy => by rw [charVal_comp i t (φ ≫ t) rfl, ht y hy, map_one])
  have h2 : φ ≫ (t ≫ u) = φ ≫ 1 :=
    (Category.assoc _ _ _).symm.trans (h1.trans (MonObj.comp_one φ).symm)
  have := GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom i) hi
  refine Over.OverMorphism.ext (GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap i) ?_)
  · rw [Over.w, Over.w]
  · exact congr($(h2).left)

theorem false_of_killsOver {u : splitTorus S X ⟶ G} {K : Type} [Field K] (b : Sp K ⟶ S) {l : ℕ} (hl : l.Prime)
    (ψ : X →+ ZMod l) (hψ : Function.Surjective ψ) (hk : KillsOver u ψ.ker b)
    (hinj : ∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ b) ⟶ splitTorus S X),
      t ≫ u = 1 → t = 1) : False := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨t, ht⟩ := exists_charVal (X := X) (spMap (algebraMap K (AddMonoidAlgebra K (ZMod l))) ≫ b)
    (MonoidHom.toHomUnits ((AddMonoidAlgebra.of K (ZMod l)).comp (AddMonoidHom.toMultiplicative ψ)))
  have ht' : ∀ χ, charVal t χ = AddMonoidAlgebra.single (ψ χ) 1 := ht
  have h1 := hk _ _ t fun y hy => by
    rw [ht', (AddMonoidHom.mem_ker).1 hy]; rfl
  have h2 := hinj _ _ t h1
  obtain ⟨χ, hχ⟩ := hψ 1
  have h3 := ht' χ
  rw [h2, charVal_one, AddMonoidAlgebra.one_def, hχ] at h3
  exact one_ne_zero (AddMonoidAlgebra.single_left_injective one_ne_zero h3).symm

theorem killsOver_of_residue [IsSeparated G.hom] {u : splitTorus S X ⟶ G} [IsMonHom u] {Y : AddSubgroup X}
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (b : Sp R ⟶ S)
    (h : KillsOver u Y (spMap (IsLocalRing.residue R) ≫ b)) : KillsOver u Y b := by
  refine _root_.GlobalTheory.CompanionTheory.Ar.KillsAdic.killsOver_of_forall_pow S G X u Y R b fun n => ?_
  induction n with
  | zero =>
    let e : IsLocalRing.ResidueField R →+* R ⧸ (IsLocalRing.maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.lift _ (Ideal.Quotient.mk _) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha)
    have he : e.comp (IsLocalRing.residue R) = Ideal.Quotient.mk _ := by
      ext a; rfl
    have := killsOver_comp e h
    rwa [← Category.assoc, spMap_comp_spMap, he] at this
  | succ n ih =>
    set m := IsLocalRing.maximalIdeal R with hm
    have hne : m ^ (n + 1 + 1) ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.pow_eq_top_iff.1 htop |>.elim id (by simp))
    let q := Ideal.Quotient.mk (m ^ (n + 1 + 1))
    haveI : Nontrivial (R ⧸ m ^ (n + 1 + 1)) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
      IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
    let I : Ideal (R ⧸ m ^ (n + 1 + 1)) := (m ^ (n + 1)).map q
    have hI : I ^ 2 = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    refine _root_.GlobalTheory.CompanionTheory.Ar.killsOver_of_sq_zero S G X u Y _ (spMap q ≫ b) I hI ?_
    let e : R ⧸ m ^ (n + 1) →+* (R ⧸ m ^ (n + 1 + 1)) ⧸ I :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp q) fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    have he : e.comp (Ideal.Quotient.mk (m ^ (n + 1))) = (Ideal.Quotient.mk I).comp q := by
      ext a; rfl
    have := killsOver_comp e ih
    rw [← Category.assoc, spMap_comp_spMap, he, ← spMap_comp_spMap, Category.assoc] at this
    exact this

theorem lie_injective : ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (G : Over Z) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (u : splitTorus Z X ⟶ G) [IsMonHom u] (U : Z.Opens), (U : Set Z).Nonempty → (∀ (k : Type) [Field k] (x : Sp k ⟶ Z), ⊤ ≤ x ⁻¹ᵁ U → ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z X), t ≫ u = 1 → t = 1) → ∀ (k : Type) [Field k] (x : Sp k ⟶ Z) (M : LieModel (splitTorus Z X) x (X →+ k)), IsCocharLie M → ∀ δ, M.pt δ ≫ u = 1 → δ = 0 := by
  intro Z _ _ G _ _ X _ _ u _ U hU hinj k _ x M hM δ hδ
  by_contra hne
  obtain ⟨l, hl, ψ, hψ, hk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TsField.exists_mu_killed Z G X u k x M hM δ hne hδ
  obtain ⟨z, f, hx⟩ : ∃ (z : Z) (f : Z.residueField z ⟶ CommRingCat.of k),
      x = Spec.map f ≫ Z.fromSpecResidueField z :=
    ⟨_, _, ((Scheme.SpecToEquivOfField k Z).symm_apply_apply x).symm⟩
  by_cases hz : z ∈ U
  · have hU' : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
      subst hx
      change (Z.fromSpecResidueField z) _ ∈ U
      rwa [Scheme.fromSpecResidueField_apply]
    exact false_of_killsOver x hl ψ hψ hk (hinj k x hU')
  have hgen : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hzg : z ≠ genericPoint Z := fun h => hz (h ▸ hgen)
  have hkκ : KillsOver u ψ.ker (Z.fromSpecResidueField z) :=
    killsOver_descent f.hom (hx ▸ hk)
  obtain ⟨V, hV, hA, hdom⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.proof Z z hzg
  let jv : Z.presheaf.stalk z →+* V := (algebraMap (Z.presheaf.stalk z) Z.functionField).codRestrict V hA
  haveI : IsLocalHom jv := ⟨fun a ha => by
    by_contra hna
    exact ((hdom a).2 ((IsLocalRing.mem_maximalIdeal a).2 hna)) ha⟩
  let b : Sp V ⟶ Z := spMap jv ≫ Z.fromSpecStalk z
  let rm : IsLocalRing.ResidueField (Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V :=
    IsLocalRing.ResidueField.map jv
  have e1 : spMap rm ≫ Z.fromSpecResidueField z = spMap (IsLocalRing.residue V) ≫ b := by
    have e0 : spMap rm ≫ Spec.map (Z.residue z) = spMap (IsLocalRing.residue V) ≫ spMap jv := by
      rw [spMap_comp_spMap, ← IsLocalRing.ResidueField.map_comp_residue jv, ← spMap_comp_spMap]
      rfl
    simp only [b, Scheme.fromSpecResidueField]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Z.fromSpecStalk z) e0).trans (Category.assoc _ _ _))
  have kres : KillsOver u ψ.ker (spMap (IsLocalRing.residue V) ≫ b) := e1 ▸ killsOver_comp rm hkκ
  have kV := killsOver_of_residue b kres
  have kK := killsOver_comp V.subtype kV
  have hU'' : ⊤ ≤ (spMap V.subtype ≫ b) ⁻¹ᵁ U := by
    have e2 : spMap V.subtype ≫ b = Z.fromSpecStalk (genericPoint Z) := by
      simp only [b]
      rw [← Category.assoc, spMap_comp_spMap]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
    intro p _
    change (spMap V.subtype ≫ b) p ∈ U
    rw [e2]
    have hp : (Z.fromSpecStalk (genericPoint Z)) p ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hp
    exact Specializes.mem_open hp U.isOpen hgen
  exact false_of_killsOver _ hl ψ hψ kK (hinj _ _ hU'')

end GlobalTheory.CompanionTheory.Ar.StratLie
end
end

