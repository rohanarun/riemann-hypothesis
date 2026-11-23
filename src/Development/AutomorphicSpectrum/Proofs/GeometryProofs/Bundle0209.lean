module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0203
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpDerivativeLie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv

def rho {R : Type} [CommRing R] (φ : R →+* ℂ) :
    epsAt (spMap φ) ⟶ epsAt (𝟙 (Sp R)) :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    have hsq : spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) =
        spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun r => ?_
      ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap φ
    rw [Category.comp_id, hsq])

theorem dualMap_comp_epsMul {R : Type} [CommRing R] (φ : R →+* ℂ) (c : R) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (GlobalTheory.CompanionTheory.Ar.epsMul c) =
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ c)).comp (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  refine RingHom.ext fun r => ?_
  ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, mul_comm]

theorem lieModel_pt_zero {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g : ℕ}
    (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (u : Fin g → R) :
    IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c))
      (spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left) := by
  have hF0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left :=
    congrArg (·.left) (ExpLift.ex_zero e hb)
  let T : (Fin g → R) → (epsPt (spMap (ψ b)) ⟶ G) := fun u => rho (ψ b) ≫ M.pt u
  have hTl : ∀ u, (T u).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt u).left := fun _ => rfl
  have hadd : ∀ u u', T (u + u') = T u * T u' := fun u u' => by
    simp only [T, M.add, MonObj.comp_mul]
  have hone : (T 0).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (fun z => (e.ex b z).left) 0 := by
    let i₀ : epsPt (spMap (ψ b)) ⟶ Over.mk (spMap (ψ b)) :=
      Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
    have h1 : T 0 = i₀ ≫ (1 : Over.mk (spMap (ψ b)) ⟶ G) := by
      simp only [T, lieModel_pt_zero, MonObj.comp_one]
    rw [h1, hF0]
    rfl
  have h0 : IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((0 : Fin g → R) c)) (T 0).left := by
    rw [hone]
    have : (fun c => ψ b ((0 : Fin g → R) c)) = (0 : Fin g → ℂ) := by
      funext c; simp
    rw [this]
    exact GlobalTheory.LocalLift.isDerivAt0_const _ 0 fun _ _ _ => map_zero _
  have hsm : ∀ (c : R) (w : Fin g → R),
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (w c)) (T w).left →
      IsDerivAt0 (fun z => (e.ex b z).left) (fun d => ψ b ((c • w) d)) (T (c • w)).left := by
    intro c w h
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul h (ψ b c)
    have h2 : (T (c • w)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (ψ b c)) ≫ (T w).left := by
      rw [hTl, hTl, M.smul, ← Category.assoc, ← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [dualMap_comp_epsMul]
    have h3 : (fun d => ψ b ((c • w) d)) = ψ b c • (fun d => ψ b (w d)) := by
      funext d; simp
    rw [h2, h3]
    exact h1
  have hsingle : ∀ a : Fin g,
      IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b ((Pi.single a 1 : Fin g → R) c))
        (T (Pi.single a 1)).left := by
    intro a
    have h3 : (fun c => ψ b ((Pi.single a 1 : Fin g → R) c)) = (Pi.single a 1 : Fin g → ℂ) := by
      funext c
      by_cases h : c = a
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h3]
    exact e.diff b hb a
  have hs : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left)
      (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c))
      (T (∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R))).left := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, hadd]
      have h1 := GlobalTheory.UnifCompare.isDerivAt0_mul (y := spMap (ψ b)) (G := G) hF0
        (hsm (u a) _ (hsingle a)) ih
      have h3 : (fun c => ψ b ((u a • (Pi.single a 1 : Fin g → R) +
          ∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) =
          (fun d => ψ b ((u a • (Pi.single a 1 : Fin g → R)) d)) +
            (fun c => ψ b ((∑ a ∈ s, u a • (Pi.single a 1 : Fin g → R)) c)) := by
        funext c; simp only [Pi.add_apply, map_add (f := _)]
      rw [h3]
      exact h1
  have hu : ∑ a, u a • (Pi.single a 1 : Fin g → R) = u := by
    funext c
    simp [Finset.sum_apply, Pi.single_apply]
  have := hs Finset.univ
  rw [hu] at this
  exact this

theorem isDerivAt0_frame_section : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ) (b : Fin n → ℂ), b ∈ B → ∀ u : Fin g → R, IsDerivAt0 (fun z => (e.ex b z).left) (fun c => ψ b (u c)) (spMap (dualMap (ψ b)) ≫ (M.pt u).left) :=
  fun _ _ _ _ _ _ _ _ _ _ e _ hb u => isDerivAt0_pt e hb u

end GlobalTheory.CompanionTheory.Ar.Flat.FrameDeriv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0ZeroOfFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {X : Scheme.{0}}

noncomputable def pullPolL (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj

theorem isDerivAt0_zero_of_fixed {g : ℕ} {Y : Scheme.{0}} {F : (Fin g → ℂ) → (Sp ℂ ⟶ Y)}
    {v : Sp (DualNumber ℂ) ⟶ Y} (h0 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = F 0)
    (hv : spMap (epsMul (0 : ℂ)) ≫ v = v) : IsDerivAt0 F 0 v := by
  refine ⟨h0, fun U h f => ?_⟩
  rw [map_zero]
  have key : ∀ (v' : Sp (DualNumber ℂ) ⟶ Y) (_ : v' = spMap (epsMul (0 : ℂ)) ≫ v) (h' : ⊤ ≤ v' ⁻¹ᵁ U),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v'.appLE U ⊤ h').hom f)) = 0 := by
    rintro _ rfl h'
    have hs := ReciprocityTheory.ChartRestriction.G.PullbackSections.specMap_comp_appLE (CommRingCat.ofHom (epsMul (0 : ℂ))) v U h' h
    have := ConcreteCategory.congr_hom hs f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    simp [epsMul]
  exact key v hv.symm h

theorem isHolTo_slice {n g : ℕ} {B : Set (Fin n → ℂ)} {Y : Scheme.{0}}
    {F : (Fin n → ℂ) × (Fin g → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo (B ×ˢ Set.univ) F) {b : Fin n → ℂ} (hb : b ∈ B) :
    IsHolTo Set.univ (fun z : Fin g → ℂ => F (b, z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  have hc : Continuous (fun z : Fin g → ℂ => (b, z)) := by fun_prop
  have hmem : ∀ z, z ∈ {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} →
      (b, z) ∈ {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩
  have hset : {z ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F (b, z) ⁻¹ᵁ U} =
      (fun z => (b, z)) ⁻¹' {bz ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ F bz ⁻¹ᵁ U} :=
    Set.ext fun z => ⟨hmem z, fun hz => ⟨trivial, hz.2⟩⟩
  refine ⟨hset ▸ h1.preimage hc, fun z hz => ?_⟩
  have hd := (h2 _ (hmem z hz)).differentiableAt (h1.mem_nhds (hmem z hz))
  have hi : DifferentiableAt ℂ (fun z : Fin g → ℂ => (b, z)) z := by fun_prop
  exact (DifferentiableAt.comp z hd hi).differentiableWithinAt

theorem isDerivAt0_pt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ}
    {M : LieModel G (𝟙 (Sp R)) (Fin g → R)} {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)}
    (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B) (Mz : LieModel G (spMap (ψ b)) (Fin g → ℂ))
    (hL : ∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) (x : Fin g → ℂ) :
    IsDerivAt0 (fun z => (e.ex b z).left) x (Mz.pt x).left := by
  have h1 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  have h0 : (fun z => (e.ex b z).left) 0 = (1 : Over.mk (spMap (ψ b)) ⟶ G).left := congrArg (·.left) h1
  have hbas : ∀ i, IsDerivAt0 (fun z => (e.ex b z).left) (Pi.single i 1) (Mz.pt (Pi.single i 1)).left := fun i => by
    have h := e.diff b hb i
    have h' := hL i
    change _ ≫ _ = _ ≫ _ at h'
    rw [Category.comp_id] at h'
    rwa [← h'] at h
  have hsc : ∀ (c : ℂ) i, IsDerivAt0 (fun z => (e.ex b z).left) (c • Pi.single i 1)
      (Mz.pt (c • Pi.single i 1)).left := fun c i => by
    rw [Mz.smul]
    exact isDerivAt0_smul (hbas i) c
  have hzero : IsDerivAt0 (fun z => (e.ex b z).left) 0 (Mz.pt 0).left := by
    refine isDerivAt0_zero_of_fixed ((Mz.tan 0).trans h0.symm) ?_
    have := Mz.smul 0 0
    rw [zero_smul] at this
    exact this.symm
  have hsum : ∀ s : Finset (Fin g), IsDerivAt0 (fun z => (e.ex b z).left) (∑ i ∈ s, x i • Pi.single i 1)
      (Mz.pt (∑ i ∈ s, x i • Pi.single i 1)).left := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Mz.add]
      exact UnifCompare.isDerivAt0_mul h0 (hsc _ _) ih
  have hx : ∑ i, x i • (Pi.single i 1 : Fin g → ℂ) = x := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := hsum Finset.univ
  rwa [hx] at this

theorem isDiff_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp ℂ))
    (hP : IsPrincipal t) {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ t.G.left} (hφ : IsGrpPullback A t.G (𝟙 _) φ)
    {g' : ℕ} (u : HolUnif A (t.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (hA : u.IsAH Hm χ)
    {v : epsR ℂ ⟶ A} (hv : IsTangent v) {w w' : Fin g' → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  obtain ⟨hpr, ham, hk⟩ := hP
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  let Q : Out.PolAV (Sp ℂ) :=
    { A := t.G, g := d, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ham, ktriv := hk
      isAb := ⟨inferInstance, inferInstance, hpr, ‹_›⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := GlobalTheory.CechPic.sym_of_isSymmetric t.PP t.sym }
  have hφ' : IsGrpPullback A Q.A (𝟙 _) φ := hφ
  obtain ⟨-, -, -, -, t1, -, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all
    (GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.Pol.pullPolL Q hφ') g' u Hm χ hA
  exact (t1 v hv).unique h h'

theorem isDiff_eq_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (Mz : LieModel t.G (spMap (ψ b)) (Fin g → ℂ)), (∀ i, ((Mz.pt (Pi.single i 1)).left ≫ (𝟙 _) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (ψ b)) ≫ (M.pt (Pi.single i 1)).left)) → ∀ (x : Fin g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v' : epsR ℂ ⟶ A) (w : Fin g' → ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → v'.left ≫ φ = (v ≫ P.τ.q ≫ P.e.hom).left → u.IsDiff w v' → w = ℓ x := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hφ hA hP hl Mz hL x v v' w hv hv' hw
  have Hc := P.m.cart.1
  have hex : ∀ y, ∃ s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G, s.left ≫ P.m.φ = (e.ex b y).left := fun y =>
    ⟨Over.homMk (Hc.lift (e.ex b y).left (𝟙 _) (by simpa using Over.w (e.ex b y))) (Hc.lift_snd _ _ _),
      Hc.lift_fst _ _ _⟩
  choose s hs using hex
  have hd1 := isDerivAt0_pt e hb Mz hL x
  have hFeq : (fun z => (s z).left ≫ P.m.φ) = fun z => (e.ex b z).left := funext hs
  have hd2 : IsDerivAt0 (fun z => (s z).left) x v.left :=
    GlobalTheory.FibreDeriv.isDerivAt0_of_isPullback Hc (fun z => Over.w (s z))
      (by rw [hFeq]; exact isHolTo_slice e.hol hb) (by simpa using Over.w v) (by rw [hFeq, hv]; exact hd1)
  have : IsIso φ := hφ.1.isIso_fst_of_isIso
  have hd3 := isDerivAt0_comp_hom hd2 ((P.τ.q ≫ P.e.hom).left ≫ inv φ)
  have e1 : v.left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ = v'.left := by
    rw [← Category.assoc, ← Over.comp_left, ← hv', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have e2 : (fun z => (s z).left ≫ (P.τ.q ≫ P.e.hom).left ≫ inv φ) = fun z => (u.ex (ℓ z)).left :=
    funext fun z => by
      rw [← Category.assoc, ← Over.comp_left, ← hl z (s z) (hs z), Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
  rw [e1, e2] at hd3
  have hz : (u.ex (ℓ 0)).left = η[A].left := by
    rw [map_zero]
    exact GlobalTheory.CompanionTheory.Ar.Flat.PerGram.ex_zero_left u
  have htan : IsTangent v' := hd3.1.trans hz
  have hdiff : u.IsDiff (ℓ x) v' := fun U h f => by
    refine (hd3.2 U h f).trans ?_
    have hU : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      have := tangent_open_preimage_zero hd3 U h
      simpa using this
    have hd : DifferentiableAt ℂ (fun z => valAt' (u.ex z).left U f) (ℓ.toContinuousLinearMap 0) := by
      rw [map_zero]
      exact ((u.hol U f).2 0 hU).differentiableAt ((u.hol U f).1.mem_nhds hU)
    have := fderiv_comp (𝕜 := ℂ) (0 : Fin g → ℂ) hd ℓ.toContinuousLinearMap.differentiableAt
    show fderiv ℂ ((fun z => valAt' (u.ex z).left U f) ∘ ℓ.toContinuousLinearMap) 0 x = _
    rw [this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv, map_zero]
    rfl
  exact isDiff_unique P.tB hP hφ u Hm χ hA htan hw hdiff

end GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodRiemannLatticeFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

def conjEnd (g : ℕ) : Module.End ℂ (Fin g → ℂ) →+* Module.End ℂ (Fin g → ℂ) where
  toFun f :=
    { toFun := fun x => star (f (star x))
      map_add' := fun x y => by simp only [star_add, map_add (f := _)]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply] }
  map_one' := by ext x; simp
  map_mul' f f' := by ext x; simp
  map_zero' := by ext x; simp
  map_add' f f' := by ext x; simp

theorem conjEnd_apply {g : ℕ} (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) :
    conjEnd g f x = star (f (star x)) := rfl

theorem mem_eigSp_iff {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ)
    (x : Fin g → ℂ) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem finrank_eigSp_conj {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ) :
    Module.finrank ℂ (eigSp ((conjEnd g).comp ρ) σ) = Module.finrank ℂ (eigSp ρ ((starRingEnd ℂ).comp σ)) := by
  have h1 : ∀ x, x ∈ eigSp ((conjEnd g).comp ρ) σ → star x ∈ eigSp ρ ((starRingEnd ℂ).comp σ) := by
    intro x hx
    rw [mem_eigSp_iff] at hx ⊢
    intro a
    have := congrArg star (hx a)
    simpa [conjEnd_apply, star_smul] using this
  have h2 : ∀ y, y ∈ eigSp ρ ((starRingEnd ℂ).comp σ) → star y ∈ eigSp ((conjEnd g).comp ρ) σ := by
    intro y hy
    rw [mem_eigSp_iff] at hy ⊢
    intro a
    simp [conjEnd_apply, hy a, star_smul]
  let j : eigSp ((conjEnd g).comp ρ) σ ≃+ eigSp ρ ((starRingEnd ℂ).comp σ) :=
    { toFun := fun x => ⟨star x.1, h1 _ x.2⟩
      invFun := fun y => ⟨star y.1, h2 _ y.2⟩
      left_inv := fun x => Subtype.ext (star_star _)
      right_inv := fun y => Subtype.ext (star_star _)
      map_add' := fun x y => Subtype.ext (star_add _ _) }
  have hr := rank_eq_of_equiv_equiv (R := ℂ) (R' := ℂ) (starRingEnd ℂ) j
    (Function.Involutive.bijective (f := starRingEnd ℂ) (fun z => by simp)) (fun r m => by
      apply Subtype.ext
      change star (r • m.1) = star r • star m.1
      exact star_smul r m.1)
  exact congrArg Cardinal.toNat hr

theorem star_herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    star z ⬝ᵥ Hm.map (starRingEnd ℂ) *ᵥ star (star w) = star (z ⬝ᵥ Hm *ᵥ star w) := by
  simp [dotProduct, mulVec, star_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjLat {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := by simp [R.alt x]
  unimod := by
    constructor
    · intro x y h
      exact R.unimod.1 (neg_injective (by simpa using h))
    · intro f
      obtain ⟨x, hx⟩ := R.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  adj a a' h x y := by simp [R.adj a a' h x y]
  P :=
    { toFun := fun x => star (R.P x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := by
    ext i j
    have := R.herm.apply i j
    simp [Matrix.conjTranspose_apply, ← this]
  pos z hz := by
    have h := R.pos (star z) (by simpa using hz)
    have h' := star_herm R.Hm (star z) (star z)
    simp only [star_star] at h'
    rw [h']
    simpa using h
  im x y := by
    have h := R.im x y
    have h' := star_herm R.Hm (R.P x) (R.P y)
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h']
    simp [h]
  B := (conjEnd g).comp R.B
  act a x := by simp [conjEnd_apply, R.act]

theorem conj_rt_iff (H : Host E) (s : E →+* ℂ) :
    ((starRingEnd ℂ).comp s) (H.rt : E) = H.rt0 ↔ ¬ s (H.rt : E) = H.rt0 := by
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h2 : s (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => s (a : E)) H.rt_sq
    simpa using h
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have hi := congrArg Complex.im h0
    have hr := congrArg Complex.re h0
    simp [pow_two] at hi hr
    rcases (by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact mul_eq_zero.1 this) with h | h
    · exact h
    · exfalso; rw [h] at hr; nlinarith [mul_self_nonneg H.rt0.re]
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
    exact H.d_prime.ne_zero h0
  have hpm : s (H.rt : E) = H.rt0 ∨ s (H.rt : E) = -H.rt0 := by
    have : (s (H.rt : E) - H.rt0) * (s (H.rt : E) + H.rt0) = 0 := by
      linear_combination h2 - h0
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    exact hne (by linear_combination -(1 / 2 : ℂ) * h)
  rcases hpm with h | h
  · simp only [RingHom.comp_apply, h, hconj]
    simpa using hneg
  · simp only [RingHom.comp_apply, h, map_neg, hconj, neg_neg]
    simpa using hneg

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.PeriodConj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

open PeriodConj

theorem period_lattice_fibre_and_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod (FU.Di i) ty P → (∃ R : RiemLat E g (FU.Di i).La, R.form = (FU.Di i).EF ∧ FibreLat Xo.univ.t (FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) ∧ (∃ R : RiemLat E g (FU.Di i).La, R.form = -(FU.Di i).EF ∧ FibreLat Xo.univ.t (spMap (starRingEnd ℂ) ≫ FU.u i P) R ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.q else D.p) := by
  intro E _ _ _ H D l Xo σ g ty FU i P hty hP
  have hty' : IsTypeFn H (FU.Di i).p (FU.Di i).q ty := by
    rw [(FU.sig i).1, (FU.sig i).2]; exact hty
  obtain ⟨R, hRP, hRf, -, hrk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.riemLat_of_period E H (FU.Di i) g ty P hty' hP
  have hF : FibreLat Xo.univ.t (FU.u i P) R :=
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period E H D l Xo σ g ty FU i R P 1 hP hRf (by simp) (fun x => by simp [hRP]) Empty
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
  refine ⟨⟨R, hRf, hF, fun s => ?_⟩, ⟨conjLat R, ?_, ?_, fun s => ?_⟩⟩
  · rw [hrk s, (FU.sig i).1, (FU.sig i).2]
  · show -R.form = _
    rw [hRf]
  · exact (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move E H Xo.X Xo.X Xo.univ.t Xo.univ.t (𝟙 _) g _ R (conjLat R) (FU.u i P)).2
      (fun _ => rfl) rfl (fun _ _ => rfl) hF
  · have h1 : Module.finrank ℂ (eigSp (conjLat R).B (s.comp (algebraMap (𝓞 E) E))) =
        Module.finrank ℂ (eigSp R.B (((starRingEnd ℂ).comp s).comp (algebraMap (𝓞 E) E))) :=
      finrank_eigSp_conj R.B (s.comp (algebraMap (𝓞 E) E))
    rw [h1, hrk, (FU.sig i).1, (FU.sig i).2]
    by_cases h : s (H.rt : E) = H.rt0
    · rw [if_pos h, if_neg (fun h' => (conj_rt_iff H s).1 h' h)]
    · rw [if_neg h, if_pos ((conj_rt_iff H s).2 h)]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

