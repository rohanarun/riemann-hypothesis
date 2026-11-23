module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothFunctionAsDegreeZeroMetric
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0007
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0107
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairLatticeSumComap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeSum

section LinearAlgebra

open _root_.Submodule

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]

theorem range_append {α : Type} {r s : ℕ} (f : Fin r → α) (g : Fin s → α) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact Or.inl ⟨i, by simp⟩
    · exact Or.inr ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd s i, by simp⟩
    · exact ⟨Fin.natAdd r i, by simp⟩

theorem linearIndependent_append {r s : ℕ} {f : Fin r → V} {g : Fin s → V} (hf : LinearIndependent Ω f)
    (hg : LinearIndependent Ω g) (hd : Disjoint (span Ω (Set.range f)) (span Ω (Set.range g))) :
    LinearIndependent Ω (Fin.append f g) := by
  have h := hf.sum_type hg hd
  have e : Fin.append f g = Sum.elim f g ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp
  rw [e]
  exact h.comp _ finSumFinEquiv.symm.injective

theorem span_lift_eq_top {W : Submodule Ω V} {n : ℕ} {v : Fin n → V} {c : Fin n → W} (hc : ∀ k, (c k : V) = v k)
    (hv : span Ω (Set.range v) = W) : span Ω (Set.range c) = ⊤ := by
  apply Submodule.map_injective_of_injective W.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  have e : (W.subtype ∘ c) = v := funext hc
  rw [show (⇑W.subtype ∘ c) = v from e, hv]

theorem comap_sup_span (A : Subring Ω) {W : Submodule Ω V} {r s : ℕ} {f : Fin r → V} {g : Fin s → V}
    {c : Fin (r + s) → W} (hc : ∀ k, (c k : V) = Fin.append f g k) :
    (span A (Set.range f) ⊔ span A (Set.range g)).comap (W.subtype.restrictScalars A) =
      span A (Set.range c) := by
  have hinj : Function.Injective (W.subtype.restrictScalars A) := W.injective_subtype
  have e : span A (Set.range f) ⊔ span A (Set.range g) =
      (span A (Set.range c)).map (W.subtype.restrictScalars A) := by
    rw [Submodule.map_span, ← Set.range_comp, ← Submodule.span_union, ← range_append]
    congr 2
    exact funext fun k => (hc k).symm
  rw [e, Submodule.comap_map_eq_of_injective hinj]

end LinearAlgebra

end GlobalTheory.CompanionTheory.Ar.HodgeSum

theorem GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (a b : CMType H ⊕ CMType H), a ≠ b → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsVB (labelRk D a + labelRk D b) ⊤ := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 a b hab
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨-, -, -, -, -, -, hind, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hβ
  have hdisj : Disjoint (𝔐.Vgen a) (𝔐.Vgen b) := hind.pairwiseDisjoint hab
  intro p _
  obtain ⟨Ua, hpa, f, hfs, hff⟩ := 𝔐.vb a p (Set.mem_univ _)
  obtain ⟨Ub, hpb, g, hgs, hgf⟩ := 𝔐.vb b p (Set.mem_univ _)
  have hfs' : Submodule.span Ω (Set.range f) = 𝔐.Vgen a := hfs
  have hgs' : Submodule.span Ω (Set.range g) = 𝔐.Vgen b := hgs
  have hspan : Submodule.span Ω (Set.range (Fin.append f g)) = 𝔐.Vgen a ⊔ 𝔐.Vgen b := by
    rw [HodgeSum.range_append, Submodule.span_union, hfs', hgs']
  have hmem : ∀ k, Fin.append f g k ∈ 𝔐.Vgen a ⊔ 𝔐.Vgen b := fun k => by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hli : LinearIndependent Ω (Fin.append f g) :=
    HodgeSum.linearIndependent_append (hff p (Set.mem_univ _) hpa).1 (hgf p (Set.mem_univ _) hpb).1
      (by rw [hfs', hgs']; exact hdisj)
  refine ⟨Ua ⊓ Ub, ⟨hpa, hpb⟩, fun k => ⟨Fin.append f g k, hmem k⟩,
    HodgeSum.span_lift_eq_top (fun _ => rfl) hspan, fun q _ hq => ⟨?_, ?_⟩⟩
  · exact LinearIndependent.of_comp (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype hli
  · have h1 : 𝔐.V a q = Submodule.span (regAt 𝔐.ξ q) (Set.range f) := (hff q (Set.mem_univ _) hq.1).2
    have h2 : 𝔐.V b q = Submodule.span (regAt 𝔐.ξ q) (Set.range g) := (hgf q (Set.mem_univ _) hq.2).2
    show (𝔐.V a q ⊔ 𝔐.V b q).comap ((𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype.restrictScalars (regAt 𝔐.ξ q)) = _
    rw [h1, h2]
    exact HodgeSum.comap_sup_span (regAt 𝔐.ξ q) fun _ => rfl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PositiveHomogeneousPotential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.FlatExt

open Filter Topology Set

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNz : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conj_mem_mcPts {P : Ideal (MRing J)} {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) :
    (fun p => starRingEnd ℂ (z p)) ∈ mcPts P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, by simpa using hi⟩
  · have h := hz.2 f hf
    rw [MvPolynomial.eval_map] at h ⊢
    have e := MvPolynomial.eval₂_comp_left (starRingEnd ℂ) (Int.castRingHom ℂ) z f
    rw [h, map_zero, Subsingleton.elim ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)] at e
    exact e.symm

theorem continuousOn_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X}
    {g : X → ℂ} (h : A.HoloOn U g) : ContinuousOn g U := by
  intro y hy
  obtain ⟨j, hj⟩ := A.cover y
  have hc := (A.chart j).continuousAt hj
  have hsy : (A.chart j).symm (A.chart j y) = y := (A.chart j).left_inv hj
  have han : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j y) :=
    (h j _ ⟨(A.chart j).map_source hj, by simpa [hsy] using hy⟩).continuousAt
  have hcomp : ContinuousAt ((g ∘ (A.chart j).symm) ∘ (A.chart j)) y := ContinuousAt.comp han hc
  refine (hcomp.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with w hw
  simp [(A.chart j).left_inv hw]

theorem analyticAt_lift {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (x : R.X) (j : Fin R.A.n)
    {t : Fin D → ℂ} (ht : t ∈ (R.A.chart j).target) (hx : (R.A.chart j).symm t ∈ R.U x) :
    AnalyticAt ℂ (fun t' => R.lift x ((R.A.chart j).symm t')) t :=
  AnalyticAt.pi fun p => R.holo x p j t ⟨ht, hx⟩

theorem ratio_eq {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (H : HermLine J) (hHa : H.a = a) {x y : R.X} (hy : y ∈ R.U x) :
    φ (R.lift y y) / H.h (R.lift y y) = φ (R.lift x y) / H.h (R.lift x y) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, hsm _ (R.mem x y hy) c hc, H.smul c _ hc, hHa, mul_div_mul_left _ _ hne]

theorem smooth_ratio {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) {a : K → ℤ}
    {φ : ((Σ k, J k) → ℂ) → ℝ}
    (hsm : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖)
    (H : HermLine J) (hHa : H.a = a) (hH : IsSmoothHerm H) :
    R.A.Smooth fun x => Real.log (φ (R.lift x x) / H.h (R.lift x x)) := by
  intro j t ht
  have ht : t ∈ (R.A.chart j).target := ht.1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = (R.A.chart j).symm t := ⟨_, rfl⟩
  have hm₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hγ : AnalyticAt ℂ (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    analyticAt_lift R x₀ j ht (hx₀ ▸ R.mem_U _)
  have hγt : R.lift x₀ ((R.A.chart j).symm t) = R.lift x₀ x₀ := by rw [hx₀]
  have hsc : ContinuousAt (R.A.chart j).symm t := (R.A.chart j).continuousAt_symm ht
  have hev : ∀ᶠ t' in 𝓝 t, (R.A.chart j).symm t' ∈ R.U x₀ ∧
      R.lift x₀ ((R.A.chart j).symm t') ∈ V := by
    refine (hsc.eventually ((R.isOpen_U x₀).mem_nhds (hx₀ ▸ R.mem_U _))).and
      (hγ.continuousAt.eventually (hV.mem_nhds ?_))
    show R.lift x₀ ((R.A.chart j).symm t) ∈ V
    rw [hγt]
    exact hzV
  have hne : F (R.lift x₀ ((R.A.chart j).symm t)) ≠ 0 := by
    rw [hγt]
    exact (hFφ _ ⟨hzV, hm₀⟩).1
  have hFa : AnalyticAt ℂ (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    AnalyticAt.fun_comp (hF _ (by rw [hγt]; exact hzV)) hγ
  have e1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => F (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    hFa.contDiffAt.restrict_scalars ℝ
  have e2 := (e1.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hγr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => R.lift x₀ ((R.A.chart j).symm t')) t :=
    hγ.contDiffAt.restrict_scalars ℝ
  have hmem : R.lift x₀ ((R.A.chart j).symm t) ∈ {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    rw [hγt]
    exact hm₀.1
  have e3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t' => H.h (R.lift x₀ ((R.A.chart j).symm t'))) t :=
    ContDiffAt.comp t (hH.contDiffAt (isOpen_blockNz.mem_nhds hmem)) hγr
  have e4 := e3.log (H.pos _ hmem).ne'
  refine ((e2.sub e4).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hev] with t' ht'
  obtain ⟨h1, h2⟩ := ht'
  have hm := R.mem _ _ h1
  obtain ⟨h0, hφ⟩ := hFφ _ ⟨h2, hm⟩
  show Real.log (φ (R.lift _ _) / H.h (R.lift _ _)) = _
  rw [ratio_eq R hsm H hHa h1, hφ, Real.log_div (norm_ne_zero_iff.2 h0) (H.pos _ hm.1).ne']

theorem isFlatOn_of_local {P Jd : Ideal (MRing J)} {D : ℕ} (R : AnLogRes P Jd D) (T : HermLine J)
    {φ : ((Σ k, J k) → ℂ) → ℝ} (hT : ∀ z ∈ mcPts P, T.h z = φ z)
    (hloc : ∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) :
    IsFlatOn R T := by
  intro x _
  have hm₀ : R.lift x x ∈ mcPts P := R.mem _ _ (R.mem_U _)
  obtain ⟨V, F, hV, hzV, hF, hFφ⟩ := hloc _ hm₀
  have hcl : ContinuousOn (R.lift x) (R.U x) :=
    continuousOn_pi.2 fun p => continuousOn_of_holoOn R.A (R.holo x p)
  have hW₁ : IsOpen (R.U x ∩ R.lift x ⁻¹' V) := hcl.isOpen_inter_preimage (R.isOpen_U x) hV
  have hf0 : F (R.lift x x) ≠ 0 := (hFφ _ ⟨hzV, hm₀⟩).1
  have hfc : ContinuousOn (fun y => F (R.lift x y) / F (R.lift x x)) (R.U x ∩ R.lift x ⁻¹' V) :=
    (hF.continuousOn.comp (hcl.mono inter_subset_left) fun y hy => hy.2).div_const _
  have hW := hfc.isOpen_inter_preimage hW₁ Complex.isOpen_slitPlane
  refine ⟨_, hW, ⟨⟨R.mem_U x, hzV⟩, by simp [hf0]⟩,
    fun y => Complex.log (F (R.lift x y) / F (R.lift x x)) + (Real.log ‖F (R.lift x x)‖ : ℂ), ?_, ?_⟩
  · intro j t ht
    have hγ := analyticAt_lift R x j ht.1 ht.2.1.1
    have hFa : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t'))) t :=
      AnalyticAt.fun_comp (hF _ ht.2.1.2) hγ
    have hga : AnalyticAt ℂ (fun t' => F (R.lift x ((R.A.chart j).symm t')) / F (R.lift x x)) t :=
      hFa.div analyticAt_const hf0
    exact (hga.clog ht.2.2).add analyticAt_const
  · intro y hy
    have hm : R.lift x y ∈ V ∩ mcPts P := ⟨hy.1.2, R.mem x y hy.1.1⟩
    obtain ⟨h0, h1⟩ := hFφ _ hm
    show Real.log (T.h (R.lift x y)) - 0 = _
    rw [hT _ hm.2, h1, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 h0) (norm_ne_zero_iff.2 hf0)]
    ring

theorem exists_flat_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P ⊤ D) (a : K → ℤ) (φ : ((Σ k, J k) → ℂ) → ℝ), (∀ z ∈ mcPts P, 0 < φ z) → (∀ z ∈ mcPts P, φ (fun p => starRingEnd ℂ (z p)) = φ z) → (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → φ (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * φ z) → (∀ z ∈ mcPts P, ∃ (V : Set ((Σ k, J k) → ℂ)) (F : ((Σ k, J k) → ℂ) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ F V ∧ ∀ z' ∈ V ∩ mcPts P, F z' ≠ 0 ∧ φ z' = ‖F z'‖) → ∃ T : HermLine J, T.a = a ∧ IsSmoothHerm T ∧ IsConjInvariantH T ∧ (∀ z ∈ mcPts P, T.h z = φ z) ∧ IsFlatOn R T := by
  intro K _ J _ P D R a φ hpos hconj hsm hloc
  have hHs : IsSmoothHerm (GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a) :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FsInvPow.isSmoothHerm_fsHerm a
  obtain ⟨H, hHdef⟩ : ∃ H, H = GroundTheory.Heights₂.Heights.LowerBoundFree.fsHerm J a := ⟨_, rfl⟩
  have hHa : H.a = a := by rw [hHdef]; rfl
  rw [← hHdef] at hHs
  obtain ⟨B, hBa, hBs, hB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.exists_hermLine_log_eq_of_smooth K J P D R _ (smooth_ratio R hsm hloc H hHa hHs)
  have hT₀s : IsSmoothHerm (H.tensor B) := ContDiffOn.mul hHs hBs
  have hT₀a : (H.tensor B).a = a := by
    show H.a + B.a = a
    rw [hHa, hBa, add_zero]
  have hpt : ∀ x, (H.tensor B).h (R.lift x x) = φ (R.lift x x) := by
    intro x
    have hm := R.mem x x (R.mem_U x)
    have hHp := H.pos _ hm.1
    have hBp := B.pos _ hm.1
    have hq : 0 < φ (R.lift x x) / H.h (R.lift x x) := div_pos (hpos _ hm) hHp
    have e := Real.log_injOn_pos (Set.mem_Ioi.2 hBp) (Set.mem_Ioi.2 hq) (hB x)
    show H.h _ * B.h _ = _
    rw [e]
    field_simp
  have hT₀ : ∀ z ∈ mcPts P, (H.tensor B).h z = φ z := by
    intro z hz
    have hnt : z ∉ mcPts (⊤ : Ideal (MRing J)) := fun h => by
      have h1 := h.2 1 trivial
      simp at h1
    obtain ⟨x, c, hc, e⟩ := R.surj z hz hnt
    have hne : (∏ k, ‖c k‖ ^ a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    have h1 := hpt x
    rw [e, (H.tensor B).smul c z hc, hT₀a, hsm z hz c hc] at h1
    exact mul_left_cancel₀ hne h1
  obtain ⟨T, hTa, hTs, hTc, hT⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.exists_conjInvariant_line_averaged K J (H.tensor B) hT₀s
  have hTφ : ∀ z ∈ mcPts P, T.h z = φ z := by
    intro z hz
    have hc := conj_mem_mcPts hz
    have e := hT z hz.1
    rw [hT₀ z hz, hT₀ _ hc, hconj z hz, add_self_div_two] at e
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (T.pos z hz.1)) (Set.mem_Ioi.2 (hpos z hz)) e
  exact ⟨T, hTa.trans hT₀a, hTs, hTc, hTφ, isFlatOn_of_local R T hTφ hloc⟩

end GlobalTheory.CompanionTheory.Ar.Chg.FlatExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

def propFTopE {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) : ℝ :=
  if hp : 2 ≤ p then Classical.choose (_root_.GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one Ψ N T.j p τ (frob p τ) T.j_lt.le hp) else 0

theorem propFTopE_spec {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N)
    (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (p : ℕ) (τ : Ψ) (hp : 2 ≤ p) :
    |propFTopE T frob p τ| ≤ N / ((p : ℝ) - 1) ∧
      ∀ Q : RP Ψ N, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q := by
  have h := Classical.choose_spec (_root_.GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one Ψ N T.j p τ (frob p τ) T.j_lt.le hp)
  simp only [propFTopE, dif_pos hp]
  exact ⟨h.1, h.2.2.2⟩

theorem propFTop : PropFTop := by
  intro hPI hML hDS Ψ _ _ N T II frob rd Lval hII hConv hProp hP6 hrd hbad hNear
  classical
  choose R hR using hNear
  let good : ℕ → Finset ℕ := fun B => (Finset.Ioc 2 B).filter (fun p => p.Prime ∧ p ∉ T.bad)
  refine ⟨fun B c τ => (R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p, ?_, ?_⟩
  · intro B hB c τ Q hQ
    have hN : 1 ≤ N := by have := T.j_pos; have := T.j_lt; omega
    have hQ' : Q.IsHomogeneous (dimFl Ψ N + 1 - 1) := by rwa [Nat.add_sub_cancel]
    have h6 := hP6 2 B le_rfl hB c τ 1 le_rfl hN Q hQ'
    have hroot := _root_.GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq hPI hML hDS Ψ N (T.M 2 c) II τ (R c τ) Q hII (hConv 2 c) hQ
    have hgeo := hProp.2.1 2 c Q
    have hd : ∀ p ∈ good B, deltaTerm T.j p τ (frob p τ) 1 Q = propFTopE T frob p τ * Real.log p * degFl Q :=
      fun p hp => (propFTopE_spec T frob p τ (Finset.mem_filter.mp hp).2.1.two_le).2 Q
    have h2 : T.PPc II 2 c (pk τ 1 * Q) = (R c τ).ht * (T.vol c * degFl Q) := by
      simp only [RootTower.PPc]; rw [hroot, hgeo]
    rw [Finset.sum_congr rfl hd] at h6
    rw [sub_mul, Finset.sum_mul]
    rw [h2] at h6
    rw [← Finset.sum_mul] at h6 ⊢
    change _ = _ + T.vol c * ((∑ p ∈ good B, propFTopE T frob p τ * Real.log p) * degFl Q) at h6
    linarith [h6]
  · intro B hB hcard c τ
    obtain ⟨hrec, d, v, hrec_le, hEq, hdv, hvsum⟩ := hR c τ
    have hdisj : Disjoint T.bad (good B) :=
      Finset.disjoint_left.mpr fun p hp hg => (Finset.mem_filter.mp hg).2.2 hp
    let d' : ℕ → ℝ := fun p => if p ∈ T.bad then d p else -(propFTopE T frob p τ * Real.log p)
    let v' : ℕ → ℝ := fun p => if p ∈ T.bad then v p else 0
    have hsb : ∑ p ∈ T.bad, d' p = ∑ p ∈ T.bad, d p :=
      Finset.sum_congr rfl fun p hp => by simp [d', hp]
    have hsg : ∑ p ∈ good B, d' p = -∑ p ∈ good B, propFTopE T frob p τ * Real.log p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p hp => by
        simp [d', Finset.disjoint_right.mp hdisj hp]
    have hvb : ∑ p ∈ T.bad ∪ good B, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p := by
      rw [Finset.sum_union hdisj]
      have h1 : ∑ p ∈ T.bad, v' p * Real.log p = ∑ p ∈ T.bad, v p * Real.log p :=
        Finset.sum_congr rfl fun p hp => by simp [v', hp]
      have h2 : ∑ p ∈ good B, v' p * Real.log p = 0 :=
        Finset.sum_eq_zero fun p hp => by simp [v', Finset.disjoint_right.mp hdisj hp]
      rw [h1, h2, add_zero]
    have hS : ∀ p ∈ T.bad ∪ good B, p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact ⟨hbad p hp, Or.inr hp⟩
      · have := Finset.mem_filter.mp hp
        exact ⟨this.2.1, Or.inl (Finset.mem_Ioc.mp this.1).2⟩
    have hB3 : 3 ≤ B := by omega
    have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
    have hmain := hB_bound N T.j B (T.bad ∪ good B) d' v' (Real.log rd) Lval hrec
      ((R c τ).ht - ∑ p ∈ good B, propFTopE T frob p τ * Real.log p) T.j_lt.le hB3 hlrd hrec_le
      (by rw [Finset.sum_union hdisj, hsb, hsg, hEq]; ring)
      (fun p hp => (hS p hp).1)
      (fun p hp => by
        by_cases hb : p ∈ T.bad
        · simp only [v', hb, if_true]; exact (hdv p hb).1
        · simp [v', hb])
      (fun p hp => by
        have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
        by_cases hb : p ∈ T.bad
        · simp only [d', v', hb, if_true]
          refine (hdv p hb).2.trans (le_of_eq ?_)
          ring
        · simp only [d', v', hb, if_false, mul_zero, add_zero, abs_neg, abs_mul, abs_of_nonneg hlog]
          exact mul_le_mul_of_nonneg_right
            (propFTopE_spec T frob p τ (hS p hp).1.two_le).1 hlog)
      (by rw [hvb]; exact hvsum)
      (_root_.GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB B T.bad (T.bad ∪ good B) hB hcard hS)
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hrdpos : (0 : ℝ) < rd := by linarith
    simp only [bigLam]
    rw [Real.log_mul hBpos.ne' hrdpos.ne']
    simpa [add_assoc] using hmain

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionSplitMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_split_map : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torus_extension_generic | exact GlobalTheory.CompanionTheory.Ar.torus_extension_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.torus_extension_generic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExactStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_tangent_exact : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | exact GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | (intros; apply GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtGenIndependentChoiceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.val_at_gen_independent_choice : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (a : K → ℤ) (e₀ τ : Ω) (c₀ c₁ : (k : K) → J k) (u u' : ℂ),
    IsCptGen ξ → e₀ ≠ 0 → CoordsAt ξ y z w → (∀ k, w ⟨k, c₀ k⟩ ≠ 0) → (∀ k, w ⟨k, c₁ k⟩ ≠ 0) →
    ValAt ξ z (τ / gen y a e₀ c₀) u → ValAt ξ z (τ / gen y a e₀ c₁) u' →
    u * ∏ k, w ⟨k, c₀ k⟩ ^ a k = u' * ∏ k, w ⟨k, c₁ k⟩ ^ a k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gen_chart_change <;> assumption)
end

