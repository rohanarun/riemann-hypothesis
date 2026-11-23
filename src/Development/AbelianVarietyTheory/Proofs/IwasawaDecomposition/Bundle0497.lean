module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSLin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomain
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre.FundPre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ae_lact_notMem (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {Bad : Set (Frame X.Ψ r)} (hB : MeasurableSet Bad)
    (hinv : ∀ x, ∀ b ∈ Bor X.Ψ r, (rmul x b ∈ Bad ↔ x ∈ Bad))
    (h0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ∀ᵐ z ∂muF X x0, lact γ (cpt X x0 z) ∉ Bad := by
  have hφ : Measurable (Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) :=
    measurable_one.indicator hB
  have hM := measInv_holds (E := E) r X x0 (lact γ x0) ho (KU.isOrth_lact X hγ ho)
    (Bad.indicator 1) hφ (fun x _ b hb => by
      classical
      simp only [Set.indicator_apply, hinv x b hb, Pi.one_apply])
  have h1 : ∫⁻ z, Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
    filter_upwards [h0] with z hz
    exact Set.indicator_of_notMem hz _
  rw [h1, KU.muF_lact X hγ] at hM
  have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (lact γ x0) z) :=
    hφ.comp (KU.cont_cpt X _).measurable
  have h2 := (lintegral_eq_zero_iff hm).1 hM.symm
  filter_upwards [h2] with z hz hbad
  rw [← KU.cpt_lact] at hbad
  simp only [Set.indicator_of_mem hbad, Pi.one_apply, Pi.zero_apply] at hz
  exact one_ne_zero hz

theorem isFundSet_preimage (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ)
    (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ)
    (hp : X.p0 = r - j)
    (hfree : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1)
    (hnull : ∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 →
      muF X (x0F X) (proj X hj κ ⁻¹' N) = 0)
    (F : Set (Tau × Fin j × Fin (r - j) → ℂ)) (hF : IsFD (gammaU X hj κ) F) :
    ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧
      IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  obtain ⟨hFm, hFD, hcov, hbad⟩ := hF
  obtain ⟨N0, hN0, hN0m, hN0z⟩ := exists_measurable_superset_of_null hbad
  have ho := isOrth_x0F X
  have hOm : MeasurableSet (OmF X (x0F X)) :=
    ((FourierCoefficientDomain.isOpen_dom X).preimage (KU.cont_cpt X (x0F X))).measurableSet
  have hNm : MeasurableSet (F ∩ N0) := hFm.inter hN0m
  have hNz : muD Tau j (r - j) (F ∩ N0) = 0 := measure_mono_null Set.inter_subset_right hN0z
  refine ⟨F \ N0, hFm.diff hN0m, Set.sdiff_subset, ?_, ?_, Set.inter_subset_right, ?_, ?_⟩
  · rw [Set.sdiff_sdiff_right_self]; exact hNz
  · exact (measurable_proj X hj κ (hFm.diff hN0m)).inter hOm
  · rintro z ⟨⟨hz, hzN⟩, hzO⟩ z' ⟨⟨hz', -⟩, -⟩ γ hγ b hb h
    have hd : domPt X hj κ (cpt X (x0F X) z') = domPt X hj κ (lact γ (cpt X (x0F X) z)) := by
      rw [h, KU.lact_rmul', domPt_rmul X hj κ hb]
    have hfix : domPt X hj κ (lact γ (cpt X (x0F X) z)) = domPt X hj κ (cpt X (x0F X) z) := by
      by_contra hne
      apply hzN
      apply hN0
      refine ⟨hz, toUpq X hj κ γ, ⟨γ, hγ, rfl⟩, ?_, ?_⟩
      · change flat (moebI _ (domPt X hj κ (cpt X (x0F X) z))) ∈ F
        rw [← domPt_lact X hj κ hp γ hzO, ← hd]
        exact hz'
      · change moebI _ (domPt X hj κ (cpt X (x0F X) z)) ≠ domPt X hj κ (cpt X (x0F X) z)
        rw [← domPt_lact X hj κ hp γ hzO]
        exact hne
    have h1 := hfree γ hγ _ hzO hfix
    rw [h1, KU.lact_one] at h
    have hS : cpt X (x0F X) z' ∈ KU.Sset X (x0F X) {z} := by
      rw [h, KU.rmul_mem_S X hb, KU.cpt_mem_S X ho]
      rfl
    exact ((KU.cpt_mem_S X ho z').1 hS).symm
  · have := KU.countable_Γ X
    have hA : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (fun x => flat (domPt X hj κ x)) ⁻¹' (F ∩ N0) := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (measurable_domPt X hj κ hNm) ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_preimage, domPt_rmul X hj κ hb]
      · exact measure_eq_zero_iff_ae_notMem.1
          (hnull _ hNm (Set.inter_subset_left.trans hFD) hNz)
    have hB : ∀ᵐ z ∂muF X (x0F X), ∀ γ : X.Γ, lact (γ : GL (Fin r) E) (cpt X (x0F X) z) ∉
        (KU.Sset X (x0F X) (OmF X (x0F X)))ᶜ := by
      refine ae_all_iff.2 fun γ => ae_lact_notMem X ho (KU.meas_S X ho hOm).compl ?_ ?_ γ.2
      · intro x b hb
        simp only [Set.mem_compl_iff, KU.rmul_mem_S X hb]
      · filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hz hn
        exact hn ((KU.cpt_mem_S X ho z).2 hz)
    filter_upwards [hA, hB, ExtFPf.ae_OmF (X := X) (x0 := x0F X)] with z hzA hzB hzO
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγF⟩ := hcov _ (domPt_mem X hj κ hp hzO)
    rw [← domPt_lact X hj κ hp γ hzO] at hγF
    have h1 := hzA ⟨γ, hγ⟩
    obtain ⟨⟨z', b⟩, ⟨hz', hb⟩, he⟩ := not_not.1 (hzB ⟨γ, hγ⟩)
    have he' : rmul (cpt X (x0F X) z') b = lact γ (cpt X (x0F X) z) := he
    have hpr : proj X hj κ z' = flat (domPt X hj κ (lact γ (cpt X (x0F X) z))) := by
      rw [← he', domPt_rmul X hj κ hb]; rfl
    refine ⟨z', ⟨?_, hz'⟩, γ⁻¹, X.Γ.inv_mem hγ, b, hb, ?_⟩
    · rw [Set.mem_preimage, hpr]
      exact ⟨hγF, fun hn => h1 ⟨hγF, hn⟩⟩
    · rw [he', KU.lact_lact, inv_mul_cancel, KU.lact_one]

end GlobalTheory.FlagFibre.FundPre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsReferenceTupleBasisExtended
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC

open _root_.Formalism.L2.Col

section LiftBasis

variable {K L : Type} [Field K] [NumberField K] [StarRing K] [Field L] [NumberField L] [StarRing L] {ι : K →+* L}
  {S : GSD K} {S' : GSD L}

theorem gsdbc_lift_span (b : GSDBC ι S S') {κ : Type} [Fintype κ] (v : Module.Basis κ K S.EqFun) :
    ⊤ ≤ Submodule.span L (Set.range fun k => b.lift (v k)) := by
  obtain ⟨F⟩ := CoefFrame.nonempty ι
  intro φ _
  have h1 : Submodule.span L (Set.range b.lift) ≤ Submodule.span L (Set.range fun k => b.lift (v k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨ψ, rfl⟩
    rw [← v.sum_repr ψ, b.lift_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact h1 (b.mem_span_lift F φ)

theorem gsdbc_lift_li (b : GSDBC ι S S') {κ : Type} [Fintype κ] (v : Module.Basis κ K S.EqFun) :
    LinearIndependent L (fun k => b.lift (v k)) := by
  letI : Algebra K L := ι.toAlgebra
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ L) q, eq_ratCast (algebraMap ℚ K) q, map_ratCast]
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let e := Module.finBasis K L
  rw [Fintype.linearIndependent_iff]
  intro c hc k
  have hs : ∀ m, (∑ k, e.repr (c k) m • v k) = 0 := by
    intro m
    apply Subtype.ext
    funext d
    apply S.bV.ext_elem
    intro i
    have h0 := congrArg (fun x : S'.EqFun => b.bas.repr ((x : S'.D → S'.V) (b.eD.symm d)) i) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, Finset.sum_apply, map_sum, Finsupp.finsetSum_apply] at h0
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finsupp.smul_apply, GSDBC.lift_apply, GSDBC.repr_j,
      Equiv.apply_symm_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, map_zero, Finsupp.zero_apply] at h0
    have h1 : (∑ k, S.bV.repr ((v k : S.D → S.V) d) i • c k) = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    have h2 := congrArg (fun x => e.repr x m) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
      Finsupp.zero_apply] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, Finset.sum_apply, map_sum, Finsupp.finsetSum_apply]
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply, map_zero, Finsupp.zero_apply]
    rw [← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hz : ∀ m, e.repr (c k) m = 0 := fun m =>
    Fintype.linearIndependent_iff.1 v.linearIndependent _ (hs m) k
  rw [← e.sum_repr (c k)]
  simp [hz]

theorem gsdbc_basis_of_read (b : GSDBC ι S S') {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (Lm : M → M')
    {_ : Module K M} {_ : Module L M'} (r : M ≃ₗ[K] S.EqFun) (r' : M' ≃ₗ[L] S'.EqFun) (hL : ∀ x, r' (Lm x) = b.lift (r x))
    {κ : Type} [Fintype κ] (v : Module.Basis κ K M) :
    LinearIndependent L (fun k => Lm (v k)) ∧ ⊤ ≤ Submodule.span L (Set.range fun k => Lm (v k)) := by
  have hv : ∀ k, Lm (v k) = r'.symm (b.lift ((v.map r) k)) := fun k => by
    rw [Module.Basis.map_apply, ← hL, LinearEquiv.symm_apply_apply]
  simp only [hv]
  refine ⟨(gsdbc_lift_li b _).map' r'.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
  have hr : (Set.range fun k => r'.symm (b.lift ((v.map r) k))) =
      r'.symm.toLinearMap '' Set.range fun k => b.lift ((v.map r) k) := by
    rw [← Set.range_comp]; rfl
  rw [hr, Submodule.span_image, eq_top_iff.2 (gsdbc_lift_span b _), Submodule.map_top, LinearEquiv.range]

end LiftBasis

end GlobalTheory.Mem.R3.DefLatBC


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mem.R3.DefLatBC.lift_basis_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms), (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) → (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1)) → LinearIndependent (w'.st Z').toD7.what₂.LL (fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k)) ∧ ⊤ ≤ Submodule.span (w'.st Z').toD7.what₂.LL (Set.range fun k => L (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.basis k))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  have H1 := GlobalTheory.T.formsData_extendedData_baseChange_sameValues h1 h2 h3 h4 h5 h6 h7
  have H2 := GlobalTheory.T.formsLift_extendedData_determined_by_values h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and H1 H2) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hL hC
  beta_reduce at H
  clear H1 H2
  have Ha := H.1 B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ
  cases Ha with
  | intro b hb =>
    exact GlobalTheory.Mem.R3.DefLatBC.gsdbc_basis_of_read b (fun x => L x) (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm (Formalism.L2.Col.GSD.res (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)) (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (H.2 B f T w hE hf hP hpx Z hX Wt z g1 g2 g3 g4 Z' hX' g5 g6 g7 z' g8 g9 j j' hj φ hφ L hC b hb) _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CuspFieldChange

open GlobalTheory.FieldBC GlobalTheory.SecFieldChange
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of evR_of_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

variable {c c₀ : Coeff l} (hle : c₀.F ≤ c.F)

theorem eq_sum_of_isBC {m : ℕ} {f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf' : f' ∈ sec Xo c a n)
    {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀} (h : IsBC hle f' as fs) : f' = ∑ i, as i • rulBC hle (fs i) := by
  funext q y
  letI := resAlg hle q.R
  rw [val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def]
  rfl

theorem cusp_unfBC_eq_span {r : ℕ} (U : ∀ σ : c₀.F →+* ℂ, Unf Xo c₀ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (unfBC hle U) a n = Submodule.span c.F (rulBC hle '' (cusp Xo c₀ U a n : Set (Rul Xo c₀))) := by
  refine le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, as, fs, hfs, h⟩ := cuspBC_holds hle U a n f' hf'
    rw [eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf

theorem linearIndependent_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {v : Fin m → Rul Xo c₀}
    (hv : ∀ i, v i ∈ sec Xo c₀ a n) (hi : LinearIndependent c₀.F v) :
    LinearIndependent c.F (fun i => rulBC hle (v i)) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c₀ :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))
  have hBC : HasBC Xo c₀ := hasBC_of hS
  letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro g hg i
  refine (Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_
  refine hi (fun j => lam (g j)) ?_ i
  funext p y
  have hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R) := fun x => ext_tower x
  obtain ⟨z, hz⟩ := hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y
  have h1 := evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))
  have h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0 := evalAt_zero _ _ _
  rw [hg, h0] at h1
  have h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y) := fun j => by
    rw [((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext,
      evR_of_map hWD (hv j).1 hz]
  simp only [h2] at h1
  have h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) =
      (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R) := fun j => by
    show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) :
      TensorProduct c₀.F c.F p.R) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y) :=
    h1.trans (Finset.sum_congr rfl fun j _ => h3 j)
  have h5 := congrArg (coord lam p.R) h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h5
  simp only [coord_tmul] at h5
  rw [Finset.sum_apply, Finset.sum_apply]
  exact h5.symm

end GlobalTheory.CuspFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.ProdFibre

theorem lintegral_pi_fibre : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  intro T A B C _ _ _ _ _ _ _ g π D φ hg hπ hgπ hD hφ
  have h1 : MeasurePreserving (fun (a : T → A × B) (t : T) => g (a t)) volume volume :=
    volume_preserving_pi (f := fun _ : T => g) (fun _ => hg)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow A B T).symm
  have h3 := h1.comp h2
  have hF : Measurable (fun c : T → C => φ (fun t => π (c t)) * ∏ t, D (c t)) := by
    refine Measurable.mul (hφ.comp ?_) ?_
    · exact Measurable.of_eval (fun t => hπ.comp (measurable_pi_apply t))
    · exact Finset.measurable_prod _ (fun t _ => hD.comp (measurable_pi_apply t))
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hF.comp h3.measurable).aemeasurable).trans ?_
  refine lintegral_congr (fun a => ?_)
  have hm : ∀ t, Measurable (fun b : B => D (g (a t, b))) := fun t =>
    hD.comp (hg.measurable.comp measurable_prodMk_left)
  have hin := GlobalTheory.SnMass.Push.lintegral_fintype_prod (X := fun _ : T => B)
    (μ := fun _ => (volume : Measure B)) (fun t b => D (g (a t, b))) hm
  rw [← hin, ← volume_pi, ← lintegral_const_mul]
  · refine lintegral_congr (fun b => ?_)
    change φ (fun t => π (g (a t, b t))) * ∏ t, D (g (a t, b t)) = _
    simp only [hgπ]
  · exact Finset.measurable_prod _ (fun t _ => (hm t).comp (measurable_pi_apply t))

end GlobalTheory.ProdFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem measurePreserving_coords_sorted (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ) :
    MeasurePreserving (coords X κ) volume volume := by
  let e : Fin (nd X) ≃ Tau × Low r :=
    ((Equiv.prodCongr κ (Equiv.refl (Low r))).trans (Fintype.equivFin (Ent X))).symm
  have h1 := GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X))
  have h2 := volume_preserving_arrowCongr' e (MeasurableEquiv.refl ℂ) (MeasurePreserving.id _)
  have h3 := GlobalTheory.FlagBase.PoissonV.measurePreserving_curry Tau (Low r)
  exact h3.comp (h2.comp h1)

end GlobalTheory.FlagFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
section
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

def FlowMajSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom → ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      X.maj (X.flow ξ s x) τ v = X.maj x τ v +
        ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
          (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ))) ∧
    ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (v w : Fin r → ℂ),
      ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w ∧ ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w

def OrbitThickSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∀ x ∈ X.dom, ∃ ε : ℝ, 0 < ε ∧ ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ → ε ≤ X.la1 (X.flow ξ s x)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ThickBdd (φ : Frame X.Ψ r → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ X.dom, ε ≤ X.la1 x → φ x ≤ C

def FreqNonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ

def StepBound (w : ℝ) (φ : Frame X.Ψ r → ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ q : X.Ψ → ℝ, (∀ τ, 0 < q τ ∧ q τ ≤ 1) → ∀ B : ℝ,
    (∀ s : X.Ψ → ℝ, φ (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) ≤ B) →
    φ x ≤ B * ∏ τ, q τ ^ (-w)

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FlowTie {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β)) (k : U.Comp) (ξ' : Fin r → E)
    (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)),
      (∀ τ, 0 < d τ) ∧ (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) ∧
      ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom,
        AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z

def BdExt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {V K : Type} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) : Prop :=
  ∃ (χ : Sp V ⟶ gen Z) (g : EigFrame Z φ (χ ≫ genι Z)), χ ≫ genStr Z = spMap φ ∧
    GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ ∧
    (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ g.v τ i) ∧
    χ (IsLocalRing.closedPoint V) ∈ genBd Z

end Geometric

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardReadingTransportAndExtensionTransStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardReading_transport_and_extension_trans : (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt), z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std) ∧ ∀ (B₁ B₂ B₃ : Base) f₁ f₂ f₃ T₁ T₂ T₃ (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (w₃ : ColW B₃ f₃ T₃) (Z₁ : w₁.Lt) (Z₂ : w₂.Lt) (Z₃ : w₃.Lt) h₁ h₂ h₃ W₁ W₂ W₃ (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂) (z₃ : Dat (w₃.st Z₃) w₃.I h₃ T₃ W₃), Enl B₁ B₂ → Enl B₂ B₃ → Ext z₁ z₂ → Ext z₂ z₃ → Ext z₁ z₃ := by
  first | exact @GlobalTheory.Mem.R3.Rw.StdTr.std_copy_and_ext_trans | exact GlobalTheory.Mem.R3.Rw.StdTr.std_copy_and_ext_trans | (intros; apply GlobalTheory.Mem.R3.Rw.StdTr.std_copy_and_ext_trans <;> assumption)
end

