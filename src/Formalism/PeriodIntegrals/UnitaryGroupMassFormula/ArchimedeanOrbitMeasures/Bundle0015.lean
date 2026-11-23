module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpTube
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpLimI
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem tubeG_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    TubeG X u' V = PI.AprimeInfG.tubeS (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      V Set.univ := by
  ext g
  constructor
  · rintro ⟨g', hg', he⟩
    have hs : g'⁻¹ * g ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, he, inv_smul_smul]
    exact ⟨g', hg', ⟨_, hs⟩, Set.mem_univ _, by simp⟩
  · rintro ⟨a, ha, h, -, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]

def GrpChart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (d : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ) (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧
    PI.AprimeInfG.TubeChart X.measG.μGinf (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
      ν κ χ r0 d e ∧
    ContinuousAt d 0 ∧ 0 < d 0 ∧ ContinuousAt e 0 ∧ 0 < e 0 ∧ d 0 / e 0 * (ν Set.univ).toReal = gVal X

theorem grpLim_of_chart {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpChart X u' κ) : GrpLim X u' κ := by
  obtain ⟨η, hη, χ, r0, d, e, ν, hL, hSF, h0, hf, hC, hd, hd0, he, he0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have := hL
  have := hSF
  obtain ⟨⟨ρ0, hρ0, hP⟩, hT⟩ := PI.AprimeInfG.tube_ratio X.measG.μGinf _ ν h0 hf hC hd hd0 he he0
  refine ⟨⟨ρ0, hρ0, fun ρ hρ hρ' => ?_⟩, fun ρ hρ hρl => ?_⟩
  · rw [tubeG_eq]; exact hP ρ hρ hρ'
  · simp only [tubeG_eq]
    rw [← hval]
    exact hT.comp (tendsto_nhdsWithin_iff.2 ⟨hρl, Filter.Eventually.of_forall hρ⟩)

def GrpPieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : Prop :=
  ∃ (η : Type) (_ : Fintype η)
    (χ : EuclideanSpace ℝ η → MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))
    (r0 : ℝ) (φ : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (U : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) (D : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → ℝ)
    (F : EuclideanSpace ℝ ι × EuclideanSpace ℝ η → EuclideanSpace ℝ ι × EuclideanSpace ℝ η)
    (F' : EuclideanSpace ℝ ι × EuclideanSpace ℝ η →
      (EuclideanSpace ℝ ι × EuclideanSpace ℝ η →L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η))
    (e : EuclideanSpace ℝ η → ℝ)
    (ν : Measure (MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))),
    ν.IsMulLeftInvariant ∧ SFinite ν ∧ ν Set.univ ≠ 0 ∧ ν Set.univ ≠ ⊤ ∧ 0 < r0 ∧
    ContinuousOn κ (ball 0 r0) ∧ ContinuousOn χ (ball 0 r0) ∧ Set.InjOn χ (ball 0 r0) ∧
    (∀ a ∈ ball (0 : EuclideanSpace ℝ ι) r0, ∀ b ∈ ball (0 : EuclideanSpace ℝ ι) r0,
      (κ a)⁻¹ * κ b ∈ MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') → a = b) ∧
    (∀ A ⊆ U, MeasurableSet A → X.measG.μGinf (φ '' A) = ∫⁻ z in A, ENNReal.ofReal (D z)) ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, HasFDerivWithinAt F (F' p) (ball 0 r0) p) ∧
    Set.InjOn F (ball 0 r0) ∧ F '' ball 0 r0 ⊆ U ∧
    (∀ p ∈ ball (0 : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) r0, κ p.1 * (χ p.2 : HA _ _ _) = φ (F p)) ∧
    (∀ s, 0 < s → s ≤ r0 → ν (χ '' ball 0 s) = ∫⁻ y in ball 0 s, ENNReal.ofReal (e y)) ∧
    ContinuousAt F 0 ∧ ContinuousAt (fun p => |(F' p).det|) 0 ∧ ContinuousAt D (F 0) ∧ ContinuousAt e 0 ∧
    0 < e 0 ∧ 0 < |(F' 0).det| * D (F 0) ∧ |(F' 0).det| * D (F 0) / e 0 * (ν Set.univ).toReal = gVal X

theorem grpChart_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) :
    GrpChart X u' κ := by
  obtain ⟨η, hη, χ, r0, φ, U, D, F, F', e, ν, hL, hSF, h0, hf, hr0, hκc, hχc, hχi, hinj, hφ, hF, hFi, hFU, hΦ,
    hνH, hFc, hdet, hD, he, he0, hd0, hval⟩ := h
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  have hcl : IsClosed ((MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :
      Subgroup (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    by
      have hc := PI.AprimeInfT.continuous_orbit (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))
      show IsClosed ((fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • Y0 X u') ⁻¹' {Y0 X u'})
      exact isClosed_singleton.preimage hc
  exact ⟨η, hη, χ, r0, fun p => |(F' p).det| * D (F p), e, ν, hL, hSF, h0, hf,
    PI.AprimeInfG.tubeChart_of X.measG.μGinf _ hcl ν κ χ hr0 hκc hχc hχi hinj φ U D hφ F F' hF hFi hFU hΦ e hνH,
    PI.AprimeInfG.contAt_dens hFc hdet hD, hd0, he, he0, hval⟩

theorem grpLim_of_pieces {D7' : D7} (X : HidaSetting D7') (u' : D7'.what₂.Word) {ι : Type} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (h : GrpPieces X u' κ) : GrpLim X u' κ :=
  grpLim_of_chart X u' κ (grpChart_of_pieces X u' κ h)

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacOneOfCharts
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def UnimodInf : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal) (h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J),
      ∫⁻ g, f (g * h) ∂X.measG.μGinf = ∫⁻ g, f g ∂X.measG.μGinf

def WittNear : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a Ω' a₂, IsChart X u' hT Ω a → IsChart X u' hT Ω' a₂ →
    ∀ T ∈ Ω ∩ Ω', IsUnit (a₂ T) → ∃ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      rmulT X (a T) (Y0 X u') = h • rmulT X (a₂ T) (Y0 X u')

def GoodChartEx : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω' a₂, IsChart X u' hT Ω' a₂ ∧ GoodP X u' hT μinf νinf a₂

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbAll
section
namespace PI.AprimeInfW

theorem orbRep_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbRep :=
  orbRep_of kerMeas_holds haarUniqInf_holds (regI_of hW) (hinfFin_of hC)

theorem orbUniq_of_witt (hW : WittInf) (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of (orbRep_of_witt hW hC)

theorem orbUniq_of_compact (hC : MassDataMassesW.HinfCompact) : OrbUniq :=
  orbUniq_of_witt wittInf_holds hC

end PI.AprimeInfW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarLocalOfFibres
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem act_continuous {D : D7} (X : HidaSetting D) (y : TupI X) :
    Continuous (fun g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g • y) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec (y a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec continuous_const

theorem actMeas_holds : ActMeas := by
  intro D X Z
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (act_continuous X Z).measurable

theorem polar_local_of_fibres (hK : KPos) (hG : GramMeas) (h1 : FibOrbAt) (h2 : PushCont) (h4 : JacOneC) : PolarLoc :=
  polar_local_of_action hK hG actMeas_holds h1 h2 h4

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ProperOne
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def ProperOne : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ K : Set (TupI X), IsCompact K →
      ∃ C : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J), IsCompact C ∧
        ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • Y0 X u' ∈ K → g ∈ C

def InvNbhd : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ N ∈ 𝓝 (1 : MfI X), ∃ Nc : Set (MfI X), IsCompact Nc ∧ ∀ b ∈ N, ∃ c ∈ Nc, c * b = 1

theorem continuous_right_mul_tuple {D : D7} (X : HidaSetting D) :
    Continuous (fun p : MfI X × TupI X => rmulT X p.1 p.2) := by
  have : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [rmulT]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply_apply c a).comp continuous_fst).mul ((continuous_apply_apply c i).comp continuous_snd)

theorem properOrb_of_one (h1 : ProperOne) (hI : InvNbhd) : ProperOrb := by
  intro D X u' ψ hT μinf νinf fibInf hH K hK _
  obtain ⟨N, hN, Nc, hNc, hNi⟩ := hI X
  have hK' : IsCompact ((fun p : MfI X × TupI X => rmulT X p.1 p.2) '' (Nc ×ˢ K)) :=
    (hNc.prod hK).image (continuous_right_mul_tuple X)
  obtain ⟨C, hC, hgC⟩ := h1 X u' ψ hT μinf νinf fibInf hH _ hK'
  refine ⟨N, hN, C, hC, fun b hb g hg => hgC g ?_⟩
  obtain ⟨c, hc, hcb⟩ := hNi b hb
  have hbc : b * c = 1 := mul_eq_one_comm.1 hcb
  refine ⟨(c, g • rmulT X b (Y0 X u')), ⟨hc, hg⟩, ?_⟩
  show rmulT X c (g • rmulT X b (Y0 X u')) = g • Y0 X u'
  rw [smul_rmulT, rmulT_rmulT, hbc, rmulT_one]

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SelfDualMap
section
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

theorem smul_add_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    g • (x + y) = g • x + g • y := by
  simp only [HSMul.hSMul, SMul.smul]
  funext a
  simp only [actTup, Pi.add_apply, mulVec_add]

theorem smul_neg_tup {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (y : TupI X) :
    g • (-y) = -(g • y) := by
  have h0 : g • (0 : TupI X) = 0 := by
    simpa using smul_add_tup X g 0 0
  have h := smul_add_tup X g (-y) y
  rw [neg_add_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private theorem hform_mulVec_eq_of_cT_mul_mul_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J g : Matrix n n A) (hg : Formalism.UG.cT σ g * J * g = J) (x y : n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v) := by
    intro u v
    first
    | simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp only [Formalism.UG.hform, Matrix.dotProduct, mulVec, Function.comp, Finset.mul_sum, mul_assoc]
    | simp [Formalism.UG.hform, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ g x i
  have e1 : (g.map σ) *ᵥ (σ ∘ x) = (σ ∘ x) ᵥ* (g.map σ)ᵀ := (vecMul_transpose _ _).symm
  have hg' : (g.map σ)ᵀ * J * g = J := hg
  rw [key, key, hσ, e1, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [hg']

theorem BR_smul {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x y : TupI X) :
    BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • x) (g • y) = BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y := by
  simp only [HSMul.hSMul, SMul.smul]
  unfold BR
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf X.B.I.F) X.B.I.cm.sig)
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) * JR (Ainf X.B.I.F) X.B.I.J *
      (↑(HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g) : Matrix _ _ _) = JR (Ainf X.B.I.F) X.B.I.J :=
    (show HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J from g).2
  exact hform_mulVec_eq_of_cT_mul_mul_eq _ _ _ hg _ _

def smulAE {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) : TupI X ≃+ TupI X where
  toFun y := g • y
  invFun y := g⁻¹ • y
  left_inv y := inv_smul_smul g y
  right_inv y := smul_inv_smul g y
  map_add' x y := smul_add_tup X g x y

private theorem selfDual_map_of_isAddHaarMeasure {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (χ : V → V → ℂ) (em : V ≃ᵐ V) (hH : (μ.map em).IsAddHaarMeasure)
    (hχ : ∀ a b, χ (em a) (em b) = χ a b) (hneg : ∀ a, em (-a) = -(em a))
    (hcont : ∀ Φ : V → ℂ, Continuous Φ → HasCompactSupport Φ →
      Continuous (Φ ∘ em) ∧ HasCompactSupport (Φ ∘ em))
    (hμ : SelfDual μ χ) : SelfDual (μ.map em) χ := by
  refine ⟨hH, fun Φ hΦc hΦs hint z => ?_⟩
  obtain ⟨hc', hs'⟩ := hcont Φ hΦc hΦs
  have hinner : ∀ y, ∫ x, Φ x * χ x (em y) ∂(μ.map em) = ∫ x, (Φ ∘ em) x * χ x y ∂μ := by
    intro y
    rw [integral_map_equiv]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, hχ]
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ em) x * χ x y ∂μ) μ := by
    have h1 := (integrable_map_equiv em _).mp hint
    refine h1.congr (ae_of_all _ fun y => ?_)
    simp only [Function.comp_apply]
    exact hinner y
  have hz : ∀ y, χ (em y) z = χ y (em.symm z) := by
    intro y
    conv_lhs => rw [← em.apply_symm_apply z]
    exact hχ y (em.symm z)
  calc ∫ y, (∫ x, Φ x * χ x y ∂(μ.map em)) * χ y z ∂(μ.map em)
      = ∫ y, (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z ∂μ := integral_map_equiv em _
    _ = ∫ y, (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        show (∫ x, Φ x * χ x (em y) ∂(μ.map em)) * χ (em y) z =
          (∫ x, (Φ ∘ em) x * χ x y ∂μ) * χ y (em.symm z)
        rw [hinner y, hz y]
    _ = (Φ ∘ em) (-(em.symm z)) := hμ.2 (Φ ∘ em) hc' hs' hint' (em.symm z)
    _ = Φ (-z) := by simp only [Function.comp_apply, hneg, MeasurableEquiv.apply_symm_apply]

theorem selfDual_map {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (μ : Measure (TupI X))
    (hμ : SelfDual μ (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    SelfDual (μ.map (fun y => g • y)) (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) := by
  have hc : ∀ h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, Continuous (fun y : TupI X => h • y) := by
    intro h
    first
    | fun_prop
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup; fun_prop)
    | (simp only [HSMul.hSMul, SMul.smul]; unfold actTup;
        exact continuous_pi fun a => Continuous.matrix_mulVec continuous_const (continuous_apply a))
  let e : TupI X ≃ₜ TupI X :=
    { toEquiv := (smulAE X g).toEquiv
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  have hH : (μ.map e.toMeasurableEquiv).IsAddHaarMeasure := by
    haveI := hμ.1
    first
    | exact (smulAE X g).isAddHaarMeasure_map μ (hc g) (hc g⁻¹)
    | exact (smulAE X g).isAddHaarMeasure_map (hc g) (hc g⁻¹)
  exact selfDual_map_of_isAddHaarMeasure μ
    (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y'))
    e.toMeasurableEquiv hH
    (fun a b => by
      show psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (g • a) (g • b)) =
        psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J a b)
      rw [BR_smul])
    (fun a => smul_neg_tup X g a)
    (fun Φ hΦc hΦs => ⟨hΦc.comp e.continuous, hΦs.comp_homeomorph e⟩) hμ

def SdTestI : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ Φ : TupI X → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
      Integrable (fun y => ∫ x, Φ x * psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) ∂μinf) μinf ∧
      ∃ z, Φ (-z) ≠ 0

private theorem eq_one_of_selfDual_smul {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (c : ENNReal) (hctop : c ≠ ⊤) (χ : V → V → ℂ) (hμ : SelfDual μ χ)
    (hν : SelfDual (c • μ) χ) (Φ : V → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ)
    (hi : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ) (z : V) (hz : Φ (-z) ≠ 0) : c = 1 := by
  have hin : ∀ y, ∫ x, Φ x * χ x y ∂(c • μ) = (c.toReal : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [integral_smul_measure, Complex.real_smul]
  have hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp only [hin]
    exact (hi.const_mul _).smul_measure hctop
  have key := hν.2 Φ hc hs hi' z
  simp only [hin] at key
  rw [integral_smul_measure, Complex.real_smul] at key
  simp only [mul_assoc] at key
  rw [integral_const_mul, hμ.2 Φ hc hs hi z] at key
  have h2 : ((c.toReal : ℂ) * c.toReal - 1) * Φ (-z) = 0 := by linear_combination key
  have h3 : (c.toReal : ℂ) * c.toReal = 1 := by
    have h3' := (mul_eq_zero.mp h2).resolve_right hz
    linear_combination h3'
  have h4 : c.toReal * c.toReal = 1 := by exact_mod_cast h3
  have h5 : c.toReal = 1 := by
    rcases mul_self_eq_one_iff.mp h4 with h | h
    · exact h
    · linarith [ENNReal.toReal_nonneg (a := c)]
  first
  | exact (ENNReal.toReal_eq_one_iff c).mp h5
  | rw [← ENNReal.ofReal_toReal hctop, h5, ENNReal.ofReal_one]

theorem sdInvG_of (hT : SdTestI) : SdInvG := by
  unfold SdInvG
  intro D X u' ψ hT' μinf νinf fibInf hP g
  have hμ : SelfDual μinf
      (fun X' Y' : TupI X => psiInf X.B.I.F ψ (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J X' Y')) :=
    hP.2.2.2.2.1
  obtain ⟨Φ, hΦc, hΦs, hΦi, z, hz⟩ := hT X u' ψ hT' μinf νinf fibInf hP
  have hν := selfDual_map X ψ μinf hμ g
  haveI := hμ.1
  haveI := hν.1
  obtain ⟨c, hctop, hc⟩ : ∃ c : ENNReal, c ≠ ⊤ ∧ μinf.map (fun y => g • y) = c • μinf := by
    refine ⟨(Measure.addHaarScalarFactor (μinf.map fun y => g • y) μinf : ENNReal), ENNReal.coe_ne_top,
      (Measure.isAddLeftInvariant_eq_smul (μinf.map fun y => g • y) μinf).trans ?_⟩
    ext s _
    simp [Measure.smul_apply]
  rw [hc] at hν
  rw [hc]
  have hc1 : c = 1 :=
    eq_one_of_selfDual_smul μinf c hctop _ hμ hν Φ hΦc hΦs hΦi z hz
  rw [hc1, one_smul]

end PI.AprimeInfW
end
end

