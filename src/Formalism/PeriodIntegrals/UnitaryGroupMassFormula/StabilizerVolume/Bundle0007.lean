module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.VolStabFromSWS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0001
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibInf
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW PI.AdicCompletionValuation

theorem densFibInf_holds : DensFibInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ μinf hμ νinf hν fibInf hfib Φ g
    hΦc hΦs hg
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have hD : {S : HermR (Ainf F) σ a | IsUnit (S : Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)).det} ∈
      𝓝 (hermOf (Ainf F) σ (gramE σ J X0) hT) :=
    (isOpen_unitHerm (Ainf F) (isOpen_units_Ainf F) σ a).mem_nhds
      (isUnit_det_hermOf (Ainf F) σ _ hT hdet)
  exact DensGen.densGen (f' := gramH (Ainf F) σ hσ J hJ.1) hfib
    (continuous_gramH (Ainf F) σ hσ J hJ.1) (fun _ => rfl) Subtype.val_injective
    (fun v hv => linIndep_of_isUnit_det (Ainf F) σ J v hv) hΦc hΦs hg Filter.univ_mem hD hD

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
section
noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation

section Local

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem countable_numberField : Countable F :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

theorem separableSpace_Fv : TopologicalSpace.SeparableSpace (Fv F v) := by
  haveI := countable_numberField F
  exact ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
    HeightOneSpectrum.denseRange_algebraMap F v⟩⟩

theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  haveI := separableSpace_Fv F v
  exact UniformSpace.secondCountable_of_separable (Fv F v)

theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) := by
  have hK := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers (F := F) (v := v)
  have hN : (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∈ 𝓝 (0 : v.adicCompletion F) := by
    exact (Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers F).zero_mem
  exact hK.locallyCompactSpace_of_mem_nhds_of_addGroup hN

theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  have h : {r : Fv F v | IsUnit r} = {0}ᶜ := by
    ext r
    simp [isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton

end Local

theorem densFibV_holds : DensFibV := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet ψ _ v μv hμv νv hνv fibV hfib Φv gv
    hSB hdens
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have := hμv.1
  have := hνv.1
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have hN := isOpen_unitHerm (Fv F v) (isOpen_units_Fv F v) σ a
  exact DensGen.densGen (B := Set.univ) hfib (continuous_gramH (Fv F v) σ hσ J hJ.1)
    (fun X => rfl) Subtype.val_injective
    (fun X hX => linIndep_of_isUnit_det (Fv F v) σ J X hX)
    hSB.1.continuous hSB.2 hdens Filter.univ_mem
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))
    (hN.mem_nhds (isUnit_det_hermOf (Fv F v) σ _ hT hdet))

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExChar
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem exChar_holds : ExChar := by
  intro F E _ _ _ _ _ σ hE M J _hJ _ha hc a _ha1 ha2 _X0 _hT _hdet
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  have h0 : 2 * 0 < M := by omega
  have hrd : RapidDecay b (fun _ : Fin 0 → Fin M → Ainf F ⊗[F] E => (1 : ℂ)) :=
    fun N => ⟨1, fun X => by simp [sizeTup]⟩
  have hpf : IsPureFin b (fun _ : Fin 0 → Fin M → Af F ⊗[F] E => (1 : ℂ))
      (fun v (_ : Fin 0 → Fin M → Fv F v ⊗[F] E) => (1 : ℂ)) := by
    refine ⟨fun v => ⟨IsLocallyConstant.const 1, ?_⟩, Filter.Eventually.of_forall fun v => ?_,
      fun X => by simp⟩
    · exact (Set.subsingleton_of_subsingleton).isCompact
    · funext X
      simp [latV, Set.indicator]
  have hS := hc 0 h0 (0 : Matrix (Fin 0) (Fin 0) E) (fun i => Fin.elim0 i) (by simp)
    (Module.finrank F E) b (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => 1)
    continuous_const hrd (Formalism.L2.SG.Pf.NcWeil.isSmoothCc_empty _) hpf (fun _ => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  exact ((hS.2 μ hμ).2 𝓕 h𝓕).1

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStab
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)

theorem exFDStab_of (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩

theorem discHF_of_discHA (h : PI.VolSemiDirect.W.DiscHA) : DiscHF := by
  intro F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _
  exact (h F E σ hE M J hJ).2

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

section Abstract

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [MulAction G X] [TopologicalSpace X] [MeasurableSpace X]

theorem orb_mk (x0 : X) (k : G) :
    ((k : G ⧸ MulAction.stabilizer G x0)).out • x0 = k • x0 := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (MulAction.stabilizer G x0) k
  rw [hh, mul_smul, (MulAction.mem_stabilizer_iff.1 h.2)]

theorem orb_smul (x0 : X) (g : G) (q : G ⧸ MulAction.stabilizer G x0) :
    (g • q).out • x0 = g • (q.out • x0) := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  have : g • ((q.out : G) : G ⧸ MulAction.stabilizer G x0) =
      ((g * q.out : G) : G ⧸ MulAction.stabilizer G x0) := rfl
  rw [this, orb_mk, mul_smul]

end Abstract

def SecCtblG : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def OrbTup : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ y : Fin a → Fin M → AF F ⊗[F] E, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) →
    ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y

def StabClosed : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  IsClosed ((stabT (AF F) σ J X0 : Subgroup (HA (AF F) σ J)) : Set (HA (AF F) σ J))

def NuInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ (g : HA (AF F) σ J) (s : Set (Fin a → Fin M → AF F ⊗[F] E)), MeasurableSet s →
      νX ((fun y => g • y) ⁻¹' s) = νX s

def NuFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → νX K < ⊤

def NuNeZero : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX → νX ≠ 0

def OrbEmb : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  MeasurableEmbedding (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0) ∧
    Continuous (fun q : HA (AF F) σ J ⧸ stabT (AF F) σ J X0 => q.out • ratTup (F := F) (AF F) X0)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibOfTens
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def DensAll {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) :
    Prop :=
  ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∃ g : X → ℝ, Continuous g ∧ ∀ S : Set X, IsCompact S →
      ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν

def FibOfDens : Prop :=
  ∀ (V X Y : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V]
    [T2Space V] [SecondCountableTopology V] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] (μ : Measure V) (ν : Measure X),
    IsFiniteMeasureOnCompacts μ → IsFiniteMeasureOnCompacts ν → ν.IsOpenPosMeasure →
    ∀ (f : V → Y) (ι : X → Y) (U : Set V), Continuous f → IsClosedEmbedding ι →
      (∀ v, f v ∈ Set.range ι) → IsOpen U → DensAll μ f ι ν U →
      ∃ fib : X → Measure V, IsFibreFamily μ f ι U ν Set.univ fib

def TensFacts (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : Prop :=
  LocallyCompactSpace (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧
    IsClosed (HermR R σ a : Set (Matrix (Fin a) (Fin a) (R ⊗[F] E))) ∧
    Continuous (gramR R σ J (n := a)) ∧ (∀ X, gramR R σ J (n := a) X ∈ HermR R σ a) ∧
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}

def TensAll : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  TensFacts F E σ M J a (Ainf F) ∧ ∀ v : HeightOneSpectrum (𝓞 F), TensFacts F E σ M J a (Fv F v)

def DensInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
      DensAll μinf (gramR (Ainf F) σ J) Subtype.val νinf
        {X | LinearIndependent (Ainf F ⊗[F] E) X}

def DensV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensAll μv (gramR (Fv F v) σ J) Subtype.val νv {X | LinearIndependent (Fv F v ⊗[F] E) X}

theorem fib_of_tens {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {a : ℕ} {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] (hG : FibOfDens) (hT : TensFacts F E σ M J a R)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hD : DensAll μ (gramR R σ J) Subtype.val ν {X | LinearIndependent (R ⊗[F] E) X}) :
    ∃ fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E),
      IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
        Set.univ fib := by
  obtain ⟨hLC, hT2, hSC, hCl, hCont, hMem, hOpen⟩ := hT
  haveI := hLC
  haveI := hT2
  haveI := hSC
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  haveI : SecondCountableTopology (HermR R σ a) := by
    first
      | infer_instance
      | exact hCl.isClosedEmbedding_subtypeVal.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.isEmbedding.isInducing.secondCountableTopology
      | exact hCl.isClosedEmbedding_subtypeVal.toIsEmbedding.toIsInducing.secondCountableTopology
  haveI : BorelSpace (HermR R σ a) := by
    first
      | infer_instance
      | exact ⟨rfl⟩
  haveI : LocallyCompactSpace (HermR R σ a) := hCl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact hG _ _ _ μ ν inferInstance inferInstance inferInstance (gramR R σ J) Subtype.val _ hCont
    hCl.isClosedEmbedding_subtypeVal (fun v => ⟨⟨_, hMem v⟩, rfl⟩) hOpen hD

theorem fibInfEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensInf) : FibInfEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν
  exact fib_of_tens hG (hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).1 μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ μ hμ ν hν)

theorem fibVEx_of (hG : FibOfDens) (hT : TensAll) (hD : DensV) : FibVEx := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν
  exact fib_of_tens hG ((hT F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet).2 v) μ ν hμ.1 hν.1
    (hD F E σ hCM M J hJ h1 h2 a ha haM X0 hX0 hdet ψ hψ v μ hμ ν hν)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InvInvSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def InvInv : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  (∀ μ, IsHaarH F E σ M J μ → μ.IsInvInvariant) ∧
    ∀ ψ, IsCharAF F ψ → ∀ μ, IsHaarH F E σ M J μ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
      ∀ μ' : Measure (stabT (AF F) σ J X0), μ'.IsHaarMeasure → IsCompatT F E σ M J X0 μ μ' νX →
        μ'.IsInvInvariant

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasOrbSt
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def MeasOrb : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ, IsAdm F E Φ →
    Measurable fun g : HA (AF F) σ J => Φ (g • ratTup (AF F) X0)

def MeasGrp : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a _X0 _hT =>
  MeasurableMul (HA (AF F) σ J) ∧ MeasurableInv (HA (AF F) σ J)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SWeqOm
section
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Decay

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem continuous_sizeInf {d : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem continuous_sizeTup {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Continuous (sizeTup (M := M) (n := n) b) := by
  unfold sizeTup
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i _ => ?_
  exact (continuous_sizeInf b).comp ((continuous_apply i).comp (continuous_apply a))

theorem rapidDecay_of_compact {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    RapidDecay b Φ := by
  intro N
  have hcont : Continuous fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    (continuous_norm.comp hc).mul ((continuous_const.add (continuous_sizeTup b)).pow N)
  have hsupp : HasCompactSupport fun X => ‖Φ X‖ * (1 + sizeTup b X) ^ N :=
    hs.norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨C, fun X => le_trans (le_abs_self _) (by simpa only [Real.norm_eq_abs] using hC X)⟩

end Decay

theorem sWeqOm_of (h1 : DensFibInf) (h2 : DensFibV) : SWeqOm := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν Φ hΦ
  obtain ⟨d, b, Φinf, Φf, Φv, hci, hsi, hpf, hpr, hsm⟩ := hΦ
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b Φ Φinf Φf Φv hci
    (rapidDecay_of_compact b Φinf hci hsi) hsm hpf hpr
  obtain ⟨_, hν2⟩ := hν
  obtain ⟨μinf, hμinf⟩ := hν2.1
  have hν3 := hν2.2 μinf hμinf
  obtain ⟨νinf, hνinf⟩ := hν3.1
  have hν4 := hν3.2 νinf hνinf
  obtain ⟨μv, hμv⟩ := hν4.1
  have hν5 := hν4.2 μv hμv
  obtain ⟨νv, hνv⟩ := hν5.1
  have hν6 := hν5.2 νv hνv
  obtain ⟨fibInf, hfibInf⟩ := hν6.1
  have hν7 := hν6.2 fibInf hfibInf
  obtain ⟨fibV, hfibV⟩ := hν7.1
  have hν8 := hν7.2 fibV hfibV d b Φ Φinf Φf Φv hci hsi hpf hpr
  obtain ⟨ginf, gv, hdi, hdv, _, hmean⟩ :=
    (((((((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ).2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv)
  have hmean' : meanC μ 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = gramE σ J X0}) =
      ginf (hermOf (Ainf F) σ (gramE σ J X0) hT) *
        ∏' v, gv v (hermOf (Fv F v) σ (gramE σ J X0) hT) := hmean
  rw [hmean', hν8.2.2, h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
    fibInf hfibInf Φinf ginf hci hsi hdi]
  congr 1
  exact tprod_congr fun v => h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfibV v) (Φv v) (gv v) (hpf.1 v) (hdv v)

end PI.VolStabS
end
end

