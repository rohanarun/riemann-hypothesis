module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairTiesPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.FinLevi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0040

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsCountBase
section
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsCountBase

open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

open Formalism.MainNotions.BridgeLemma NumberField in
theorem splits_X (k : Fin 2) : SplitsCompl X.B.I.E (D.host.g k) := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  exact Formalism.L2.SG.ThmSOwn.splitsCompl_of_equiv X.ιE hspl

theorem hc_X (hT : AutTie D X.B X.pl) (v : NumberField.InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  exact Inh.aut_isHCParam_of_autTie hT v

theorem countBase_of (hT : AutTie D X.B X.pl) {large₂ : SizeData₂ D} {n0 : ℕ} {A C cb : ℝ}
    (hp : AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n0 A C cb) (hg1 : 4 * D.R.r < D.host.g 1) : CountBase X n0 A C cb := by
  obtain ⟨-, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, p12⟩ := hp
  have hn := hT.n_eq
  have hf := hT.f_eq
  have hrd := hT.rd_eq
  have tg := X.g_eq
  have hq : ∀ v, X.B.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.B.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := hT.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  refine ⟨large₂.sc.b, C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE), fun k => ?_,
    fun v a c hac => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, hc_X X hT, ?_, ?_, ?_, D.host.g_prime _, ?_, splits_X X _⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [hrd, hn]; exact p4
    · intro v a
      rw [hT.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [hn]
      fin_cases k
      · exact hg1
      · exact p7
  · rw [hT.lam_eq v a, hT.lam_eq v c]
    exact p9 _ _ _ (by rw [← hT.eps_eq v a, ← hT.eps_eq v c]; exact hac)
  · rw [hn, hf, hrd]
  · rw [hf, hn]; exact p10
  · rw [hf, hn]; exact p12
  · have h := Formalism.MainNotions.BridgeLemma.Dstar_pos D
    rw [hT.Dstar_eq] at h
    exact h

section Fam

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData Formalism.L2.SG.ThmSOwn

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.L2.SG.Pf.AllRowsCountBase
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL
noncomputable section

namespace Formalism.L2.SG.Pf.DstarVolPf

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.Theta
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def frOf : Formalism.IndefR.Eqv.UI.Frames D (VS D) where
  ε := fun _ => Formalism.L2.SG.InstExistsPf.epsV D
  P := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose
  unit := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.1
  spec := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.2
  Λ := Formalism.L2.SG.InstExistsPf.Lv D
  Λ_fg := Formalism.L2.SG.InstExistsPf.L_fg D
  Λ_span := Formalism.L2.SG.InstExistsPf.L_span D
  Λ_dual := Formalism.L2.SG.InstExistsPf.L_dual D

theorem instOf_eq : Formalism.L2.SG.InstExistsPf.instOf D = Formalism.IndefR.Eqv.UI.instV (frOf D) := rfl

theorem lv_eq : (frOf D).Λ = Formalism.IndefR.Eqv.UI.Lv D (VS D) := rfl

abbrev IV : Formalism.MainNotions.S.AutInst := Formalism.IndefR.Eqv.UI.instV (frOf D)

def cdProdI : ENNReal := ∏ v : InfinitePlace D.host.F, (D.s.cdScale (VS D).rank ((frOf D).ε v) : ENNReal)

def muVI (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [SigmaFinite μf] : Measure (GA D (VS D)) :=
  cdProdI D • ((Formalism.IndefR.Eqv.UI.instV (frOf D)).muA μf).map (Formalism.IndefR.Eqv.UI.brg (frOf D))

def VolMeasOf : Prop :=
  ∀ (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    μf (Formalism.IndefR.Eqv.UI.instV (frOf D)).Kset = 1 →
    IsVolMeas D (VS D) (D.R.k + D.R.rS) (D.R.rS + 1) (muVI D μf)

theorem volMeasOf_of (hcd : cdScaleTie D) : VolMeasOf D := by
  intro μf _ _ hK
  have h1 : ∀ (v : InfinitePlace D.host.F) (i : Fin (D.R.k + D.R.rS)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i)) = true := fun v i => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 : ∀ (v : InfinitePlace D.host.F) (j : Fin (D.R.rS + 1)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j)) = false := fun v j => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  exact Formalism.L2.S.S7.ZsCovMeas.isVolMeas_muV (frOf D) hcd (lv_eq D) (fun _ => (Formalism.L2.SG.InstExistsPf.eSgn D).symm)
    h1 h2 (fun v => (D.s.cdScale_pos _ _).ne') μf hK

theorem cdScale_cast {n m : ℕ} (h : n = m) (ε : Fin n → Bool) :
    D.s.cdScale n ε = D.s.cdScale m (fun i => ε (Fin.cast h.symm i)) := by
  subst h; rfl

theorem cdScale_epsV :
    D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) = D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) := by
  rw [cdScale_cast D ((Formalism.L2.SG.InstExistsPf.rank_eq D).trans (dimS_eq D.R).symm)]
  rfl

section Gen

variable {I : Formalism.MainNotions.S.AutInst} (hb : AdBridgeIso I)

theorem mem_rr_iff' (x : I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF I ↔ toHA I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds I (toHA I hb) (toHA_isBridge I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J,
      h ∈ ratHA I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA I hb).injective hyx]

theorem isFD_image (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ν : Measure (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))
    (hν : ν ≪ (I.muA μf).map (toHA I hb)) :
    IsFundamentalDomain (HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) (toHA I hb '' fund) ν := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : (I.muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' I μf
  haveI : (I.muA μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund (I.muA μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
  let e := (toHA I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF I :=
    { toFun := fun g => ⟨(toHA I hb).symm (g : HA _ _ _), (mem_rr_iff' hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA I hb x, (mem_rr_iff' hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((I.muA μf).map e) (I.muA μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' fund) ((I.muA μf).map e) := by
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : I.GA) * x) = (g : HA _ _ _) * e x
    show toHA I hb ((toHA I hb).symm g * x) = (g : HA _ _ _) * toHA I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  exact hfd.mono hν

end Gen

theorem covol_gen (hVM : VolMeasOf D) (hVol : VolTie D) (I : Formalism.MainNotions.S.AutInst)
    (hI : I = Formalism.IndefR.Eqv.UI.instV (frOf D)) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hf : I.IsFundDom (I.muA μf) fund) :
    I.vol μf fund / (μf I.Kset).toReal *
      ∏ _v : InfinitePlace I.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = volY0 D := by
  subst hI
  have hKc : IsCompact (IV D).Kset := Formalism.L2.SG.Closed.AutKCompact_holds (IV D)
  have hKo : IsOpen (IV D).Kset := by
    have h := (IV D).topf_open 1 le_rfl
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨hx, fun y hy => ⟨_, Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv _ hx hy, by simp⟩⟩
    · intro hx
      exact hx.1
  have hpos : 0 < μf (IV D).Kset := hKo.measure_pos μf ⟨1, Formalism.L2.SG.Pf.unitaryCongruence.K_one _⟩
  have hfin : μf (IV D).Kset < ⊤ := hKc.measure_lt_top
  set c := μf (IV D).Kset with hc
  let μ' : Measure (IV D).Gf := c⁻¹ • μf
  haveI : μ'.IsHaarMeasure := Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos.ne')
  have hfs : ∀ n, μ' (spanningSets μf n) < ⊤ := fun n => by
    show (c⁻¹ • μf) _ < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hpos) (measure_spanningSets_lt_top μf n)
  haveI : SigmaFinite μ' :=
    ⟨⟨{ set := spanningSets μf, set_mem := fun _ => Set.mem_univ _, finite := hfs, spanning := iUnion_spanningSets μf }⟩⟩
  have hK1 : μ' (IV D).Kset = 1 := by
    show (c⁻¹ • μf) (IV D).Kset = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hpos.ne' hfin.ne]
  have hV := hVM μ' hK1
  have hsig : (VS D).SigOK := D.sp.Y_sig 0
  have hsv : ∀ τ, (VS D).sig τ = (D.R.k + D.R.rS, D.R.rS + 1) := fun τ => D.sp.baseSpace_signature_eq τ
  obtain ⟨-, hall⟩ := hVol (VS D) _ _ hsig hsv
  obtain ⟨-, hfd⟩ := hall _ hV
  let hb : AdBridgeIso (IV D) := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (IV D)).1
  have hbrg : Formalism.IndefR.Eqv.UI.brg (frOf D) = toHA (IV D) hb := rfl
  have hμA : (IV D).muA μ' = c⁻¹ • (IV D).muA μf := by
    show (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod (c⁻¹ • μf) = c⁻¹ • (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod μf
    exact Measure.prod_smul_right _
  haveI : BorelSpace (HAd (IV D)) := ⟨rfl⟩
  have hν : muVI D μ' ≪ ((IV D).muA μf).map (toHA (IV D) hb) := by
    unfold muVI
    rw [hbrg, hμA, Measure.map_smul]
    · exact (Measure.smul_absolutelyContinuous).trans Measure.smul_absolutelyContinuous
    · exact (toHA (IV D) hb).continuous.measurable.aemeasurable
  have hFD := isFD_image hb μf fund hf (muVI D μ') hν
  have key : muVI D μ' (toHA (IV D) hb '' fund) = ENNReal.ofReal (D.vol (VS D)) := hfd _ hFD
  let e := (toHA (IV D) hb).toHomeomorph.toMeasurableEquiv
  have hmeas : Measurable (toHA (IV D) hb) := (toHA (IV D) hb).continuous.measurable
  have hS : MeasurableSet (toHA (IV D) hb '' fund) := (e.measurableSet_image).2 hf.1
  have hmap : muVI D μ' (toHA (IV D) hb '' fund) = cdProdI D * (c⁻¹ * (IV D).muA μf fund) := by
    unfold muVI
    rw [Measure.smul_apply, smul_eq_mul, hbrg, hμA]
    congr 1
    erw [Measure.map_apply hmeas hS]
    rw [Set.preimage_image_eq _ (toHA (IV D) hb).injective, Measure.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 200000 in
  have hA0 : (IV D).muA μf fund ≠ 0 := by
    haveI : ((IV D).muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' (IV D) μf
    haveI : ((IV D).muA μf).IsMulLeftInvariant := inferInstance
    have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF (IV D)) fund ((IV D).muA μf) :=
      Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
    exact hfd0.measure_ne_zero (NeZero.ne _)
  have hcd0 : cdProdI D ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa using (D.s.cdScale_pos _ _).ne'
  have hci0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin.ne
  replace key := hmap.symm.trans key
  have hAT : (IV D).muA μf fund ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.mul_top hci0, ENNReal.mul_top hcd0] at key
    exact ENNReal.ofReal_ne_top key.symm
  have hL0 : cdProdI D * (c⁻¹ * (IV D).muA μf fund) ≠ 0 := mul_ne_zero hcd0 (mul_ne_zero hci0 hA0)
  have hvpos : 0 < D.vol (VS D) := by
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at key
    exact hL0 key
  have hR := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_ofReal hvpos.le, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv] at hR
  have hcdR : (cdProdI D).toReal = ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) := by
    unfold cdProdI
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show ((D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) : ENNReal)).toReal = _
    rw [cdScale_epsV]
    rfl
  rw [hcdR] at hR
  show ((IV D).muA μf fund).toReal / c.toReal *
      ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = D.vol (VS D)
  rw [← hR]
  ring

section Record

variable {D}

theorem dstarVolV_of (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVolV X :=
  covol_gen D (volMeasOf_of D hcd) hVol X.B.I (h.trans (instOf_eq D)) X.B.μf X.B.fund X.B.fund_spec

theorem dstarVol_holds (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) (hT : dsigTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVol X :=
  Formalism.L2.SG.Pf.RowDictPf.dstarVol_of X hT (dstarVolV_of X h hVol hcd)

end Record

end Formalism.L2.SG.Pf.DstarVolPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
section
namespace Formalism.L2.SG.Pf

theorem iotaRowC_holds : FinXP.IotaRowC := fun _ _ Y _ _ s₁ s₂ hr =>
  Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ (congrArg (fun q => q.1.1) hr) (congrArg (fun q => q.2.1.1) hr)
    (congrArg (fun q => q.2.2) hr)

theorem pairTiesAll_holds : Formalism.L2.SG.TermTieOf.PairTiesAll := FinXP.pairTies_of iotaRowC_holds


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem finXC_of (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC :=
  FinXP.finX_holds hWu hRF Formalism.L2.SG.Pf.FinLeviPf.finLeviC_holds Formalism.L2.SG.Pf.KernelOfEmbedding.IotaKer_holds

end Formalism.L2.SG.Pf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.OOCoreHilbertSchmidt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_hilbertSchmidt_sq {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact inner_self_eq_norm_sq _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

variable {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word)

theorem hsNormSq_OOP_quot (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (w : Point D.host.E (D.R.rS + 1))
    (hw : ∃ γ, IsPtRep X u u' w γ) (hG : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) :
    Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) =
      ∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  have hF := hQ w hw hG
  rw [hsNormSq_eq_hilbertSchmidt_sq]
  simp only [hsNormSq_eq_hilbertSchmidt_sq]
  unfold Formalism.L2.SG.Pf.OOCore.OOP hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GXPos : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ γ, IsPtRep X u u' w γ) → ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

variable (Y : Formalism.L2.SG.Full.Full X) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

section GX

variable {D : D7} {X : HidaSetting D}

theorem frm_sc (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    frm X u sc v a = (((sc ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • frm X u 1 v a := by
  unfold frm famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem zx_rd (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    ZX X u u' D.host.rdE γ v a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * ZX X u u' 1 γ v a b := by
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = (D.host.rdE ^ (D.R.rS - (c : ℕ)))⁻¹ := by
    intro c
    have hc := c.isLt
    unfold rhoF
    have h1 := Real.rpow_intCast D.host.rdE (-((D.R.rS - (c : ℕ) : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast] at h1
    rw [← h1]
    congr 1
    push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hc)]
    ring
  rw [hρ a, hρ b]
  unfold ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_sc u D.host.rdE v a, frm_sc u' D.host.rdE v b, Matrix.mulVec_smul]
  unfold hJ
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  clear hρ
  push_cast
  ring

theorem gx_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ γ, IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    GX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) =
      Formalism.MainNotions.S.ThB.Gpt (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w) := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw]
    exact hw.choose_spec
  have hZ : ∀ a b, ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) a b =
      (-1 : ℂ) ^ (D.R.rS - b.val) * ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w) a b := by
    intro a b
    have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
    unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
    simp only [Matrix.map_apply] at h1
    rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
    have hs : ((-1 : ℂ) ^ (D.R.rS - b.val)) * (-1 : ℂ) ^ (D.R.rS - b.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [zx_rd, Formalism.L2.SG.Pf.RelPtR.ptMat_ptLoc τ w a b]
    have h2 : ZX X u u' 1 (gamW X u u' w) (vOf X τ) a b = (-1 : ℂ) ^ (D.R.rS - b.val) * embS D τ (ptMat w a b) := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2]
    ring
  have hD : ∀ l (hl : l ≤ D.R.rS + 1), Complex.normSq (Formalism.L2.SG.RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)) l) =
      Complex.normSq (leadMinor (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) l hl) := by
    intro l hl
    unfold Formalism.L2.SG.RealObj.Dl leadMinor
    rw [dite_eq_left hl]
    have hM : (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)).submatrix (Fin.castLE hl) (Fin.castLE hl) *
          Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE hl b).val)) := by
      ext i j
      simp [Matrix.mul_diagonal, hZ, mul_comm]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    simp [Complex.normSq_neg]
  unfold GX Gv Formalism.MainNotions.S.ThB.Gpt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hD (D.R.rS + 1) le_rfl, hD D.R.rS (Nat.le_succ _)]

theorem gxPos_holds (u u' : D.what₂.Word) : GXPos (X := X) u u' := by
  intro w hb hw v
  have hv : v = vOf X (X.pl v) := (X.pl.symm_apply_apply v).symm
  rw [hv, gx_eq u u' w hw (X.pl v)]
  exact hb.2 (X.pl v)

end GX

end Formalism.L2.SG.Pf.OOCoreHilbertSchmidt
end
end

