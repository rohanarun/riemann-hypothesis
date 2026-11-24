module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AtPtRel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
attribute [-instance] PI.WSF.instMeasurableSpaceMat PI.WSF.instBorelSpaceMat
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.FdegGap

def plusFirst {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem plusFirst_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (plusFirst ε (Sum.inl i)) = true := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {a // ε a = true}).symm i).2

theorem plusFirst_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (plusFirst ε (Sum.inr j)) = false := by
  simp only [plusFirst, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

theorem muCD_eq_scaled (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal)
    (hc : ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)})
    {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (sc N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA]
  exact (hc N ε _ _ (plusFirst ε) (plusFirst_inl ε) (plusFirst_inr ε) A hA).symm

theorem one_le_p {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = true) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem one_le_q {N : ℕ} {ε : Fin N → Bool} (h : ∃ a, ε a = false) : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε := by
  obtain ⟨a, ha⟩ := h
  exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

theorem thrStar_eq {N : ℕ} (ε : Fin N → Bool) : ReciprocityTheory.ChartRestriction.DS.thrStar ε = Formalism.MainNotions.GapDS.thrE ε := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS
  rfl

theorem fdeg_gap : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) := by
  intro cd sc hc N ε lam h hlam hp hq hgap hh H _ _ σ hσ
  haveI : CompleteSpace H := hσ.1
  haveI : Nontrivial H := hσ.2.1
  have hCD := muCD_eq_scaled cd sc hc ε
  have hp1 := one_le_p hp
  have hq1 := one_le_q hq
  have hh' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by rw [thrStar_eq]; exact hh
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp1 hq1
  have h8 : 8 * (N : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have hm : 16 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ))
        ≤ ReciprocityTheory.ChartRestriction.DS.thrStar ε := le_max_right _ _
    have h0 : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    have hs : (0 : ℝ) ≤ Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    nlinarith
  have hΨ : ∀ μ : Fin N → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin N) (Fin N) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hμg
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor N ε μ h T m hμ hm hμg hq0 h8).1⟩
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdim : fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ w = ReciprocityTheory.ChartRestriction.DS.dimVlam lam :=
    ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp1 hq1 hlam hgap hh' hΨ hσ hw
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ hσ
  have hpos : (0 : ℝ) < (sc N ε : ℝ) := by
    rcases (sc N ε).coe_nonneg.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      haveI := ReciprocityTheory.ChartRestriction.DS.muCD_isHaar ε
      have hz : sc N ε = 0 := by exact_mod_cast heq.symm
      have hne := (isOpen_univ (X := Formalism.REAL.UJ ε)).measure_ne_zero (ReciprocityTheory.ChartRestriction.DS.muCD ε) Set.univ_nonempty
      rw [hCD, hz] at hne
      simp at hne
  have hsc : IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (d / (sc N ε : ℝ)) := by
    have := ReciprocityTheory.ChartRestriction.DS.isFdeg_smul hpos hd
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hval : d / (sc N ε : ℝ) = Formalism.QuantumDeterminants.fdegHC lam := by
    have h1 := ReciprocityTheory.ChartRestriction.DS.fdegOf_of_isFdeg' (hCD ▸ hsc) hw
    rw [h1] at hdim
    rw [hdim, ReciprocityTheory.ChartRestriction.DS.dimVlam_eq_vand hlam.1, Formalism.MainNotions.BridgeLemma.szh_fdegHC lam hlam.1]
    rfl
  rwa [hval] at hsc

end GlobalTheory.FdegGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFramePairsDifferIsometryUnitriangular
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocOver.WittFrames

theorem zhatOM_injective {K : Type*} [CommRing K] {r : ℕ} {Z Z' : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (h : ZhatOM Z = ZhatOM Z') : Z = Z' := by
  ext a b
  have h1 := congrFun (congrFun h a) b
  simp only [ZhatOM] at h1
  exact ((isUnit_one.neg).pow (r - b.val)).mul_left_cancel h1

theorem tri_symm {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (h : Tri E f g) : Tri E g f := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA1 i j hij
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [hA2]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  obtain ⟨hB1, hB2⟩ := inv_unitri A hA1 hA2
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A⁻¹, ⟨hB1, hB2⟩, fun b => ?_⟩
  show f b = ∑ a, A⁻¹ a b • g a
  have hm := Matrix.mul_nonsing_inv A hu
  simp_rw [hc', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ c, ∑ a, (A⁻¹ a b * A c a) • f c = (A * A⁻¹) c b • f c := by
    intro c
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  simp_rw [this, hm, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp

theorem tri_map {E W : Type} [Field E] [AddCommGroup W] [Module E W] {n : ℕ} {f g : Fin n → W}
    (γ : W →ₗ[E] W) (h : Tri E f g) : Tri E (fun a => γ (f a)) (fun a => γ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  have hc' : ∀ b, g b = ∑ a, A a b • f a := hc
  refine ⟨A, hA, fun b => ?_⟩
  show γ (g b) = ∑ a, A a b • γ (f a)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc' b, map_sum]
  simp [map_smul]

theorem exists_isom_of_gram (hW : PI.WittExtension) {K V : Type} [Field K] [StarRing K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (hs : ∀ x y, star (B x y) = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0)
    {ι : Type} (v v' : ι → V) (hv : LinearIndependent K v) (hv' : LinearIndependent K v')
    (hg : ∀ i j, B (v i) (v j) = B (v' i) (v' j)) :
    ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ i, g (v i) = v' i := by
  let U := Submodule.span K (Set.range v)
  let bU : Module.Basis ι K U := Module.Basis.span hv
  have hbU : ∀ i, (bU i : V) = v i := fun i => congrArg Subtype.val (Module.Basis.span_apply hv i)
  let f : U →ₗ[K] V := bU.constr K v'
  have hf : ∀ i, f (bU i) = v' i := fun i => by simp [f, Module.Basis.constr_basis]
  have hfe : f = Finsupp.linearCombination K v' ∘ₗ bU.repr.toLinearMap := by
    refine bU.ext (fun i => ?_)
    rw [hf]; simp
  have hinj : Function.Injective f := by
    rw [hfe, LinearMap.coe_comp]
    exact Function.Injective.comp hv' bU.repr.injective
  have hiso : ∀ x y : U, B (f x) (f y) = B x y := by
    have : (B.comp f).compl₂ f = (B.comp U.subtype).compl₂ U.subtype := by
      refine LinearMap.ext_basis bU bU (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, hf, hbU]
      exact (hg i j).symm
    intro x y
    have := LinearMap.congr_fun₂ this x y
    simpa using this
  obtain ⟨g, hg1, hg2⟩ := hW K V B hs hn U f hinj hiso
  exact ⟨g, hg1, fun i => by rw [← hbU i, hg2, hf]⟩

end GlobalTheory.LocOver.WittFrames

namespace GlobalTheory.LocOver


open GlobalTheory.LocOver.WittFrames Formalism.L2.SG.GramJoint in
theorem witt_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F F00 : LFlag (D.sp.Y 0) D.R.rS T)
    (F' F'0 : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → Gval F F' ≠ 0 →
    IsInCell (ZhatOM (ZhatL F F')) w → ZhatOM (ZhatL F00 F'0) = ptMat w →
    Gval F00 F'0 = Gval F F' ∧ ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT,
      Tri D.host.E (frame F00) (fun a => γ (frame F a)) ∧ Tri D.host.E (frame F'0) (fun a => γ (frame F' a)) := by
  intro D T T' F F00 F' F'0 w hT hT' hG hcell hpt
  obtain ⟨⟨Fb, Fb', h1, h2, hb⟩, hall⟩ := _root_.GlobalTheory.LocOver.base_frames_at_point D F F' w hT hT' hcell
  have hGb : Gval Fb Fb' = Gval F F' := (hall Fb Fb' h1 h2).2
  have hZ : ZhatL Fb Fb' = ZhatL F00 F'0 := zhatOM_injective (hb.trans hpt.symm)
  have hG0 : Gval F00 F'0 = Gval Fb Fb' := by
    show Gmat (Zhat F00.fl F'0.fl) T T' = Gmat (Zhat Fb.fl Fb'.fl) T T'
    exact congrArg (fun Z => Gmat Z T T') hZ.symm
  refine ⟨hG0.trans hGb, ?_⟩
  have hGb0 : Gflag Fb.fl Fb'.fl ≠ 0 := by rw [← hGb] at hG; exact hG
  have hG00 : Gflag F00.fl F'0.fl ≠ 0 := by
    have := hG0.trans hGb; rw [← this] at hG; exact hG
  have hli := (gramIndep D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl hGb0).1
  have hli' := (gramIndep D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl hG00).1
  have hgram : ∀ i j, (VS D).hT (pairVec Fb.fl Fb'.fl i) (pairVec Fb.fl Fb'.fl j) =
      (VS D).hT (pairVec F00.fl F'0.fl i) (pairVec F00.fl F'0.fl j) := by
    intro i j
    have e := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' Fb.fl Fb'.fl) i) j
    have e' := congrFun (congrFun (gramBlocks D.host.E (VS D) D.R.rS T T' F00.fl F'0.fl) i) j
    have hZ' : Zhat Fb.fl Fb'.fl = Zhat F00.fl F'0.fl := hZ
    rw [hZ'] at e
    exact e.trans e'.symm
  have hs : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hn : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨γ, hγ, hγv⟩ := exists_isom_of_gram witt_extension_theorem (VS D).hT hs hn _ _ hli hli' hgram
  refine ⟨γ, fun x y => hγ x y, ?_, ?_⟩
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h1
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb a)) = frame F00 :=
      funext fun a => hγv (Sum.inl a)
    rw [e] at this
    exact tri_symm this
  · have := tri_map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) h2
    have e : (fun a => (γ : (VS D).V →ₗ[D.host.E] (VS D).V) (frame Fb' a)) = frame F'0 :=
      funext fun a => hγv (Sum.inr a)
    rw [e] at this
    exact tri_symm this

end GlobalTheory.LocOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFrames
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.BasePt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frame_castSucc {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (i : Fin D.R.rS) :
    frame F i.castSucc = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem tri_of_adapt {T : D.host.E} (g : GV D) (F G : LFlag (D.sp.Y 0) D.R.rS T) (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (h : ∀ a : Fin (D.R.rS + 1), g (frame F a) - frame G a ∈ Xflag G a.val) :
    GlobalTheory.LocOver.Tri D.host.E (frame G) (frame (Formalism.L2.SG.Saturated.mapL g hg F)) := by
  have ex : ∀ b : Fin (D.R.rS + 1), ∃ l : Fin D.R.rS →₀ D.host.E,
      l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.val < b.val} ∧
        Finsupp.linearCombination D.host.E G.fl.e l = g (frame F b) - frame G b := fun b =>
    (Finsupp.mem_span_image_iff_linearCombination D.host.E).1 (h b)
  choose l hl hx using ex
  have hz : ∀ b (i : Fin D.R.rS), ¬ i.val < b.val → l b i = 0 := fun b i hi =>
    (Finsupp.mem_supported' D.host.E (l b)).1 (hl b) i hi
  refine ⟨fun a b => (if a = b then 1 else 0) + (if h : a.val < D.R.rS then l b ⟨a.val, h⟩ else 0), ⟨?_, ?_⟩, ?_⟩
  · intro a b hba
    dsimp only
    rw [if_neg (ne_of_gt hba), zero_add]
    split_ifs with h'
    · exact hz b _ (by show ¬ a.val < b.val; have := Fin.lt_def.1 hba; omega)
    · rfl
  · intro a
    dsimp only
    rw [if_pos rfl]
    split_ifs with h'
    · rw [hz a _ (by simp), add_zero]
    · rw [add_zero]
  · intro b
    rw [Formalism.L2.SG.Saturated.frame_mapL]
    simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true,
      zero_smul, add_zero, frame_castSucc, Fin.eta]
    have e := hx b
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
    rw [e]
    abel

theorem term_at_base_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 →
      ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → t.G ≠ 0 ∧ ptPN t = toPts w := by
  intro D X Y u u' F F' w hZ hG t Λ hTG
  obtain ⟨g, ⟨hg, h1⟩, ⟨-, h2⟩, -⟩ := hTG
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u').A.T_prime.ne_zero
  have hcell : IsInCell (ZhatOM (ZhatL F F')) w := by
    refine ⟨1, 1, fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_lt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩,
      fun i j => ⟨fun hij => Matrix.one_apply_ne (ne_of_gt hij), fun hij => by subst hij; exact Matrix.one_apply_eq i⟩, ?_⟩
    rw [hZ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨-, hB⟩ := _root_.GlobalTheory.LocOver.base_frames_at_point D F F' w hT hT' hcell
  obtain ⟨hcell2, hG2⟩ := hB _ _ (tri_of_adapt g (lf D (X.Fu u)) F hg h1) (tri_of_adapt g t.frame F' hg h2)
  replace hcell2 : IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) t.frame)) w :=
    (congrArg (fun Z => IsInCell (ZhatOM Z) w) (Formalism.L2.SG.Saturated.zhat_mapL g hg (lf D (X.Fu u)) t.frame)).mp hcell2
  replace hG2 : Gval (lf D (X.Fu u)) t.frame = Gval F F' :=
    (Formalism.L2.SG.Saturated.gval_mapL g hg (lf D (X.Fu u)) t.frame).symm.trans hG2
  have hGt : t.G ≠ 0 := by rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, hG2]; exact hG
  have hat : t.toTerm.atPt w := ⟨t.frame, ⟨t.rep.2.2.2.2, rfl⟩, fun h0 => hG (hG2.symm.trans h0), hcell2⟩
  have hrel : t.toTerm.relevant := Formalism.L2.SG.Pf.FinXP.atPtRelevant_holds D u u' _ _ t.toTerm w hat
  have hsp := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm ⟨w, hat, hrel⟩
  have heq := Formalism.L2.SG.Pf.cellPtUnique_of Formalism.L2.SG.Pf.cell_point_uniqueness
    (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u) t.toTerm _ _ hsp hat
  exact ⟨hGt, by show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = toPts w; rw [heq]⟩

end GlobalTheory.Unfold.BasePt
end
end

