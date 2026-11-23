module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsAllTwistPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeIndexValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftNearOne
section
noncomputable section

namespace GlobalTheory.SeeSaw.BaseFrame

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix

theorem near_left {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hC : ∀ i j, v (C i j) ≤ 1) (hM : ∀ i j, v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : C - 1 = (C * M - 1) - C * (M - 1) := by rw [mul_sub, mul_one]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C) (N := M - 1)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hC i l)).trans_lt (hM l j)

theorem near_right {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, v (M i j) ≤ 1) (hC : ∀ i j, v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : M - 1 = (C * M - 1) - (C - 1) * M := by rw [_root_.sub_mul, one_mul]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C - 1) (N := M)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (hM l j)).trans_lt (hC i l)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem kMat_mul (P : HeightOneSpectrum (𝓞 E)) (g k : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    kMat P (g * k) f = kMat P k 1 * kMat P g f := by
  ext1 i j
  have e : ∀ l, kMat P k 1 i l = adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 i l) := fun l => by
    show adAt F P (Col2.pullV k (Pi.single l 1) i) = _
    unfold Col2.pullV
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [Matrix.mul_apply]
  simp only [e]
  unfold kMat Col2.pullV
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, map_sum]
  simp only [map_mul]

theorem kMat_one (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    kMat P (1 : GL (Fin n) (AfE F E)) f i j = algebraMap E _ (f (Pi.single j 1) i) := by
  unfold kMat Col2.pullV
  rw [inv_one, Units.val_one, Matrix.one_mulVec, adAt_inclE]

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem lift_near_one {y k k' : GL (Fin n) (AfE F E)} {p p₀ : DecoF E n ST SG Q} (h : IsPtOf hc (y * k) p) (h' : IsPtOf hc (y * k') p)
    (h₀ : IsPtOf hc k' p₀) (hN : p₀.deco.1.N = stdLat E n) (w : SG) (hk : bc (prV (E := E) (w.1.under (𝓞 F))) k = 1)
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : TopStep.IsLiftFr p₀.deco.1 w f) (i j : Fin n) :
    w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  have hl := TopStep.liftFr_spec p.deco.2 w
  have h1 := val_kMat_sub_lt h w hl
  have h2 := val_kMat_sub_lt h' w hl
  have h3 := val_kMat_sub_lt h₀ w hf
  have e1 : kMat w.1 (y * k) (p.deco.1.liftFr w) = kMat w.1 y (p.deco.1.liftFr w) := by
    ext1 a b
    exact ZeroMove.adAt_pullV_mul w.1 y hk _ a
  rw [e1] at h1
  rw [kMat_mul] at h2
  rw [← one_mul k', kMat_mul] at h3
  have hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) := fun x => by simp
  have i1 := val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k' (stdLat E n) (stdLat E n)) fun _ => Iff.rfl
  have i2 := val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)
  have h4 := near_right _ i2 (near_left _ i1 h1 h2) h3 i j
  rw [kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl] at h4
  rw [← valued_algebraMap, map_sub, apply_ite (algebraMap E _), map_one, map_zero]
  exact h4

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SeeSaw.BaseFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LivechartKernelVectorsRealPointsDetPowersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.livechart_kernelVectors_realPoints_detPowers : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → JetS I l Z R.ψ R.θ s → (∀ j, j ≤ B.R.m → (g.x j).Is) → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → (clsKL R g P r k tl s J A ι).Real := by
  first | exact @GlobalTheory.KJRealLive.clsKL_real | exact GlobalTheory.KJRealLive.clsKL_real | (intros; apply GlobalTheory.KJRealLive.clsKL_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
namespace GlobalTheory.LocMod

theorem pi_e_self {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  have h := p.ι_π 1
  rw [map_one, mul_one] at h
  rw [← h, p.π_ι]

theorem pi_eq_zero_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {e : AE D} (h : e * p.e = 0) : p.π e = 0 := by
  have := congrArg p.π h
  rwa [map_mul, pi_e_self, mul_one, map_zero] at this

theorem up_down_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := by
  unfold Place.up Place.down
  have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [hM]
  ext i j
  simp only [Matrix.map_apply, p.ι_π]

theorem ratDatum_factor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  intro D k _ _ _ _ p ψ hψ _hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd Ξ Ξ' Ξk hΞk hΞ' c hc f₀ f f' hf₀ hvac hf hf'
  obtain ⟨Φ, hΦSB, hΦrat, hθ⟩ := hf
  obtain ⟨Φ', hΦ'SB, hΦ'rat, hθ'⟩ := hf'
  obtain ⟨T', hT'⟩ := hθ'.1
  have hf'T : f' = T' Φ' := hθ'.2 T' hT'
  have horth : e * p.e = 0 := _root_.GlobalTheory.LocMod.OutsideOrth.mul_eq_zero D k p P PP e hPP hIdemAt hE
  have hstabp := _root_.GlobalTheory.AdForm.stdHom_map_splitIdem D S T p.e p.split
  have hθT' := _root_.GlobalTheory.LocMod.StdTheta.theta_placeModel_std D ψ hψ S T _ (e + p.e) hE' f₀ T' hf₀ hvac hT'
  have hsb := _root_.GlobalTheory.LocMod.Place.isSBHalf_tensorAt D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB
  have hmodel := _root_.GlobalTheory.LocMod.TensorModel.isModel_tensor D k p ψ S T Y Y' FS FT e horth Φ hΦSB.1 f₀ T' hT' hθT' hsb
  have hvacm := _root_.GlobalTheory.LocMod.TOneModel.isPlaceModel_tensorOne D k p ψ S T Y Y' FS FT e horth hstd hstabp f₀ T' hT'
    (fun Φ₁ h₁ => _root_.GlobalTheory.LocMod.Place.isSBHalf_tensorAt D k p S T Y Y' FS FT e horth hstd hstabp Φ₁ h₁ _ (GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'))
  have hfT : f = T' (p.tensorOne FS FT Φ) := hθ.2 _ hvacm
  have hπe : p.π e = 0 := pi_eq_zero_of p horth
  have hpe2 : p.e * p.e = p.e := p.split.1
  have hid : Φ' = p.tensorAt FS FT Φ Ξk := by
    refine _root_.GlobalTheory.RatHalfDense.eq_of_rat D S T _ (e + p.e) hE' Φ' _ hΦ'SB (hsb Ξk hΞk) fun γ => ?_
    rw [hΦ'rat, hΞ']
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add (f := _), hπe, pi_e_self, zero_add, one_mul, Place.pr]
    have hs : (γ.map fun a => (e + p.e) * incA D a) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) =
        γ.map fun a => e * incA D a := by
      rw [up_down_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have key := hc.2 (T' ∘ₗ p.tensorL FS FT Φ) hmodel ⟨Place.intInd Y Y', GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'⟩ ⟨Ξk, hΞk⟩ rfl rfl
  rw [hf'T, hid, hfT]
  simpa only [LinearMap.comp_apply, Place.tensorL_apply, Place.tensorOne_apply] using key

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.ZeroCongr
open Formalism.UG

theorem adFun_of_same {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (Ψ) (hΨ : Ψ ∈ AdFun S' (embT D)) : Ψ ∈ AdFun S (embT D) := by
  intro γ hγ x x' κ h y y' hy
  rw [hchi κ ⟨κ.1, (hU _).1 κ.2⟩ rfl]
  exact hΨ γ hγ x x' ⟨κ.1, (hU _).1 κ.2⟩ h y y' hy


set_option maxHeartbeats 1000000 in
theorem rdS_congr (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (hn : V.rank = n)
    (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    {cl cl' : Type} (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (yc' : cl' → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hb' : Function.Bijective (fun c => (Quotient.mk'' (yc' c) : Cls S')))
    (lam : D.what₂.Tau → DomWeight n) (φ) (φ') (hφ' : φ' ∈ FiC S' (embT D) lam yc')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (hrep : ∀ c, ∃ c', ∃ κ : S.U, (yc' c').1 = (yc c).1 * κ.1 ∧ S.chi κ = 1 ∧ φ c = φ' c')
    (y : Frames (gramC J (embT D))) (g : GA D V) :
    rdS θ V hn S yc φ y g = rdS θ V hn S' yc' φ' y g := by
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ'
  have hA' := (Submodule.mem_inf.1 hΨ).1
  have hA := adFun_of_same S S' hU hchi Ψ hA'
  have e : φ = fun c => Ψ (yc c) := by
    funext c z
    obtain ⟨c', κ, hy, hχ, hφc⟩ := hrep c
    rw [hφc]
    have h1 : IsTr (atInf (embT D) ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) z z := fun τ => by
      show z.1 τ = _ * z.1 τ
      simp [atInf]
    have e3 := hA 1 (Subgroup.one_mem _) (yc c) (yc' c') κ (by rw [map_one, one_mul]; try exact hy) z z h1
    show Ψ (yc' c') z = Ψ (yc c) z
    rw [e3, hχ, Units.val_one, one_mul]
  subst e
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T f bad S cl yc hb Ψ hA y g
  obtain ⟨-, -, hv'⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T' f' bad' S' cl' yc' hb' Ψ hA' y g
  let z : Frames (gramC J (embT D)) :=
    ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hu τ).mul (y.2 τ)⟩
  exact (hv x z hx (fun τ => rfl)).trans (hv' x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.ZeroCongr

namespace GlobalTheory.Fam


set_option maxHeartbeats 4000000 in
theorem rd_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ θ hθ ψ₀ hψ y
  unfold GlobalTheory.AdForm.TwDat.rd GlobalTheory.AdForm.Chart.rd GlobalTheory.Core.Mi.chart0
  dsimp only
  have hfr : ((C.forms u).to0.val0.eY y) = (⟨y.1, y.2⟩ : Frames (gramC (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (embT (I.rec7 l Z)))) :=
    Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y)
  rw [hfr]
  funext g
  refine GlobalTheory.AdForm.ZeroCongr.rdS_congr (I.rec7 l Z) θ hθ _ _ _ _ ?hJ _ _ _ _ (A.K 0 (Nat.zero_le _) β).y_bij ((C.forms u).to0.cls0.toChart.y_bij) (lamT u 0) _ _ ?hφ ?hU ?hchi ?hrep _ g
  case hJ => rfl
  case hφ => exact ((C.forms u).to0.val0.Fi ψ₀).1 (((I.rec7 l Z).fm u).Fi_zero ▸ hψ.1)
  case hU => exact GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member I hI hP l Z C hC u a Ch A hA β hβ
  case hchi => exact _root_.GlobalTheory.Fam.chi_zero_std I hI hP l Z C hC u a Ch A hA β hβ
  case hrep =>
    intro c
    obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.stepZero_representative_differs_by_level I hI hP l Z C hC u a Ch A hA β hβ c
    refine ⟨(I.eCls0 l u a).symm c.1, κ, h1, h2, ?_⟩
    funext z
    have hz : (C.forms u).to0.val0.eY.symm z = ⟨z.1, z.2⟩ := by
      apply (C.forms u).to0.val0.eY.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) _).symm
    rw [hz]
    rfl

end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlaceBis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  first | exact @GlobalTheory.DStepCell.cell_collapse | exact GlobalTheory.DStepCell.cell_collapse | (intros; apply GlobalTheory.DStepCell.cell_collapse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsAllTwistPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_last_two_steps_all_twist_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ w.Q) Ψ₂ → ∀ φ, IsContAut (c.X j) φ → ∀ α β, (∏ i, ((F.Q i).idx (j + 1) : ℂ)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ (conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i))).support, conv (List.ofFn fun i => (F.Q i).εL j (F.eqv j α i)) g • t.om j (g, 1) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (w.eQT j h) Ψ₂)) = ∑ γ, (∏ i, (F.Q i).wt (j + 1) (F.eqv (j + 1) γ i)) • c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ (aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i))) (aconv (List.ofFn fun i => (F.Q i).dL (j + 1) (F.eqv (j + 1) γ i) (F.eqv (j + 1 + 1) β i))) (c.lst j h (v.τ j h) (t.sBF j 0 h) Ψ₁ Ψ₂)) := by
  first | exact @GlobalTheory.QLastCore.core | exact GlobalTheory.QLastCore.core | (intros; apply GlobalTheory.QLastCore.core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  first | exact @GlobalTheory.SeeSawLaws.gLaws | exact GlobalTheory.SeeSawLaws.gLaws | (intros; apply GlobalTheory.SeeSawLaws.gLaws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTransportRelations_of_familyLaws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  first | exact @GlobalTheory.SeeSaw.mainX_of_lawsX | exact GlobalTheory.SeeSaw.mainX_of_lawsX | (intros; apply GlobalTheory.SeeSaw.mainX_of_lawsX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.Fam
namespace VolMid

theorem index_pi_univ' {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_of_pi {ι : Type} [Fintype ι] {G : Type} [Group G] {M : ι → Type} [∀ i, Group (M i)]
    (φ : G →* ((i : ι) → M i)) (Up U : Subgroup G) (K H : ∀ i, Subgroup (M i))
    (hK : ∀ g ∈ Up, ∀ i, φ g i ∈ K i) (hs : ∀ x : (i : ι) → M i, (∀ i, x i ∈ K i) → ∃ g ∈ Up, φ g = x)
    (hU : ∀ g, g ∈ U ↔ g ∈ Up ∧ ∀ i, φ g i ∈ H i) : U.relIndex Up = ∏ i, (H i).relIndex (K i) := by
  let ψ : Up →* ((i : ι) → K i) :=
    { toFun := fun g i => ⟨φ g.1 i, hK g.1 g.2 i⟩
      map_one' := by ext i; simp
      map_mul' := by intro x y; ext i; simp }
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨g, hg, e⟩ := hs (fun i => (x i).1) (fun i => (x i).2)
    exact ⟨⟨g, hg⟩, by ext i; simp [ψ, e]⟩
  have e : U.subgroupOf Up = (Subgroup.pi Set.univ fun i => (H i).subgroupOf (K i)).comap ψ := by
    ext g
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_pi, hU, g.2, ψ]
  rw [Subgroup.relIndex, e, Subgroup.index_comap_of_surjective _ hψ, index_pi_univ']
  rfl

end VolMid

open VolMid

end GlobalTheory.Fam
end
end

