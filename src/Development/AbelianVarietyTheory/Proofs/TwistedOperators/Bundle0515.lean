module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000

theorem bridge (V : HSp D) (k : GA D V) (s : Fin V.rank → D.host.E) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) =
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

theorem fwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfg : Module.Finite (𝓞 D.host.E) C) (hsp : Submodule.span D.host.E (C : Set (Fin V.rank → D.host.E)) = ⊤)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) := by
  have hmem : (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
    Submodule.subset_span ⟨s, hs, rfl⟩
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) C hfg hsp
    (Formalism.IndefR.Lev.finE V k) ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)))
  have e : ((Formalism.IndefR.Lev.finE V k)⁻¹ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).1 *ᵥ ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j))) = (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e] at hmem
  have k2 := key.2 hmem
  have hb := bridge V k s
  simp only [hb]
  exact k2

theorem bwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  rw [bridge, map_inv]
  exact hs

theorem mem_globLat_iff {n : ℕ} (g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat g C ↔ (g⁻¹).1 *ᵥ (fun i => Formalism.IndefR.Datum.eToEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
  Iff.rfl

theorem colLat_fin {n : ℕ} (B : GL (Fin n) D.host.E) : Module.Finite (𝓞 D.host.E) (colLat B) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))

theorem colLat_span {n : ℕ} (B : GL (Fin n) D.host.E) :
    Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hcol : ∀ j : Fin n, (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) ∈
      Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) :=
    fun j => Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩)
  have e : v = ∑ j, ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) := by
    have h1 : (B : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)


set_option maxHeartbeats 1000000 in
theorem globLat_mul_iff {n : ℕ} (a b : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (Λ C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔ b.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat a Λ ↔ y ∈ Formalism.UG.CS.globLat (a * b) C := by
  rw [mem_globLat_iff, mem_globLat_iff]
  have e : ((a * b)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)).1 = (b⁻¹).1 * (a⁻¹).1 := congrArg Units.val (_root_.mul_inv_rev a b)
  have e2 : b.1 * (b⁻¹).1 = 1 := congrArg Units.val (mul_inv_cancel b)
  rw [e, ← Matrix.mulVec_mulVec, hb ((b⁻¹).1 *ᵥ ((a⁻¹).1 *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i))),
    Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

theorem movedLat_eq {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) :
    inV (S.N.fr X) (GlobalTheory.SumSize.latAt S X x) =
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) :
        Set (Fin (G.V X).rank → D.host.E)) := by
  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) x) (G.Λ X) ↔
      y ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) := by
    have e : Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X)) =
        finG (G.V X) x * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 :=
      map_mul (Formalism.IndefR.Lev.finE (G.V X)) (x : GA D (G.V X)) (S.N.u X).1
    rw [e]
    exact globLat_mul_iff _ _ _ _ (S.N.u_lat X hX)
  ext y
  simp only [inV, GlobalTheory.SumSize.latAt, Set.mem_image, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (key _).1 hz
  · intro hy
    refine ⟨((S.N.fr X)⁻¹ : GL _ D.host.E).1 *ᵥ y, ?_, ?_⟩ <;>
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact (key _).2 hy

theorem actO_latO_le (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT) :
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
  _root_.GlobalTheory.LatMoveGen.actO_mem_latO S T g h AS BS AT BT (fun s hs => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BS _ (hS s hs)) (fun t ht => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BT _ (hT t ht))

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (w : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := by
  simp only [actO]
  rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * w), ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.one_mul]

theorem actO_latO_onto (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT)
    (hS' : ∀ s ∈ BS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g⁻¹ *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AS)
    (hT' : ∀ t ∈ BT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AT) :
    (∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
    (∀ w' ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∃ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T g h w = w') :=
  ⟨actO_latO_le S T g h AS BS AT BT hS hT, fun w' hw' =>
    ⟨actO S T g⁻¹ h⁻¹ w', actO_latO_le S T g⁻¹ h⁻¹ BS AS BT AT hS' hT' w' hw', actO_actO_inv S T g h w'⟩⟩

end GlobalTheory.MovedHomLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExists
section
namespace I195MixedCoordinates_5724cff7a327dd5e61feafed

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_5724cff7a327dd5e61feafed

public noncomputable abbrev _root_.I195MixedCoordinates_17fa37e7cd6a496353bc7635.target :=
  @_root_.I195MixedCoordinates_5724cff7a327dd5e61feafed.target

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.MixAdj

theorem isBump_conj_smul {D : D7} {m n : ℕ} (c c' : AE D) (hc : c' * c = 1) (hc' : c * c' = 1) {β : Mx D m n → ℂ} (hβ : IsBump β) :
    IsBump (fun x : Mx D m n => starRingEnd ℂ (β (c • x))) := by
  let e : Mx D m n ≃ₜ Mx D m n :=
    { toFun := fun x => c • x, invFun := fun x => c' • x,
      left_inv := fun x => by simp only [smul_smul, hc, one_smul],
      right_inv := fun x => by simp only [smul_smul, hc', one_smul],
      continuous_toFun := continuous_const_smul c, continuous_invFun := continuous_const_smul c' }
  have hinf : ∀ u : Mx D m n, u.map (infPart D) = 0 → (c • u).map (infPart D) = 0 := fun u hu => by
    ext i j
    have := congrArg (fun M : Matrix _ _ _ => M i j) hu
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]
  have hfin : ∀ u : Mx D m n, u.map (finPart D) = 0 → (c • u).map (finPart D) = 0 := fun u hu => by
    ext i j
    have := congrArg (fun M : Matrix _ _ _ => M i j) hu
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, this, mul_zero, Matrix.zero_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_conj.comp (hβ.cont.comp (continuous_const_smul c))
  · exact (hβ.supp.comp_homeomorph e).comp_left (map_zero (starRingEnd ℂ))
  · obtain ⟨U, hU, hper⟩ := hβ.level
    refine ⟨U.comap (DistribSMul.toAddMonoidHom (Mx D m n) c), hU.preimage (continuous_const_smul c), ?_⟩
    intro u hu hu0 x
    simp only [smul_add]
    rw [hper (c • u) hu (hinf u hu0)]
  · intro k l hl hl0 w
    have h0 : ContDiff ℝ ∞ fun t => β (c • w + ((DistribSMul.toAddMonoidHom (Mx D m n) c).comp l) t) :=
      hβ.smooth k ((DistribSMul.toAddMonoidHom (Mx D m n) c).comp l)
        ((continuous_const_smul c).comp hl) (fun t => hfin _ (hl0 t)) (c • w)
    have h := (Complex.conjCLE.contDiff (n := ∞)).comp h0
    convert h using 2 with t
    simp [smul_add]

theorem mixT_bump_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (v : VolM D ρ S.rank) (β : Mx D S.rank ρ → ℂ) (g : WO S T₀ → ℂ), IsBump β → IsThetaFunO ψ S T₀ g → ∃ Φ, IsThetaFunO ψ S T Φ ∧ ∀ y, (_root_.I195MixedCoordinates_5724cff7a327dd5e61feafed.target d) S ψ v.μ v.𝓕 Φ y = β y • g := by
  intro D ψ hψ S T T₀ ρ d v β g hβ hg
  obtain ⟨μ', 𝓕', hcov, -, -, -, hsw⟩ := GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d v.μ v.𝓕 v.covol
  have hadj := fun X Y : HSp D => (GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ X Y).2.2.1
  have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have hc : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  have hc' : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  have hβ' := isBump_conj_smul (incA D D.host.xi0) (incA D D.host.xi0⁻¹) hc hc' hβ
  have hg' : IsThetaFunO ψ T₀ S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T₀ S) g) := (hadj S T₀ g).2 hg
  obtain ⟨Φ', hΦ', hmix⟩ := _root_.GlobalTheory.BumpMix.bump_mul_theta_mixS D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hcov⟩ _ _ hβ' hg'
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ', (hadj T S Φ').2 hΦ', fun y => ?_⟩
  have h1 := hsw (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T) Φ') y
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj _ _ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger T S)] at h1
  have h2 := hmix (incA D D.host.xi0⁻¹ • y)
  change I195MixedCoordinates_8df3303fbb03152b340aba95.source d S ψ μ' 𝓕' Φ'
    (incA D D.host.xi0⁻¹ • y) = _ at h2
  rw [h2, smul_smul, hc', one_smul] at h1
  funext z
  have h3 := congrFun h1 (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T₀ z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger, map_mul,
    Complex.conj_conj] at h3
  have h4 := congrArg (starRingEnd ℂ) h3
  simp only [map_mul, Complex.conj_conj] at h4
  simp only [Pi.smul_apply, smul_eq_mul]
  exact h4.symm

end GlobalTheory.MixAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.MovedField Formalism.L2.Host in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffIdempotentFinitePointMemCompletedTensorLattic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel.OffTens

theorem partAt_finW_off_mem_hatA : ∀ (D : D7) (S T : HSp D) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ (L : Lt D.host.E T.rank) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E), y ∈ tens (stdL D.host.E S.rank) L → GlobalTheory.LiftLevel.partAt (1 - e - cA D e) (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L)) := by
  intro D S T Pg Q e he L y hy
  classical
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := GlobalTheory.IdemSumFinAdele.exists_finAdele_of_idemSum D _ e he
  have hf : 1 - e - cA D e = 1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) := by rw [hσ]; ring
  have hW : finW S T y = GlobalTheory.LiftLevel.TrOff.gm S T 1 y := rfl
  rw [hf, hW, GlobalTheory.LiftLevel.TrOff.partAt_gm, mul_one]
  have hO : ∀ (c : 𝓞 D.host.F), ∀ z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L),
      (algebraMap D.host.F D.host.E (c : D.host.F)) • z ∈ tens (stdL D.host.E S.rank) (GlobalTheory.LiftLevel.liftI Pg Q • L) :=
    fun c z hz => GlobalTheory.Ker.HatLat.smul_mem_tens _ _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c) hz
  have hγ : (1 - σ) ∈ intAf D.host.F := by
    intro w
    rw [map_sub, map_one]
    by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
    · obtain ⟨PP, hPP, rfl⟩ := hw
      rw [hσ1 PP hPP, sub_self]; exact zero_mem _
    · push_neg at hw
      rw [hσ0 w hw, sub_zero]; exact GlobalTheory.LatVac.one_mem_intAf _ w
  refine GlobalTheory.HatPoint.mem_hatA_of_div D S T _ hO _ hγ _ fun w => ?_
  by_cases hw : ∃ PP ∈ Pg ∪ Q, HeightOneSpectrum.under (𝓞 D.host.F) PP = w
  · left
    obtain ⟨PP, hPP, rfl⟩ := hw
    rw [map_sub, map_one, hσ1 PP hPP, sub_self]
  · right
    push_neg at hw
    have hex : ∀ PP ∈ Pg ∪ Q, ∃ s : 𝓞 D.host.F,
        algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s ∈ PP.asIdeal ∧ s ∉ w.asIdeal := by
      intro PP hPP
      by_contra hcon
      push_neg at hcon
      apply hw PP hPP
      have hle : (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal ≤ w.asIdeal := fun s hs => hcon s hs
      exact HeightOneSpectrum.ext ((HeightOneSpectrum.isMaximal _).eq_of_le w.isPrime.ne_top hle)
    choose! tf htf1 htf2 using hex
    refine ⟨∏ PP ∈ Pg ∪ Q, tf PP, ?_, ?_⟩
    · exact (Submonoid.prod_mem w.asIdeal.primeCompl fun c hc => htf2 c hc : _)
    · have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP) ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
        rw [map_prod]
        exact Ideal.prod_mem_prod fun PP hPP =>
          GlobalTheory.TrOffShift.algebraMap_mem_conjI (D := D) _ _ (htf1 PP hPP)
      exact GlobalTheory.LiftLevel.smul_mem_tens (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (∏ PP ∈ Pg ∪ Q, tf PP))
        (fun u hu => Submodule.smul_mem_smul hmem hu) hy

end GlobalTheory.LiftLevel.OffTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairChangeBasis
section
namespace GlobalTheory.TracePairingBasisChange

open Matrix

theorem pair_eq_trace {K : Type} [Field K] {n d : ℕ} (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = Matrix.trace (Xᵀ * Y) := by
  unfold GlobalTheory.FlipMatch.pairM
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem pair_change_basis {K : Type} [Field K] {n d : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin d) (Fin d) K) (b : GL (Fin n) K) (c : GL (Fin d) K)
    (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM
                 ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
                 (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B *
                   (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  rw [pair_eq_trace, Matrix.mul_neg, Matrix.trace_neg, neg_inj]
  have hb : Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K) * Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have key : Matrix.transpose ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K)) *
      (Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K)) =
      (↑c⁻¹ : Matrix (Fin d) (Fin d) K) * ((Matrix.transpose P * (A * (Q * Matrix.transpose B))) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.transpose (↑b⁻¹ : Matrix (Fin n) (Fin n) K)), hb, Matrix.one_mul]
  rw [key, Matrix.trace_mul_comm, Matrix.mul_assoc, hc, Matrix.mul_one]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.TracePairingBasisChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.resT_cP_argT | exact GlobalTheory.SeeConjChar.resT_cP_argT | (intros; apply GlobalTheory.SeeConjChar.resT_cP_argT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighestStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  first | exact @GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | exact GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | (intros; apply GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest <;> assumption)
end

