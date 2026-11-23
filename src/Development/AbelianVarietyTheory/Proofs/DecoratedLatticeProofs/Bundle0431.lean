module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PolOfFnOfOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentPowCompletionTrivialAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.DiUnit

variable {D : D7}

theorem eq_one_iff {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} : idV 𝔞 v = idV 1 v ↔
    ∀ s, s ∈ idV 𝔞 v ↔ incA D (1 : D.host.E)⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  simp only [inv_one, map_one, one_mul]
  constructor
  · intro h s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => ⟨h, h.1⟩, fun h => h.1⟩
  · intro h
    ext s
    rw [h, GlobalTheory.SeeSaw.idV_one_eq_intAt]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩

theorem mul_eq_one {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (h1 : idV 𝔞 v = idV 1 v) (h2 : idV 𝔟 v = idV 1 v) :
    idV (𝔞 * 𝔟) v = idV 1 v := by
  have := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔟 1 1 one_ne_zero one_ne_zero (eq_one_iff.1 h1) (eq_one_iff.1 h2)
  rw [mul_one] at this
  exact eq_one_iff.2 this

theorem pow_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) (n : ℕ) : idV (𝔞 ^ n) v = idV 1 v := by
  induction n with
  | zero => rw [pow_zero]
  | succ n ih => rw [pow_succ]; exact mul_eq_one ih h

theorem inv_eq_one {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} (h : idV 𝔞 v = idV 1 v) : idV 𝔞⁻¹ v = idV 1 v := by
  have h0 : 𝔞 ≠ 0 := fun e =>
    GlobalTheory.SeeSaw.LiftModel.idV_ne_bot (one_ne_zero (α := FI D)) v (by rw [← h, e, GlobalTheory.SeeSaw.idV_zero])
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔞⁻¹ (inv_ne_zero h0)
  have h1 := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v 𝔞 𝔞⁻¹ 1 y one_ne_zero hy0 (eq_one_iff.1 h) hy
  rw [mul_inv_cancel₀ h0, one_mul] at h1
  ext s
  rw [hy, ← h1]

theorem AAbar_eq_one {v : GlobalTheory.FinPl.Pl D} (hA : idV D.host.AA v = idV 1 v) : idV D.host.AAbar v = idV 1 v := by
  ext s
  have h1 := GlobalTheory.SeeSaw.idV_cA_iff D v D.host.AA (cA D s)
  rw [GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.conjFI_AA] at h1
  have h2 := GlobalTheory.SeeSaw.idV_cA_iff D v 1 s
  rw [map_one] at h2
  rw [← h1, hA, h2]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace (p : SplitPt D k) (hp : p.UnitAA) :
    idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v = idV 1 p.v := by
  have hx : D.host.xi0 ≠ 0 := Formalism.L2.Pj.cmHost_imaginaryGenerator_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  ext s
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  constructor
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
      have e : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (r • D.host.xi0) : AE D) =
          incA D D.host.xi0 * (pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E r) := by
        rw [GlobalTheory.IdVGen.incA_mul_tmul, Algebra.smul_def, mul_comm (algebraMap (𝓞 D.host.E) D.host.E r)]
      rw [e]
      exact (hp.1 _ (GlobalTheory.IdVGen.gen_mem_intAt hα hαv r)).1
    | zero => exact GlobalTheory.IdVGen.intAt_zero' _
    | add a b _ _ ha hb => exact GlobalTheory.IdVGen.intAt_add' ha hb
    | neg a _ ha => exact GlobalTheory.IdVGen.intAt_neg' ha
  · intro hs
    have h3 := (GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 (hp.1 s hs).2
    have key : ∀ y ∈ idV (1 : FI D) p.v,
        incA D D.host.xi0 * y ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0) p.v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, hαv, a, ha, rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
        rw [GlobalTheory.IdVGen.incA_mul_tmul]
        refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
        exact (FractionalIdeal.mem_spanSingleton _).2 ⟨o, by rw [Algebra.smul_def]; exact mul_comm _ _⟩
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul] at this

theorem AA_eq_one (p : SplitPt D k) (hp : p.UnitAA) : idV D.host.AA p.v = idV 1 p.v := by
  let L : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1
  let ζ : Fin L.rank → D.host.E := fun _ => 1
  have hζ : ζ ≠ 0 := fun e => one_ne_zero (congrFun e ⟨0, by change 0 < 1; decide⟩)
  have e : GlobalTheory.FinPl.latA L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ 1) (· = p.v) =
      GlobalTheory.FinPl.latV L (GlobalTheory.SeeSaw.LiftModel.lineLat L ζ D.host.AA) (· = p.v) := by
    unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
    congr 1
    ext y
    constructor
    · rintro ⟨α, h1, h2, a, ha, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, 1, rfl, _, ⟨a * c, ?_, rfl⟩, ?_⟩
      · have := FractionalIdeal.mul_mem_mul (S := nonZeroDivisors (𝓞 D.host.E)) (I := D.host.AA) (J := 1) ha hc
        rwa [mul_one] at this
      · funext i; simp [mul_assoc]
    · rintro ⟨α, h1, h2, _, rfl, _, ⟨c, hc, rfl⟩, rfl⟩
      refine ⟨α, h1, h2, c, hc, _, ⟨1, FractionalIdeal.one_mem_one _, rfl⟩, ?_⟩
      funext i; simp
  have key : ∀ s ∈ idAt D (· = p.v), s ∈ idV D.host.AA p.v ↔ s ∈ idV 1 p.v := fun s hs => by
    rw [← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ D.host.AA p.v s hs,
      ← GlobalTheory.SeeSaw.LiftModel.lineLatAt_lineLat L hζ 1 p.v s hs, ← e, hp.2]
  ext s
  exact ⟨fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).1 h,
    fun h => (key s (GlobalTheory.SeeSaw.LiftModel.idV_le_idAt _ _ s h)).2 h⟩

end GlobalTheory.Core.Mi.LatMatch.DiUnit


open GlobalTheory.Core.Mi.LatMatch.DiUnit in
theorem GlobalTheory.Core.Mi.LatMatch.idV_dI_pow_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), p.UnitAA → ∀ (n : ℕ) (a : AE D), (a ∈ idV (dI D ^ n) p.v ↔ a ∈ intAt D (· = p.v)) ∧ (a ∈ idV (dI D ^ n)⁻¹ p.v ↔ a ∈ intAt D (· = p.v)) := by
  intro D k _ _ _ _ p hp n a
  have hd : idV (dI D) p.v = idV 1 p.v := by
    have hA := AA_eq_one p hp
    unfold GlobalTheory.SeeSaw.dI
    exact mul_eq_one (mul_eq_one (fractionalIdealCompletion_xi0Span_eq_unit_at_splitPlace p hp) hA) (AAbar_eq_one hA)
  have h1 := pow_eq_one hd n
  have h2 := inv_eq_one h1
  exact ⟨by rw [h1, GlobalTheory.SeeSaw.idV_one_eq_intAt], by rw [h2, GlobalTheory.SeeSaw.idV_one_eq_intAt]⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace

variable {D : D7} {c : Comm D} {v : VCom c}

def IsMatrixInFrameOfXZero (G : GLoc v) (κ : GA D (c.X 0)) (g : GL (XIx (Fin D.R.k) (Fin D.R.t) 0) G.k) : Prop :=
  (mt (c.X 0) κ).map G.q.pr = (G.FX 0 (Nat.zero_le _)).β * g.val * (G.FX 0 (Nat.zero_le _)).γ

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end GlobalTheory.FamTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn.HalfOff

variable {D : D7} {S T : HSp D}

theorem smul_apply' (b : AE D) (t : WO S T) (i j) : (b • t) i j = b * t i j := by
  rw [Matrix.smul_apply, smul_eq_mul]

theorem smul_half_zero {a b : AE D} (hab : a * b = 0) {x : WO S T} (hx : IsHalf a x) : b • x = 0 := by
  ext i j
  rw [smul_apply', Matrix.zero_apply, ← hx i j, ← mul_assoc, mul_comm b a, hab, zero_mul]

theorem half_smul {b : AE D} (hb : b * b = b) (t : WO S T) : IsHalf b (b • t) := fun i j => by
  rw [smul_apply', ← mul_assoc, hb]

theorem tens_trans {a b : AE D} (hab : a * b = 0) (Φ Ψ : WO S T → ℂ) {x : WO S T} (hx : IsHalf a x) :
    tens b (fun t => Φ (t + x)) Ψ = fun t => tens b Φ Ψ (t + x) := by
  funext t
  simp only [tens_apply, smul_add, smul_half_zero hab hx, add_zero]
  congr 2
  abel

theorem tens_modul (ψ : AddChar (AF D.host.F) ℂ) {a b : AE D} (hab : a * b = 0) (hb : b * b = b)
    (Φ Ψ : WO S T → ℂ) {y : WO S T} (hy : IsHalf (cA D a) y) :
    tens b (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
  funext t
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
    rw [← GlobalTheory.LocMod.TensorModel.symplO_add_left', sub_add_cancel]
  rw [tens_apply, tens_apply, e1, GlobalTheory.LocMod.TensorModel.symplO_half_zero hba (half_smul hb t) hy, add_zero, mul_assoc]

theorem tens_vac {a b : AE D} (hab : a * b = 0) (hb : b * b = b) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, b • u ∈ Λ) :
    tens b ((1 : ℂ) • halfInd a Λ) (halfInd b Λ) = (1 : ℂ) • halfInd (a + b) Λ := by
  classical
  funext t
  simp only [one_smul, tens_apply]
  set M : WO S T := b • t with hMdef
  have hM : IsHalf b M := half_smul hb t
  have key : ((t - M ∈ Λ ∧ IsHalf a (t - M)) ∧ M ∈ Λ) ↔ (t ∈ Λ ∧ IsHalf (a + b) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 h3, fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, smul_apply'] at h
      linear_combination h + t i j * hab
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λ := hΛ t h1
      refine ⟨⟨sub_mem h1 h3, fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, smul_apply']
      linear_combination h2 i j - t i j * hab
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (a + b) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos ⟨h3, hM⟩, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λ
    · rw [if_pos (show M ∈ Λ ∧ IsHalf b M from ⟨h3, hM⟩), mul_one,
        if_neg (show ¬(t - M ∈ Λ ∧ IsHalf a (t - M)) from fun h => hR (key.1 ⟨h, h3⟩))]
    · rw [if_neg (show ¬(M ∈ Λ ∧ IsHalf b M) from fun h => h3 h.1), mul_zero]

end GlobalTheory.FinPl.PutIn.HalfOff


open GlobalTheory.FinPl.PutIn.HalfOff in
theorem GlobalTheory.FinPl.PutIn.isPlaceModel_tensHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ : AddSubgroup (WO S T)) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensL b (halfInd b Λ)) := by
  intro D ψ S T a b Λ f₀ Tm hab hb hΛ hT
  have hba : b * a = 0 := by rw [mul_comm, hab]
  have hsb : ∀ Φ, IsSBHalf a Λ Φ → IsSBHalf (a + b) Λ (tens b Φ (halfInd b Λ)) := fun Φ hΦ =>
    _root_.GlobalTheory.FinPl.PutIn.isSBHalf_tens D S T a b Λ Φ (halfInd b Λ) hab hb hΛ hΦ (GlobalTheory.isSBHalf_halfInd b Λ)
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.comp_apply, tensL_apply, tens_trans hab Φ _ hx]
    have hx' : IsHalf (a + b) x := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum hba hx
    exact hT.trans _ (hsb Φ hΦ) x hx'
  · rw [LinearMap.comp_apply, tensL_apply, tens_modul ψ hab hb Φ _ hy]
    have hy' : IsHalf (cA D (a + b)) y := by
      rw [add_comm]; exact GlobalTheory.LocMod.TensorModel.half_sum_cA hba hy
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensL_apply, tens_vac hab hb Λ hΛ]
    exact hT.vac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedIntegralValueSuccPlacesOuter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.QValOuter

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem gl₂_comm (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (a : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)
    (b : GL (Q'.n₂ ⊕ Fin (Q'.c + 1)) Q'.k) : Q₀.gl₂ a * Q'.gl₂ b = Q'.gl₂ b * Q₀.gl₂ a := by
  have h0 : Q₀.gl₂ a ∈ grpAt S.B'.V (· = Q₀.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q₀.k Q₀.q S.B'.V _ Q₀.F.G₂ Q₀.gl₂ Q₀.loc₂).2.1]; exact ⟨a, rfl⟩
  have h1 : Q'.gl₂ b ∈ grpAt S.B'.V (· = Q'.q.v) := by
    rw [← (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q'.k Q'.q S.B'.V _ Q'.F.G₂ Q'.gl₂ Q'.loc₂).2.1]; exact ⟨b, rfl⟩
  exact GlobalTheory.SeeSawLastValue.grpAt_comm (fun p hp hp' => hne (hp.symm.trans hp')) h0 h1

theorem typed_trc (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) (e : GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k →₀ ℂ)
    {f : GA D S.B'.V → ℂ} (hf : Q'.Typed f) : Q'.Typed (trc (e.mapDomain Q₀.gl₂) f) := by
  classical
  intro j
  funext x
  have hj := hf j
  simp only [rTrans, Pi.smul_apply, smul_eq_mul, trc_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hg)
  have := congrFun hj (x * Q₀.gl₂ a)
  simp only [rTrans, Pi.smul_apply, smul_eq_mul] at this
  rw [mul_assoc x, ← gl₂_comm Q₀ Q' hne, ← mul_assoc, this]
  ring

theorem away_pair (Q₀ Q' : QStep S) (hne : Q₀.q.v ≠ Q'.q.v) {A T : HSp D} (c d : WO A T →₀ ℂ) (hc : Q'.Away c)
    (hd : ∀ u ∈ d.support, IsHalf (Q₀.q.e + cA D Q₀.q.e) u) : Q'.Away (aconv [c, d]) := by
  obtain ⟨ε₀, hε₀, he₀⟩ := Q₀.q.above
  obtain ⟨ε', hε', he'⟩ := Q'.q.above
  have horth : algebraMap (AF D.host.F) (AE D) ε' * algebraMap (AF D.host.F) (AE D) ε₀ = 0 := by
    rw [← map_mul, GlobalTheory.VacuumFrameCompare.place_orth hε' hε₀ (Ne.symm hne), map_zero]
  intro u hu i j
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_aconv_pair c d hu
  have h1 := hc a ha i j
  have h2 := hd b hb i j
  rw [he'] at h1 ⊢
  rw [he₀] at h2
  have h3 : (1 - algebraMap (AF D.host.F) (AE D) ε') * b i j = b i j := by
    rw [← h2, sub_mul, one_mul, ← mul_assoc, horth, zero_mul, sub_zero]
  rw [Matrix.add_apply, mul_add, h1, h3]

theorem hyps_succ {r : ℕ} (Q : Fin (r + 1) → QStep S) (hinj : Function.Injective fun i => (Q i).q.v)
    {c₁ : WO S.B.A S.J.W₀ →₀ ℂ} {c₂ : WO S.J.W₀ S.B'.A →₀ ℂ} {f₁ : WO S.B.V S.J.W → ℂ} {f₂ : WO S.J.W S.B'.V → ℂ}
    {φ : GA D S.B.A → ℂ} {f : GA D S.B'.V → ℂ} {g : GA D S.B.V} {h₁ : GA D S.J.W} {h₂ : GA D S.B'.V}
    (hH : Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) (γ : (Q 0).A₁) (β : (Q 0).A₂) :
    Hyps (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  obtain ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩ := hH
  have hne : ∀ i : Fin r, (Q 0).q.v ≠ (Q i.succ).q.v := fun i h => Fin.succ_ne_zero i (hinj h).symm
  have hP : ∀ v, places (fun i : Fin r => Q i.succ) v → places Q v := fun v ⟨i, hi⟩ => ⟨i.succ, hi⟩
  refine ⟨fun i => ⟨away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).1 ((Q 0).ent₁ γ).1,
      away_pair (Q 0) (Q i.succ) (hne i) _ _ (hc i.succ).2 ((Q 0).ent₂ γ β).1⟩, t1, t2, fun i => hv i.succ, hφ,
    contAut_trc _ hf, fun i => typed_trc (Q 0) (Q i.succ) (hne i) _ (ht i.succ),
    grpOff_anti D _ _ _ hP hg, grpOff_anti D _ _ _ hP hh₁, grpOff_anti D _ _ _ hP hh₂⟩

theorem trc_conv_cons {V : HSp D} (E : GA D V →₀ ℂ) (l : List (GA D V →₀ ℂ))
    (h : ∀ x ∈ E.support, ∀ e ∈ l, ∀ y ∈ e.support, x * y = y * x) (f : GA D V → ℂ) :
    trc (conv (E :: l)) f = trc (conv l) (trc E f) := by
  have e1 : conv (E :: l) =
      (MonoidAlgebra.ofCoeff (conv l) * MonoidAlgebra.ofCoeff E : MonoidAlgebra ℂ (GA D V)).coeff := by
    rw [← comm_conv E l h, ← conv_cons]
  rw [e1, trc_mul]

theorem sum_pi_succ {r : ℕ} {α : Fin (r + 1) → Type} [∀ i, Fintype (α i)] (F : (∀ i, α i) → ℂ) :
    ∑ γ, F γ = ∑ a : α 0, ∑ γ' : ∀ i : Fin r, α i.succ, F (Fin.cons a γ') := by
  rw [← (Fin.consEquiv α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem value_succ {r : ℕ} (Q : Fin (r + 1) → QStep S)
    (hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a)
    (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ)
    (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ) (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) :
    value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ = ∑ p : (Q 0).A₁ × (Q 0).A₂, (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2) *
      value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
        (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ := by
  classical
  have hX : ∀ (γ0 : (Q 0).A₁) (β0 : (Q 0).A₂) (γ' : ∀ i : Fin r, (Q i.succ).A₁) (β' : ∀ i : Fin r, (Q i.succ).A₂),
      S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)))
        (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ ((Fin.cons γ0 γ' : ∀ i, (Q i).A₁) i)
          ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i).e₂ ((Fin.cons β0 β' : ∀ i, (Q i).A₂) i)).mapDomain (Q i).gl₂)) f)
        g h₁ h₂ =
      S.val (aconv (aconv [c₁, (Q 0).d₁ γ0] :: List.ofFn fun i => (Q i.succ).d₁ (γ' i)))
        (aconv (aconv [c₂, (Q 0).d₂ γ0 β0] :: List.ofFn fun i => (Q i.succ).d₂ (γ' i) (β' i))) f₁ f₂ φ
        (trc (conv (List.ofFn fun i => ((Q i.succ).e₂ (β' i)).mapDomain (Q i.succ).gl₂))
          (trc (((Q 0).e₂ β0).mapDomain (Q 0).gl₂) f)) g h₁ h₂ := by
    intro γ0 β0 γ' β'
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [aconv_pair_cons, aconv_pair_cons, trc_conv_cons]
    intro x hx e he y hy
    rw [List.mem_ofFn] at he
    obtain ⟨i, rfl⟩ := he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact hcomm i a b
  rw [Fintype.sum_prod_type]
  simp only [value]
  simp only [sum_pi_succ (α := fun i => ↥(Q i).A₁), sum_pi_succ (α := fun i => ↥(Q i).A₂)]
  simp only [hX]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ0 _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β0 _ => Finset.sum_congr rfl fun γ' _ => Finset.sum_congr rfl fun β' _ => ?_
  ring

theorem outer : ∀ (D : D7) (r : ℕ), ValQr D r → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin (r + 1) → QStep S), Function.Injective (fun i => (Q i).q.v) → ∀ μ₁ ρ₁ μ₂ ρ₂, Norm (fun i => Q i.succ) μ₁ ρ₁ μ₂ ρ₂ → ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ → Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => innerVal Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂) := by
  intro D r IH ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ hN c₁ c₂ f₁ f₂ φ f g h₁ h₂ hH
  have hinj' : Function.Injective fun i : Fin r => (Q i.succ).q.v := hinj.comp (Fin.succ_injective _)
  have hcomm : ∀ i : Fin r, ∀ a b, (Q 0).gl₂ a * (Q i.succ).gl₂ b = (Q i.succ).gl₂ b * (Q 0).gl₂ a :=
    fun i => gl₂_comm (Q 0) (Q i.succ) fun h => Fin.succ_ne_zero i (hinj h).symm
  have key := GlobalTheory.SeeSaw.VanMany.iteratedQuotientIntegral_finite_linearCombination ρ₁ μ₁ ρ₂ μ₂ (I := (Q 0).A₁ × (Q 0).A₂)
    (fun p => (Q 0).volJ * ((Q 0).w₁ p.1 * (Q 0).w₂ p.2))
    (fun p x y => integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂ x.1 y.1)
    (fun p => value (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ p.1]) (aconv [c₂, (Q 0).d₂ p.1 p.2]) f₁ f₂ φ
      (trc (((Q 0).e₂ p.2).mapDomain (Q 0).gl₂) f) g h₁ h₂)
    (fun p => IH ψ hψ σ S (fun i => Q i.succ) hinj' μ₁ ρ₁ μ₂ ρ₂ hN _ _ f₁ f₂ φ _ g h₁ h₂ (hyps_succ Q hinj hH p.1 p.2))
  rw [value_succ Q hcomm]
  convert key using 1
  funext x y
  simp only [innerVal, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

end GlobalTheory.QValOuter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelEntryRationalEquivarianceTransports
section
noncomputable section

namespace GlobalTheory.KerDia.Eqv

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.KerDia
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem ent_smul : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ)
    {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β} (q : (I.stp u a i).D b) (q' : (I.stp u a (i + 1)).D b') (g : (I.stp u a i).G b)
    (g' : (I.stp u a (i + 1)).G b') (x : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) → ℂ),
    (I.chain l u a).sharp i x ∈ LinearMap.range (fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1) →
    ent I l u a i ((I.stp u a i).act b g q) ((I.stp u a (i + 1)).act b' g' q') ((I.stp u a i).tr B.fields.emb B.embLL b g x) =
      (I.stp u a (i + 1)).tr B.fields.emb B.embLL b' g' (ent I l u a i q q' x) := by
  intro B X I l h u a i b b' q q' g g' x hx
  obtain ⟨P, hP⟩ := hx
  funext y'
  have hP' : fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 1 P = fun y : GlobalTheory.Mem.Col2.Fr B.fields.emb B.embLL (B.R.N i) =>
      (∏ τ, deFr y τ ^ (I.chain l u a).sSharp i τ) * x y := hP
  have hr : I.rho u a i b ((I.stp u a i).act b g q) * I.rho' u a i b' ((I.stp u a (i + 1)).act b' g' q') ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have key := opOf_equiv B.fields.emb B.embLL ((I.chain l u a).sSharp i) ((I.chain l u a).sDiv i) I.J.cD (th_contDiff I h u a i q q')
    ((I.stp u a i).gam b g) ((I.stp u a (i + 1)).gam b' g') ((I.stp u a i).chr b g) ((I.stp u a (i + 1)).chr b' g') hr
    (th_move I l h u a i q q' g g') hP' y'
  refine (ent_apply I l u a i _ _ _ y').trans (key.trans ?_)
  rw [← ent_apply]
  rfl

end GlobalTheory.KerDia.Eqv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastGroup_embedding_real_components_block_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (θ : InfFam (I.rec7 l Z)), IsInfFam θ → ∀ (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) emb → ∀ (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (τ : (I.rec7 l Z).what₂.Tau), GlobalTheory.BranchFormula.IsBlock hN (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb k) τ) (infM θ _ (rankP (I.rec7 l Z)) k τ) 1 := by
  first | exact @GlobalTheory.EmbTopBlock.isBlock_infM_emb | exact GlobalTheory.EmbTopBlock.isBlock_infM_emb | (intros; apply GlobalTheory.EmbTopBlock.isBlock_infM_emb <;> assumption)
end

