module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsRename
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContraction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.LineVanish

variable {D : D7}

theorem mxAt_mul_right' {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem fin_of_mxAt' {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem isHalf_mul_right {e : AE D} {m n r : ℕ} {u : Mx D m n} (hu : IsHalf e u) (N : Mx D n r) :
    IsHalf e (u * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hu i k]

theorem isHalf_mul_left {e : AE D} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (N * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hu k j]

theorem contr_smul_left' {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem step3 : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V T : HSp D) (LV : Lat V) (LT : Lat T), IsSelfDualC V LV → IsSelfDualC T LT → ∀ y : WO V T, MxAt P y → y ∉ latO V T (LV : Set _) (LT : Set _) P → ∃ u ∈ latO V T (LV : Set _) (LT : Set _) P, (∃ e, IsSplitIdem D e ∧ IsHalf e u) ∧ ψ (symplO V T u y) ≠ 1 := by
  intro D k _ _ _ _ ι p I P hP ψ hψ V T LV LT hLV hLT y hy hout
  by_contra hno
  push_neg at hno
  apply hout
  have hadd : ∀ a b : WO V T, symplO V T (a + b) y = symplO V T a y + symplO V T b y := by
    intro a b
    have h := GlobalTheory.SplitScalar.symplO_sub_left V T (a + b) b y
    rw [add_sub_cancel_right] at h
    rw [h]; ring
  have hneg : ∀ a : AF D.host.F, ψ a = 1 → ψ (-a) = 1 := by
    intro a ha
    calc ψ (-a) = ψ (-a) * ψ a := by rw [ha, mul_one]
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let K : AddSubgroup (WO V T) :=
    { carrier := {u | ψ (symplO V T u y) = 1}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, GlobalTheory.SplitScalar.symplO_zero_left, AddChar.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hadd, AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h0 : symplO V T (-a) y = -symplO V T a y := by
          have := hadd (-a) a
          rw [neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_left] at this
          exact eq_neg_of_add_eq_zero_left this.symm
        rw [h0]; exact hneg _ ha }
  rw [_root_.GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ V T LV LT hLV hLT P y hy]
  intro u' hu'
  have hle : AddSubgroup.closure {x : WO V T | x ∈ latO V T (LV : Set _) (LT : Set _) P ∧
      ∃ e, IsSplitIdem D e ∧ IsHalf e x} ≤ K := by
    apply (AddSubgroup.closure_le K).2
    intro u hu
    exact hno u hu.1 hu.2
  have hK : u' ∈ K := hle
    (_root_.GlobalTheory.HalfGen.latO_le_closure_halves D k ι p I P hP V T _ _ u' hu')
  rw [GlobalTheory.SplitScalar.symplO_skew]
  exact hneg _ hK


set_option maxHeartbeats 2000000 in
theorem vanish : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr y hy hout f₁ f₂ h₁ h₂
  classical

  have hyM : MxAt P ((B.o.resS S).symm (0, y)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right' hy _
  obtain ⟨u, hu, ⟨e, he, heu⟩, hψu⟩ := step3 D k ι p I P hP ψ hψ B.V₀ S M LS hM hLS _ hyM hout
  set h := (B.o.resS S u).2 with hh
  have hhN : (B.o.resS S).symm (0, h) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    _root_.GlobalTheory.LineProj.lineProj_mem_latO D k ι p I P hP n' ρ B S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) u hu
  have hhalf : IsHalf e h := isHalf_mul_right heu _
  have hhmx : MxAt P h := by
    have := ((_root_.GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).1 hhN).1
    have h2 : (B.o.resS S ((B.o.resS S).symm (0, h))).2 = h := by rw [AddEquiv.apply_symm_apply]
    rw [← h2]; exact mxAt_mul_right' this _
  have hpair : symplO B.V₀ S ((B.o.resS S).symm (0, h)) ((B.o.resS S).symm (0, y)) =
      symplO B.V₀ S u ((B.o.resS S).symm (0, y)) := by
    rw [B.o.symplO_resS, B.o.symplO_resS S u, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.SplitScalar.symplO_zero_right, GlobalTheory.SplitScalar.symplO_zero_right]

  obtain ⟨x', hkx, hxmx, hxhalf⟩ := _root_.GlobalTheory.LinkKapInv.kappa_inv D ρ B B'.L B'.ζ l S P h
  have hx'N : (B'.o.resT S).symm (0, x') ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P := by
    rw [_root_.GlobalTheory.KappaLat.kappa_line_lat_iff D k ι p I P hP n' n'' ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x' (hxmx hhmx), hkx]
    exact hhN
  have hx'half : IsHalf (cA D e) ((B'.o.resT S).symm (0, x')) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (hxhalf e hhalf)
  have hf₂ : heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x')) f₂ = f₂ :=
    h₂.2.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) _ hx'N hx'half
  have hf₁ : heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x')) f₁ = f₁ := by
    rw [hkx]
    exact h₁.2.2 e he _ hhN (by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]; exact isHalf_mul_right hhalf _)
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt' hyM) h₁.1
  have hmove := _root_.GlobalTheory.Unf.ContrHeis.contr_heisO D ψ hψ ρ σ B B' l S vL _ f₂ hth h₂.1 x'
  rw [hf₂, GlobalTheory.SplitScalar.heisO_comm, hf₁, contr_smul_left', hkx, hpair] at hmove
  set C := GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂
  have : (ψ (symplO B.V₀ S u ((B.o.resS S).symm (0, y))) - 1) • C = 0 := by
    rw [sub_smul, hmove, one_smul, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψu)

end GlobalTheory.FinPl.LineVanish
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Rebase
open ValuativeRel

theorem mem_grpAt_of_bc {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V) (hh : h ∈ GfC V)
    (κ : GL (Fin n) (EF D)) (hκ : finM V hn h = κ.1)
    (hoff : ∀ v, ¬ P v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) κ = 1) : h ∈ GlobalTheory.FinPl.grpAt V P := by
  subst hn
  refine (GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V P h).2 fun i j => ⟨(GlobalTheory.FinPl.SetCut.mem_GfC_iff_entries V h).1 hh i j, fun w hw => ?_⟩
  have e1 : Formalism.UG.prV (E := D.host.E) w (κ.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun g => g.1 i j) (hoff w hw)
  rw [← hκ, GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at e1
  have e2 : Formalism.UG.prV (E := D.host.E) w (toEAf D ((Formalism.L2.Theta.mt V h - 1) i j)) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_sub, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e3 := (GlobalTheory.StabOff.prV_comm w (finPart D ((Formalism.L2.Theta.mt V h - 1) i j))).symm.trans e2
  exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).1 e3

theorem pr_mem_of_intAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P) {x : D.host.E}
    (hx : Formalism.L2.Col.IntAt P x) : q.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨r, s, hs, e⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have h1 := not_not.1 (mt (GlobalTheory.PhiOneVal.mem_prime_iff_pr_inv_notMem q P hP s hs0).2 hs)
  have e' : x = (r : D.host.E) * (s : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hsE, mul_comm]
    exact e
  rw [e', map_mul, map_mul]
  exact mul_mem (GlobalTheory.LocMod.FullLatFrame.pr_int_mem q r) h1

theorem map_pr_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (h : GA D V) (r : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E))
    (hr : ∀ i j, adAt D.host.F P (finM V hn h i j) = algebraMap D.host.E _ (r (Pi.single j 1) i))
    {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : GlobalTheory.LocMod.Frame k V.rank Y) (hF : IsStdFr pos F) (e : Y ≃ Fin n)
    (he : GlobalTheory.SymBridge.IsOrd pos e) :
    (Formalism.L2.Theta.mt V h).map q.pr = F.β * GlobalTheory.SymBridge.toLoc (q.pr.comp (incA D)) e e r * F.γ := by
  subst hn
  obtain ⟨e', he', hF⟩ := hF
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  refine Matrix.ext fun c d => ?_
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std _ e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e hF]
  have h1 := hr (e c) (e d)
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at h1
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P hP _ _ h1

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) :
    Function.Surjective (toHom S T hS hT) := fun x =>
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' x), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

open _root_.Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge

theorem disjoint_vT (hI : I.Ok) (u : B.Word) (b : I.ι) : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup b)) := by
  refine Finset.disjoint_left.2 fun P h1 h2 => ?_
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h3 := (GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup b) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem P (Finset.mem_union_left _ h1)).2.2.2.2 h1
  refine GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P ?_ ?_
  · rcases Finset.mem_union.1 h2 with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (I.Q_subset_SQ b h)
  · show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
    rw [map_natCast]
    exact h3







set_option maxHeartbeats 1000000 in
theorem dead_moved (hI : I.Ok) {b : I.ι} {Ch₀ Ch : ℕ → Type} {A A' : TwDat I l Z u b Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hl : A.Live ι)
    (hb : A'.b0 = A.b0) (hne : ∀ i, i + 1 ≠ B.R.m → A'.p0 i = A.p0 i)
    (heq : ∀ i, i + 1 = B.R.m → ∀ β, (A'.p0 i β).1.1.deco = (A.p0 i β).1.1.deco ∧ cosetIn (A'.p0 i β) = cosetIn (A.p0 i β)) :
    A'.Live ι := by
  refine ⟨hl.inj, hl.first, hl.last, fun j hj γ hγ α z => ?_⟩
  by_cases h1 : j + 1 = B.R.m
  · refine absurd ?_ hγ
    have : ∀ k, k = B.R.m → Function.Surjective (ι k) := by
      rintro _ rfl
      exact hl.last
    exact this _ h1 γ
  by_cases h2 : j + 2 = B.R.m
  swap
  · have h := hl.dead j hj γ hγ α z
    unfold TwDat.xi at h ⊢
    rw [hb, hne j h1, hne (j + 1) h2]
    exact h
  have hL : (I.idx b).Ok I.Ch I.sel (I.tup b) (I.cst b) I.glob j := by
    have := hI.idx_ok b
    rwa [show B.R.m - 2 = j by omega] at this
  obtain ⟨hd, hc⟩ := heq (j + 1) h2 γ
  have key := GlobalTheory.CplDead.xiCpl1_eq_zero_of_frames I.Ch I.sel (I.tup b) (I.cst b) (I.idx b) I.glob j hL u (disjoint_vT hI u b)
    ((A.b0 j α).get (by omega)) (A.p0 j α).1.1 (A.p0 (j + 1) γ).1.1 (A'.p0 (j + 1) γ).1.1 (A.p0 (j + 1) γ).1.2 (A'.p0 (j + 1) γ).1.2 hd
    (GlobalTheory.AdForm.Rebase.repY_cong h2 _ _ hc) (fun x => ?_)
  · unfold TwDat.xi
    rw [hb, hne j h1]
    unfold xiAt
    rw [dif_neg (by omega), dite_eq_left h2]
    exact (congrArg B.embLL (key _)).trans (map_zero _)
  · obtain ⟨z', hz'⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) x
    have h := hl.dead j hj γ hγ α z'
    unfold TwDat.xi xiAt at h
    rw [dif_neg (by omega), dite_eq_left h2] at h
    subst hz'
    exact (map_eq_zero_iff _ B.embLL.injective).1 h


end GlobalTheory.Fam.Rebase

namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase


end GlobalTheory.Fam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam

theorem conv_single_one_of_forall {G : Type} [Monoid G] (l : List (G →₀ ℂ))
    (h : ∀ x ∈ l, x = Finsupp.single 1 1) : GlobalTheory.QPl.conv l = Finsupp.single 1 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x = Finsupp.single 1 1 := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    show List.foldr _ _ (x :: l) = _
    simp only [List.foldr_cons]
    change (x.sum fun g a => (GlobalTheory.QPl.conv l).sum fun h b => Finsupp.single (g * h) (a * b)) = _
    rw [hx, hl, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_mul_level {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (j : ℕ) (hj : j ≤ B.R.m) (φ : ColT I l u a j) (hφ : φ ∈ (I.fm l u a).Fi j)
    (b : Ch j) (y : (I.chain l u a).Y j) (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (γ : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hγ : γ ∈ GQ ((I.rec7 l Z).sp.X j)) (κ : A.U j b) :
    A.rd θ j hj b φ y (γ * x * κ.1) = (A.chi j b κ : ℂ) * A.rd θ j hj b φ y x := by
  obtain ⟨γ0, hγ0, c, k0, hk0, κ0, hκ0, rfl⟩ := (_root_.GlobalTheory.ChartReps.twDat_reps I hOk hP l Z u a Ch A hA j hj b).1.dec x
  have hrd := (GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ).2 b y
  let y' : (I.chain l u a).Y j := ⟨fun τ => (show Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) ℂ from infM θ _ (rankN (I.rec7 l Z) j hj) k0 τ) * y.1 τ, fun τ => by
    rw [Matrix.det_mul]; exact (GlobalTheory.AdForm.RdVal.infM_unit θ _ (rankN (I.rec7 l Z) j hj) k0 τ).mul (y.2 τ)⟩
  have hy' : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) k0) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := fun _ => rfl
  rw [hrd γ0 hγ0 c k0 hk0 ⟨κ0, hκ0⟩ y' hy']
  have e : γ * (γ0 * (A.h j b c * k0) * κ0) * κ.1 = (γ * γ0) * (A.h j b c * k0) * ((⟨κ0, hκ0⟩ : A.U j b) * κ).1 := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [e, hrd (γ * γ0) (Subgroup.mul_mem _ hγ hγ0) c k0 hk0 (⟨κ0, hκ0⟩ * κ) y' hy', map_mul, Units.val_mul]
  ring

theorem ram_iff_scalar_ram : TwRam' := by
  intro B X I hOk hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hStd j hj φ hφ
  have hlaw := rd_mul_level I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ
  have hcont : ∀ b y, IsContAut _ (A.rd θ j hj b φ y) := fun b y =>
    ⟨fun γ hγ g => by simpa using hlaw b y g γ hγ 1, _root_.GlobalTheory.AdForm.RamCont.rd_continuous I hOk hP l Z u a Ch A hA θ hθ j hj φ hφ b y⟩
  refine ⟨hcont, ?_⟩
  obtain ⟨e, he⟩ := hStd.1
  have : Finite ι := Finite.of_equiv _ e.symm
  haveI := Fintype.ofFinite ι
  have hlev := _root_.GlobalTheory.AdForm.twLev_prime I hOk hP l Z u a Ch A hA k ι p β Q L hStd (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj
  have hfix : ∀ b y i (x : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), x • Q j i = Q j i →
      rTrans ((β j i).gl x) (A.rd θ j hj b φ y) = A.rd θ j hj b φ y := by
    intro b y i x hx
    obtain ⟨hm, h1⟩ := (hlev b).1 i x hx
    funext g
    have := hlaw b y g 1 (Subgroup.one_mem _) ⟨_, hm⟩
    simpa [rTrans, h1] using this
  choose gS hgS using fun (i : ι) (s : 𝓀[k]ˣ) =>
    MulAction.exists_smul_eq (GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (Q j i) (s • Q j i)
  have hram : ∀ b y i, GlobalTheory.FinPl.RamAt (β j i) (Q j i) (A.rd θ j hj b φ y) ↔
      ∑ᶠ s, rTrans ((β j i).gl (gS i s)) (A.rd θ j hj b φ y) = 0 := by
    intro b y i
    rw [_root_.GlobalTheory.SeeSaw.ramIff_all (I.rec7 l Z) k (p i) (Fin _) _ (β j i) (Q j i) (gS i) (hgS i)]
    exact ⟨fun h => h.2.2, fun h => ⟨hcont b y, fun x hx => hfix b y i x hx, h⟩⟩
  have hdia := fun i => _root_.GlobalTheory.AdForm.diaSum_iff I hOk hP l Z u a Ch A hA θ hθ k ι p β Q L hStd j hj φ hφ i (e i) (he i) (gS i) (hgS i)
  simp only [hram]
  unfold RamT
  constructor
  · rintro ⟨-, hR⟩ b y i
    exact (hdia i).2 (fun c => hR (e i) c) b y
  · intro h
    refine ⟨hφ, fun v c => ?_⟩
    obtain ⟨i, rfl⟩ := e.surjective v
    exact (hdia i).1 (fun b y => h b y i) c

end GlobalTheory.AdForm
end
end

