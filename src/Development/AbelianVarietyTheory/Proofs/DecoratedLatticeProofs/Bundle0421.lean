module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Formalism.LocalToGlobal.Divisibility.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrueBranch

section Gen

open Formalism.L2.DIV _root_.Formalism.L2.Col

variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem cSpan_eq_VV {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

theorem det_ne_zero_of_mem_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hk)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem polOf_fnOf_frOne (G : ι → Matrix (Fin N) (Fin N) ℂ) (sh : ι → ℤ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (P : MvPolynomial (ι × Fin N × Fin N) ℂ) : Formalism.L2.Col.polOf G sh o (fnOf G sh 1 P) = P := by
  have e : (fun τ => (o.1 τ)⁻¹) = (1 : ι → Matrix (Fin N) (Fin N) ℂ) := funext fun τ => by rw [ho τ, inv_one]; rfl
  have h := Formalism.L2.Col.polOf_fnOf G sh o P
  rwa [e] at h

theorem fnOf_actP_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (P : Pol ℂ ι n) (y y' : Frames G) (h : IsTr (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) y y') :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e1 := congrFun (Formalism.L2.Col.fnOf_mul G (shiftOf lam) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) 1 P) y
  have e2 := Formalism.L2.Col.fnOf_tr (G := G) (G' := G) (shiftOf lam) 1 (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P y' y h
  have e3 : (fun τ => (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ := by
    funext τ; simp
  rw [e2, e3, e1]
  have e4 : actP lam g P = (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ.det ^ shiftOf lam τ) •
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P := by
    simp only [actP, detTwK, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose]
    simp [detPow, shiftOf, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [e4]

theorem brEqv_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (o : Frames G)
    (ho : ∀ τ, o.1 τ = 1) :
    BrEqv hN G G' lam sg (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    refine ⟨c • (Br.brStdP hN lam sg P : Pol ℂ ι n), ?_, ?_⟩
    · rw [cSpan_eq_VV]; exact (Formalism.L2.DIV.VV ℂ sg).smul_mem c (Br.brStdP hN lam sg P).2
    · simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
  · rintro k kt hk hb _ ⟨P, hP, rfl⟩ Φ' hΦ' z z' hz
    have hk0 : ∀ τ, (k τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_mem_unitary (hk τ)
    have hkt0 : ∀ τ, (kt τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose, (hb τ).det, mul_one, ← Matrix.det_transpose]; exact hk0 τ
    let g : ι → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hk0 τ)
    let g' : ι → GL (Fin N) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hkt0 τ)
    have hblk : ∀ τ, GlobalTheory.BranchFormula.IsBlock hN ((g' τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) 1 := fun τ => (hb τ).transpose
    have hPV : P ∈ Formalism.L2.DIV.VV ℂ lam := cSpan_eq_VV lam ▸ hP
    have hE := GlobalTheory.BranchFormula.brEquiv_all ℂ hN lam sg hS g g' (fun τ => hblk τ) ⟨P, hPV⟩
    have h2 : (Br.brStdP hN lam sg (actP lam g' P) : Pol ℂ ι n) = actP sg g (Br.brStdP hN lam sg P : Pol ℂ ι n) :=
      congrArg Subtype.val hE
    have hΦe : Φ' = fnOf G (shiftOf lam) 1 (actP lam g' P) := by
      funext y
      have hd : ∀ τ, IsUnit (kt τ * y.1 τ).det := fun τ => by
        rw [Matrix.det_mul]
        refine IsUnit.mul (Ne.isUnit ?_) (y.2 τ)
        rw [← Matrix.det_transpose]; exact hkt0 τ
      let y' : Frames G := ⟨fun τ => kt τ * y.1 τ, hd⟩
      rw [hΦ' y y' (fun τ => rfl), fnOf_actP_tr G lam g' P y y' (fun τ => by
        show kt τ * y.1 τ = ((kt τ)ᵀ)ᵀ * y.1 τ
        rw [Matrix.transpose_transpose])]
    rw [hΦe]
    simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
    rw [h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, fnOf_actP_tr G' sg g _ z z' (fun τ => by
      rw [hz τ]
      show k τ * z.1 τ = ((k τ)ᵀ)ᵀ * z.1 τ
      rw [Matrix.transpose_transpose])]

theorem ne_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (hc : c ≠ 0) (o : Frames G) (ho : ∀ τ, o.1 τ = 1) :
    ∃ Φ ∈ ValC G lam, (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) Φ ≠ 0 := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  have h1 := GlobalTheory.BranchFormula.onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs
  choose f hf hf0 using fun τ => (h1 N n hN (lam τ) (sg τ) (hI τ) (hS τ)).2.2.1
  have hn : ∀ τ, f τ ∈ nablaSq ℂ N (lam τ) := fun τ => by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
  have hmem : Formalism.L2.DIV.ten f ∈ Formalism.L2.DIV.VV ℂ lam := GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn
  have ht := GlobalTheory.BranchFormula.tensor ℂ ι N n hN lam sg hI hS f ⟨_, hmem⟩ hn rfl
  refine ⟨fnOf G (shiftOf lam) 1 (Formalism.L2.DIV.ten f), ⟨_, (cSpan_eq_VV lam).symm ▸ hmem, rfl⟩, fun h => ?_⟩
  simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply] at h
  have h' : (Br.brStdP hN lam sg (Formalism.L2.DIV.ten f) : Pol ℂ ι n) =
      Formalism.L2.DIV.ten fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (lam τ) (sg τ) (f τ) := ht
  rw [h', map_smul] at h
  have h0 := Formalism.L2.Col.fnOf_injective G' (shiftOf sg) 1 (fun _ => by simp) ⟨fun _ => 1, fun _ => by simp⟩
    (((smul_eq_zero.1 h).resolve_left hc).trans (map_zero _).symm)
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ hf0 h0

end Gen

section True

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {M : ℕ} {a b : DomWeight M} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_record (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem sgT_record (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  apply domWeight_ext
  funext i
  show (B.wts.sgW τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (B.wts.sgW τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

end True

section Main

theorem branching_true_columns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  intro B X I _ _ l Z u hN
  have hM := fun τ => GlobalTheory.BranchMembers.members B.fields B.Word B.R B.wts B.wts_isOk u τ
  have hI' : ∀ τ, Formalism.L2.Col.Br.Interlace hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).1
  have hS' : ∀ τ, Formalism.L2.Col.Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).2
  have hc : (∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
      (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero _).2 (l.per u I.mu0).tz_ne)
  have hlow : lowOf I l Z u = fnOf _ (shiftOf (I.perIn u I.mu0).sgT) 1 ∘ₗ
      ((∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
        (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) •
        ((Formalism.L2.DIV.VV ℂ (I.perIn u I.mu0).sgT).subtype ∘ₗ
          Formalism.L2.Col.Br.brStdP hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u I.mu0).sgT)) ∘ₗ
      Formalism.L2.Col.polOf _ (shiftOf (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩ := by
    unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]
    rfl
  refine ⟨?_, ?_, ?_, fun a z c y => ?_⟩
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]; exact hI'
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0, hlow]
    exact brEqv_formula hN _ _ _ _ hS' _ _ (fun _ => rfl)
  · rw [lamT_record I l Z u, hlow]
    exact ne_formula hN _ _ _ _ hI' hS' _ hc _ (fun _ => rfl)
  · unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u a]
    rfl

end Main

end GlobalTheory.TrueBranch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistChainLevelProductInverseScalarLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinLaw

theorem combAt_aconv {D : D7} {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) :
    ∀ l : List (WO S T →₀ ℂ), (∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) → GlobalTheory.FinPl.CombAt P (aconv l) := by
  intro l
  induction l with
  | nil =>
    intro _ u hu i j
    have h0 : aconv ([] : List (WO S T →₀ ℂ)) = Finsupp.single 0 1 := rfl
    rw [h0, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  | cons e l ih =>
    intro hl u hu
    have e1 : aconv (e :: l) = aconv [e, aconv l] := by
      apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := WO S T)
      rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_pair]
    rw [e1] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (hl e List.mem_cons_self a ha i j)
      (ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) b hb i j)

theorem comb_aconv_cons {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ)
    (l : List (WO S T →₀ ℂ)) (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  have hG0 : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have hGa : ∀ u (a b : ℂ), (a + b) • heisO ψ S T u f = a • heisO ψ S T u f + b • heisO ψ S T u f :=
    fun u a b => add_smul _ _ _
  show (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).sum
    (fun u a => a • heisO ψ S T u f) = _
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finsupp.sum_single_index (hG0 _), GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (h x hx y hy)]

theorem comb_aconv_map {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (p : Fin r → GlobalTheory.FinPl.Pl D)
    (hp : Function.Injective p) (E : Fin r → WO S T →₀ ℂ) (hE : ∀ a, GlobalTheory.FinPl.CombAt (· = p a) (E a))
    (f : WO S T → ℂ) :
    ∀ L : List (Fin r), L.Nodup → comb ψ S T (aconv (L.map E)) f = L.foldr (fun a g => comb ψ S T (E a) g) f := by
  intro L
  induction L with
  | nil => intro _; exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    intro hL
    rw [List.map_cons, comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = p a)) (P' := fun v => ∃ b ∈ L, v = p b) ?_ (hE a x hx) ?_
    · rintro _ rfl ⟨b, hb, hab⟩
      exact (List.nodup_cons.1 hL).1 (hp hab ▸ hb)
    · exact combAt_aconv _ (L.map E) (fun e he => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
        exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun v hv => ⟨b, hb, hv⟩) (hE b u hu)) y hy

theorem eQ_comb_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ Ψ, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ → ∀ i, ∃ f, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f ∧ comb c.ψ _ _ (w.eQ j) Ψ = comb c.ψ _ _ ((F.Q i).eL j) f := by
  intro D c v t w F hc hv hP j hj Ψ hΨ i
  have hI := fun P P' hd => _root_.GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hd
  have hca : ∀ a, GlobalTheory.FinPl.CombAt (· = (F.Q a).q.v) ((F.Q a).eL j) := by
    intro a u hu r q'
    have := (F.Q a).hs
    exact (GlobalTheory.FinPl.FrameLat.idem_iff (F.Q a).q _).2 (((F.Q a).eL_at j ((F.Q a).s - j) (by omega)).1 u hu r q')
  have hdisj : ∀ a b : Fin F.r, a ≠ b → ∀ p, p = (F.Q a).q.v → ¬ p = (F.Q b).q.v := fun a b hab p ha hb =>
    hab (hP.inj (ha.symm.trans hb))
  let g : Fin F.r → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((F.Q a).eL j) f
  have hfold : comb c.ψ _ _ (w.eQ j) Ψ = (List.finRange F.r).foldr g Ψ := by
    rw [hP.eQ j hj, List.ofFn_eq_map]
    exact comb_aconv_map c.ψ (fun a => (F.Q a).q.v) hP.inj (fun a => (F.Q a).eL j) hca Ψ _ (List.nodup_finRange _)
  refine ⟨((List.finRange F.r).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) Ψ :=
      GlobalTheory.GSuppComb.vac_mono (fun p hp => by rw [hp]; exact (hP.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin F.r), (∀ a ∈ l, a ≠ i) →
        GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a l ih =>
        intro hl
        exact ((hI (· = (F.Q a).q.v) (· = (F.Q i).q.v) (hdisj a i (hl a List.mem_cons_self))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange F.r).mem_erase_iff.1 ha).1
  · rw [hfold]
    exact GlobalTheory.GSuppComb.foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ
      (List.mem_finRange i)

theorem local_scalar_law : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), (ofSplit q).IsComp χS μS → (ofSplit q).IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (e : WO S T →₀ ℂ) (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → (ofSplit q).IsCombAt ψ FS FT e Φ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∀ g gk h hk, (ofSplit q).IsLoc FS g gk → (ofSplit q).IsLoc FT h hk → ∀ z : ℂ, (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ = z • Φ → ω (g, h) (comb ψ S T e f) = z • comb ψ S T e f := by
  intro D k _ _ _ _ q hU ψ ψk hψ hch hcond S T χS χT ω hω μS μT cS cT Y Y' _ _ _ _ FS FT LS LT hLS hLT hFS hFT e Φ hΦ
    hcomb f hf g gk h hk hg hh z hz
  obtain ⟨Tm, hTm, hTO⟩ :=
    (_root_.GlobalTheory.LocMod.indicator_vac D k q hU Y Y' S T FS FT ψ ψk hψ hch hcond LS LT hLS hLT hFS hFT).2 f hf
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  let Φs : SB (Matrix Y Y' k) := ⟨Φ, hΦ⟩
  have e1 : Tm Φs = comb ψ S T e f := by rw [hcomb.2 Tm hTm O Φs hO rfl, hTO O hO]
  have e2 := _root_.GlobalTheory.LocOm.omLoc D k (ofSplit q) ψ S T χS χT ω hω μS μT cS cT Y Y' FS FT Tm hTm g gk h hk hg hh Φs (z • Φs)
    (by rw [Submodule.coe_smul]; exact hz.symm)
  rw [← e1, e2, map_smul]

theorem om_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ζ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (Φ : Matrix b a k → ℂ) :
    om (μ * ζ) g h Φ = ((ζ (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (((ζ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)) • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val]
  ring

variable {D : D7}

theorem isComp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ) (h' : p.IsComp χ' μ') :
    p.IsComp (χ * χ') (μ * μ') := fun x a ha => by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Circle.coe_mul, h x a ha, h' x a ha]

theorem isComp_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) : p.IsComp χ⁻¹ μ⁻¹ := fun x a ha => by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv, h x a ha]

theorem place_law (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t)
    (hc : c.Is) (ht : t.Is) (hv : v.Is) (hP : F.Pins w) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r)
    (cc : ℕ) (hcc : j + 1 + cc = (F.Q i).s + 1) (x : GL ((F.Q i).X (j + 1) ⊕ Fin cc) (F.Q i).k)
    (hx : x ∈ ((F.Q i).T.lev (j + 1) cc hcc).J) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, (F.Q i).gl (j + 1) cc hcc x) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) ((F.Q i).gl (j + 1) cc hcc x, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) =
          a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  have hs := (F.Q i).hs
  obtain ⟨d, rfl⟩ : ∃ d, cc = d + 1 := ⟨cc - 1, by omega⟩
  have hjd : j + (d + 1) = (F.Q i).s := by omega
  have hjd' : j + 1 + d = (F.Q i).s := by omega
  obtain ⟨χz, hV, hW, hV', hW'⟩ := hP.mid j σ h
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (F.Q i).q) χz
  refine ⟨(((F.Q i).T.lev (j + 1) (d + 1) hcc).lam ⟨x, hx⟩ : ℂ) * (((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ),
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP j (by omega) Ψ₁ h₁ i
    rw [hfe]
    have hw := (t.sBF j (σ + 1) h).weil
    rw [(ht.sBF j (σ + 1) h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu j (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χV (((F.Q i).T.mu (j + 1))⁻¹ * ζ) := by
      rw [hV]; exact isComp_mul _ hmu hζ
    have cT : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χW ((F.Q i).T.mu (j + 1))⁻¹ := by
      rw [hW]; exact hmu
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY j (d + 1 + 1) (by omega)) 1 1 := by
      have := (F.Q i).gl_loc j (d + 1 + 1) (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om j) hw _ _ cS cT _ _
      ((F.Q i).FY j (d + 1 + 1) (by omega)) ((F.Q i).FY (j + 1) (d + 1) (by omega)) (v.N j) (v.N (j + 1))
      (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) ((F.Q i).latY j (d + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).eL j) ((F.Q i).T.Phi j (d + 1) hjd)
      ((F.Q i).reg.1 j (d + 1) hjd) ((F.Q i).eL_at j (d + 1) hjd) f hf 1 1 _ x h1 ((F.Q i).gl_loc _ _ _ x) _ ?_
    rw [map_one, map_one, Units.val_one, one_smul, mul_inv, inv_inv, om_twist, ((F.Q i).laws.1 j (d + 1) hjd).2 ⟨x, hx⟩,
      smul_smul]
    congr 1
    simp only [map_one, MonoidHom.inv_apply, inv_one, Units.val_one, one_mul, inv_inv, mul_inv, Units.val_inv_eq_inv_val]
    ring
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP (j + 1) (by omega) Ψ₂ h₂ i
    rw [hfe]
    have hw := (t.sFB j σ h).weil
    rw [(ht.sFB j σ h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu (j + 1) (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χV ((F.Q i).T.mu (j + 1 + 1))⁻¹ := by
      rw [hV']; exact hmu
    have cT : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χW (((F.Q i).T.mu (j + 1 + 1))⁻¹ * ζ) := by
      rw [hW']; exact isComp_mul _ hmu hζ
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY (j + 1 + 1) d (by omega)) 1 1 := by
      have := (F.Q i).gl_loc (j + 1 + 1) d (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om (j + 1)) hw _ _
      cS cT _ _ ((F.Q i).FY (j + 1) (d + 1) (by omega)) ((F.Q i).FY (j + 1 + 1) d (by omega)) (v.N (j + 1))
      (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).latY (j + 1 + 1) d (by omega)) ((F.Q i).eL (j + 1))
      ((F.Q i).T.Phi (j + 1) d hjd') ((F.Q i).reg.1 (j + 1) d hjd') ((F.Q i).eL_at (j + 1) d hjd') f hf _ x 1 1
      ((F.Q i).gl_loc _ _ _ x) h1 _ ?_
    rw [inv_inv, ((F.Q i).laws.1 (j + 1) d hjd').1 ⟨x, hx⟩, smul_smul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem inverse_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  intro D c v t w F hc ht hv _ hP j σ h k hk
  refine Subgroup.iSup_induction (fun i => GlobalTheory.QuotientFiniteLevel.locK F j σ h i)
    (C := fun k => ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)
    (show k ∈ ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i from hk) ?_ ?_ ?_
  · intro i k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hk
    exact place_law D c v t w F hc ht hv hP j σ h i _ _ x hx
  · refine ⟨1, one_ne_zero, fun Ψ₁ Ψ₂ _ _ => ⟨?_, ?_⟩⟩
    · rw [show ((1 : GA D (c.V j)), (1 : GA D (c.V (j + 1)))) = 1 from rfl, map_one, inv_one, one_smul]; rfl
    · rw [show ((1 : GA D (c.V (j + 1))), (1 : GA D (c.V (j + 1 + 1)))) = 1 from rfl, map_one, one_smul]; rfl
  · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_ne_zero ha hb, fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
    · have e : ((1 : GA D (c.V j)), x * y) = (1, x) * (1, y) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).1, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).1, smul_smul, mul_inv,
        mul_comm b⁻¹]
    · have e : (x * y, (1 : GA D (c.V (j + 1 + 1)))) = (x, 1) * (y, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).2, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).2, smul_smul, mul_comm b a]

end GlobalTheory.QFinLaw
end
end

