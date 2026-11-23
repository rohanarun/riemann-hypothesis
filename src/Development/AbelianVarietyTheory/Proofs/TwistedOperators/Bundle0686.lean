module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastMulUnitaryAdelicGroupOfEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLaw

section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]

theorem adForms_law (ι : Γg →* Gg) (ρ : Γg →* Module.End ℂ Wg) (J : Subgroup Gg) (χ : J →* ℂˣ) {F : Gg → Wg}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : Gg) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  have e := hF 1 h k
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at e

end Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}

theorem cast_mul_unitaryAdelicGroup_of_eq {X Y : LSp D} (h : X = Y) (a b : GA D X.sp) :
    cast (congrArg (fun X : LSp D => GA D X.sp) h) (a * b) =
      cast (congrArg (fun X : LSp D => GA D X.sp) h) a * cast (congrArg (fun X : LSp D => GA D X.sp) h) b := by
  subst h; rfl

theorem toXf_mul (y k : FinPt G (.grid 0 D.R.m)) : toXf (y * k) = toXf y * toXf k := by
  unfold toXf
  rw [← map_mul, Subgroup.coe_mul]
  exact congrArg _ (cast_mul_unitaryAdelicGroup_of_eq (colY_m R.toLevCh) _ _)

theorem formC_apply (S : SumChoice W U) (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) :
    S.formC t u y = S.co ((R.HX t).e u (toXf y)) := rfl

theorem formC_mul (S : SumChoice W U) (hHX : R.models_HX) (t : T) (u : (R.HX t).H) (y k : FinPt G (.grid 0 D.R.m))
    (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) :
    S.formC t u (y * k) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.formC t u y := by
  have h : ∀ F, F ∈ LinearMap.range (R.HX t).e → F ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
      (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ := fun F hF => (hHX t).2.1 ▸ hF
  have e : (R.HX t).e u (toXf y * toXf k) =
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y) :=
    adForms_law (Bridge.ratF D.sp.X') _ _ _ (h _ (LinearMap.mem_range_self (R.HX t).e u)) (toXf y) ⟨toXf k, hk⟩
  calc S.formC t u (y * k) = S.co ((R.HX t).e u (toXf (y * k))) := formC_apply S t u (y * k)
    _ = S.co ((R.HX t).e u (toXf y * toXf k)) := congrArg (fun z => S.co ((R.HX t).e u z)) (toXf_mul y k)
    _ = S.co ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y)) := congrArg S.co e
    _ = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.co ((R.HX t).e u (toXf y)) := S.co.map_smul _ _
    _ = _ := congrArg _ (formC_apply S t u y).symm

end GlobalTheory.FirstRowLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellMassesAgainstLevelVolumesLargeDepth
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem wtAt_big : Big fun ch => ∀ s, WtAt ch s := by
  refine GlobalTheory.RowReal.big_mono ?_ (_root_.GlobalTheory.TermScales.exists_scales.and _root_.GlobalTheory.CellMass.cell_mass)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH
  obtain ⟨hA, hC⟩ := h
  have hc := hC s ρ μ hH
  classical
  let cf : ℕ → ℂ := fun j => if hj : j ∈ idx D then (hc j hj).choose else 1
  refine ⟨((idx D).map cf).prod, fun t Φ β b hb M M' hM hM' => ?_⟩
  obtain ⟨x, hx, hx1⟩ := hA t Φ β M M' hM hM'
  refine ⟨x, hx, ?_⟩
  have hlt : ∀ j ∈ idx D, 1 ≤ j ∧ j + 2 ≤ D.R.m := fun j hj => by
    rw [idx, List.mem_range'_1] at hj; omega
  have hgf : ∀ j ∈ idx D, b j ∈ GfC _ := fun j hj => by
    obtain ⟨δ, r, -, -, hf⟩ := hb.2 j hj (by have := hlt j hj; omega)
    exact hf.1
  have hfac : ∀ j ∈ idx D, (if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩ else 0) *
      ((x (.top j) : ℝ) : ℂ) = cf j * (colCoef ch t β j : ℂ) := fun j hj => by
    rw [dif_pos (hgf j hj)]
    have hs := hx (.top j) (show j ≤ D.R.m by have := hlt j hj; omega) (by simp only [ne_eq, Node.top.injEq]; have := hlt j hj; omega)
    have e := (hc j hj).choose_spec t Φ β b hb M M' hM hM' (x (.top j)) hs (hgf j hj)
    simp only [cf, dif_pos hj]
    exact e
  have hsP : sProd D x = ((idx D).map fun j => ((x (.top j) : ℝ) : ℂ)).prod := by
    have h2 : ∏ i ∈ Finset.range (D.R.m + 1), ((x (.grid i D.R.m) : ℝ) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [hx1 (.grid i D.R.m) ⟨by simp at hi; omega, rfl⟩ (by simp) (fun j _ => by simp)]
      simp
    rw [sProd, h2, mul_one, ← List.prod_toFinset _ (show (idx D).Nodup from List.nodup_range')]
    symm
    refine Finset.prod_subset (fun j hj => ?_) (fun j hj0 hj => ?_)
    · rw [List.mem_toFinset] at hj
      have := hlt j hj
      exact Finset.mem_range.2 (by omega)
    · rw [List.mem_toFinset] at hj
      have hj1 := Finset.mem_range.1 hj0
      rw [hx1 (.top j) (show j ≤ D.R.m by omega) (by simp only [ne_eq, Node.top.injEq]; omega) (fun j' hj' e => by cases e; exact hj hj')]
      simp
  have hwt : GlobalTheory.RowVal.wt ρ μ b = ((idx D).map fun j => if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩
      else 0).prod := by
    unfold GlobalTheory.RowVal.wt
    congr 1
  rw [hwt, hsP, ← List.prod_map_mul, List.map_congr_left hfac, List.prod_map_mul, coef_prod]

end GlobalTheory.RowWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem suppAt_conj {V : HSp D} {e : AE D} {y : GA D V} (h : SuppAt e V y) (δ : GA D V) : SuppAt e V (δ * y * δ⁻¹) := by
  have hs : (e + cA D e) • (mt V y - 1) = mt V y - 1 := Matrix.ext fun i j => h i j
  have hδ : mt V δ * mt V δ⁻¹ = 1 := by rw [← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one]
  have key : mt V (δ * y * δ⁻¹) - 1 = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hδ]
  have h2 : (e + cA D e) • (mt V δ * (mt V y - 1) * mt V δ⁻¹) = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasLoc_conj (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m) {y : GA D (G.V (.grid D.R.m j))}
    {g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)} (h : HasLoc t B hj y g)
    (δ : GA D (G.V (.grid D.R.m j))) :
    HasLoc t B hj (δ * y * δ⁻¹) (fun w => locAt B t w.1 j hj δ * g w * (locAt B t w.1 j hj δ)⁻¹) := by
  obtain ⟨e, he, hs, hl⟩ := h
  refine ⟨e, he, suppAt_conj hs δ, fun w => ?_⟩
  change locAt B t w.1 j hj (δ * y * δ⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => locAt B t w.1 j hj δ * z * (locAt B t w.1 j hj δ)⁻¹) (hl w)

theorem conj_rowR' {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} (hy : ∃ f, (toFrame hs hj y).val = diagonal f) (hx : x ∈ rowR hs hj) :
    y * x * y⁻¹ ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have hy' : ∃ f, (toFrame hs hj y⁻¹).val = diagonal f :=
    ⟨Ring.inverse f, by rw [map_inv, Matrix.coe_units_inv, hf, Matrix.inv_diagonal]⟩
  have := conj_rowR hs hj (g := fun _ => 1) hy' hx
  have e1 : GlobalTheory.SplitFlip.diagGL (fun _ => (1 : kˣ)) = (1 : GL (Fin (Γ.rank (Γ.m, j))) k) :=
    Units.ext (by rw [GlobalTheory.SplitFlip.diagGL_val]; exact diagonal_one)
  rwa [e1, mul_one, inv_inv] at this

theorem sgn_diag {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    (c : Fin (Γ.rank (Γ.m, j)) → kˣ) : ∃ f, (toFrame hs hj (GlobalTheory.SplitFlip.diagGL c)).val = diagonal f := by
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact ⟨_, submatrix_diagonal_equiv (fun i => (c i : k)) (frame h)⟩

end GlobalTheory.RowLift


open GlobalTheory.RowLift GlobalTheory.RowRep in
theorem GlobalTheory.RowLift.lift_rowR : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  obtain ⟨C1, hJ⟩ := GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices
  obtain ⟨C2, hB⟩ := GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hx1⟩ := hJ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, hx2⟩ := hB ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  intro s t j hjI hj hj' δ hδ l hl
  obtain ⟨y, hy⟩ := exists_hasLoc hS.core.lev ch.S.B t hj (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹)
  refine ⟨y, hy, ?_⟩
  have hc := hasLoc_conj ch.S.B t hj hy δ
  have hm : ∀ w : locPl ch.G t, locAt ch.S.B t w.1 j hj δ * (sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) *
      (locAt ch.S.B t w.1 j hj δ)⁻¹ ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj' := fun w =>
    conj_rowR' one_le_sLen hj' (locAt_tilt ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' hδ)
      (conj_rowR' one_le_sLen hj' (sgn_diag one_le_sLen hj' _) (hl w))
  unfold rowGrp
  split_ifs with h1 h2
  · exact hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' _
      (by have := (idx_le hjI); omega) _ _ hc hm
  · exact hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' h2 _ _ hc hm
  · exfalso; have := idx_le hjI; omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantParabolicBasePoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem pairVec_move (S : GridChoice W U) {t : T} (fs : Vecs G t) (hf : IsThetaFunO W.ψ _ _ (fs first))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)) :
    pairVec S (Function.update x 0 (x 0 * k)) y fs =
      pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) := by
  have hj : ∀ j, (if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    intro j
    by_cases h : j < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      rcases j with _ | j
      · have e1 : Function.update x 0 (x 0 * k) 0 = x 0 * k := Function.update_self _ _ _
        have e2 : Function.update x 0 (x 0 * k) (0 + 1) = x (0 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨0, h⟩) =
            W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (fs first) :=
          Function.update_self _ _ _
        rw [e1, e2, e3]
        unfold kkVec
        have e4 : x 0 * k * S.N.u (Pair.small (.top t 0)) =
            (x 0 * S.N.u (.top 0)) * ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) := by group
        rw [e4, GlobalTheory.KerTrans.fockComp_mul_fin W _ (p := .top t 0) (show (Pair.top t 0 : Pair T).InRange D.R.m from
          show 1 ≤ D.R.m by have := D.R.two_le_m; omega) (fs (.inl ⟨0, h⟩)) hf]
        rfl
      · have e1 : Function.update x 0 (x 0 * k) (j + 1) = x (j + 1) := Function.update_of_ne (by omega) _ _
        have e2 : Function.update x 0 (x 0 * k) (j + 1 + 1) = x (j + 1 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j + 1, h⟩) = fs (.inl ⟨j + 1, h⟩) :=
          Function.update_of_ne (by simp [first]) _ _
        rw [e1, e2, e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hcol : colV S fs (Function.update x 0 (x 0 * k)) =
      colV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) x := by
    have hfam : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (fun j => if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) :=
      funext hj
    unfold colV
    rw [hfam]
  have hri : ∀ i, (if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    intro i
    by_cases h : i < D.R.m
    · rw [dite_eq_left h, dite_eq_left h]
      have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩) = fs (.inr ⟨i, h⟩) :=
        Function.update_of_ne (by simp [first]) _ _
      rw [e3]
    · rw [dite_eq_right h, dite_eq_right h]
  have hrow : rowV S fs y = rowV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) y := by
    have hfam : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := funext hri
    unfold rowV
    rw [hfam]
  unfold pairVec
  rw [hcol, hrow]

theorem pairPts_update_top_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc ht hβ hτ hv Ψ F hΨ x y k hk
  have hk' : finG (G.V (.top 0)) k ∈ G.Kplus := hk
  rw [hΨ _ _ hk', pairPts_eq, pairPts_eq]
  have hth : ∀ d ∈ τ.support, ∀ l, IsThetaFunO W.ψ _ _ (vecsOf S d l) := fun d hd l => by
    rcases l with j | i
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .top t j) (show DefPair D.R.m (Pair.top t (j : ℕ)) from j.2) _ ((hv d hd).1 j)
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) _ ((hv d hd).2 i)
  have hp0 : (Pair.top t 0 : Pair T).InRange D.R.m := show 1 ≤ D.R.m by have := D.R.two_le_m; omega
  have hmv : ∀ d ∈ τ.support, ∀ l,
      IsThetaFunO W.ψ _ _ (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l) := by
    intro d hd l
    by_cases hl : l = first
    · subst hl
      have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) first =
          W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (vecsOf S d first) :=
        Function.update_self _ _ _
      rw [e]
      exact (W.om_is _ hp0).om_pres _ _ (hth d hd first)
    · have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l = vecsOf S d l :=
        Function.update_of_ne hl _ _
      rw [e]
      exact hth d hd l
  calc (τ.sum fun d a => a * pairVec S (Function.update x 0 (x 0 * k)) y (vecsOf S d) (Ψ (x 0)) (F (y 0)))
      = τ.sum fun d a => a * pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d))
          (Ψ (x 0)) (F (y 0)) :=
        Finset.sum_congr rfl fun d hd => by dsimp only; rw [pairVec_move S _ (hth d hd first)]
    _ = τ.sum fun d a => a * pairVec S x y (vecsOf S d) (Ψ (x 0)) (F (y 0)) :=
        GlobalTheory.TopZeroInv.pairVec_sum_eq_of_prod_eq S τ _ _ x y _ _ hmv hth (GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus S ht hL hq hc ht hβ hτ hv k hk')

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPureTensor_product_expansion_all_places : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  first | exact @GlobalTheory.LocAsm.oneProduct | exact GlobalTheory.LocAsm.oneProduct | (intros; apply GlobalTheory.LocAsm.oneProduct <;> assumption)
end

