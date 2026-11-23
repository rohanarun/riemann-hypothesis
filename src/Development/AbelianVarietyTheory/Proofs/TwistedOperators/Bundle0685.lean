module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0683
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0684
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0675
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselPiecesMutualAnnihilators
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStep
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoreChainCompositesExistLiftCombinationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_chain_composites_exist_lift_combinations : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → DepFixed → CoreModels → ChainEx := by
  first | exact @GlobalTheory.ChainLifts.chainEx | exact GlobalTheory.ChainLifts.chainEx | (intros; apply GlobalTheory.ChainLifts.chainEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelBis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowVertexInv

theorem pairPts_update_row : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc hU hβ hτ hv Ψ F x y i hi him k hk
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hF : Function.update y (j + 1) (y (j + 1) * k) 0 = y 0 := Function.update_of_ne (by omega) _ _
  rw [hF, pairPts_eq_sum, pairPts_eq_sum]
  have hth : ∀ d ∈ τ.support, ∀ a, vecOf S d a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    cases a with
    | inl j' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .top t j') (by show (j' : ℕ) + 1 ≤ D.R.m; omega) _ ((hv d hd).1 j')
    | inr i' => exact GlobalTheory.RowVertexInv.vec_mem_thetaSub S (p := .chi i' D.R.m) ⟨by omega, rfl⟩ _ ((hv d hd).2 i')
  have e1 : (τ.sum fun d c => c • pairFn S x (Function.update y (j + 1) (y (j + 1) * k)) (vecOf S d)) =
      τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d)) :=
    Finsupp.sum_congr fun d hd => by rw [GlobalTheory.RowVertexInv.pairFn_update_moveV S x y j him k _ (hth d hd)]
  rw [e1]
  have hmv : ∀ d ∈ τ.support, ∀ a, moveV S j him k (vecOf S d) a ∈
      thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) := by
    intro d hd a
    have h1 : (Pair.chi j D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have h2 : (Pair.chi (j + 1) D.R.m : Pair T).InRange D.R.m := ⟨by omega, le_rfl⟩
    have upd : ∀ (P : ∀ a, FactorFn G t a → Prop) (f : ∀ a, FactorFn G t a) (a' : Fin D.R.m ⊕ Fin D.R.m) (v' : FactorFn G t a'),
        (∀ a, P a (f a)) → P a' v' → ∀ a, P a (Function.update f a' v' a) := by
      intro P f a' v' hf hv' a
      by_cases h : a = a'
      · subst h; simpa using hv'
      · rw [Function.update_of_ne h]; exact hf a
    exact upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _
      (upd (fun a f => f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) _ _ _ (hth d hd)
        ((W.om_is _ h1).om_pres _ _ (hth d hd (.inr ⟨j, by omega⟩))))
      ((W.om_is _ h2).om_pres _ _ (hth d hd (.inr ⟨j + 1, him⟩))) a
  let V := fun a : Fin D.R.m ⊕ Fin D.R.m => thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))
  let M : MultilinearMap (RingHom.id ℂ) (fun a => ↥(V a)) (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ) :=
    MultilinearMap.mk' (fun v => pairFn S x y fun a => (v a : FactorFn G t a))
      (fun v a f g => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_add]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f g f.2 g.2).1)
      (fun v a c f => by
        have e : ∀ w : V a, (fun b => ((Function.update v a w b : V b) : FactorFn G t b)) =
            Function.update (fun b => (v b : FactorFn G t b)) a (w : FactorFn G t a) := fun w => by
          funext b; exact Function.apply_update (fun b (w : V b) => (w : FactorFn G t b)) v a w b
        simp only [e, Submodule.coe_smul]
        exact (GlobalTheory.RowVertexInv.pairFn_update_linear S x y _ (fun b => (v b).2) a f f f.2 f.2).2 c)
  classical
  let φ : PureDat G t → ∀ a, V a := fun d =>
    if hd : d ∈ τ.support then fun a => ⟨moveV S j him k (vecOf S d) a, hmv d hd a⟩ else 0
  let φ' : PureDat G t → ∀ a, V a := fun d => if hd : d ∈ τ.support then fun a => ⟨vecOf S d a, hth d hd a⟩ else 0
  have key := GlobalTheory.finsupp_sum_multilinear_eq_of_prod_eq V M τ τ φ φ' (fun z => by
    refine (Finsupp.sum_congr fun d hd => ?_).trans ((_root_.GlobalTheory.RowVertexInv.sum_prod_moveV_eq S hL hq hc hU hβ hτ hv j him k hk z).trans (Finsupp.sum_congr fun d hd => ?_))
    · simp only [φ, dif_pos hd]
    · simp only [φ', dif_pos hd])
  have l1 : (τ.sum fun d c => c • pairFn S x y (moveV S j him k (vecOf S d))) = τ.sum fun d c => c • M (φ d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ, dif_pos hd, MultilinearMap.mk'_apply]
  have l2 : (τ.sum fun d c => c • pairFn S x y (vecOf S d)) = τ.sum fun d c => c • M (φ' d) :=
    Finsupp.sum_congr fun d hd => by simp only [M, φ', dif_pos hd, MultilinearMap.mk'_apply]
  rw [l1, l2, key]

end GlobalTheory.RowVertexInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantLastVertexLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pairing_invariant_last_vertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) →
    (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) →
    t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.LastVertexInv.pairPts_last_invariant | exact GlobalTheory.LastVertexInv.pairPts_last_invariant | (intros; apply GlobalTheory.LastVertexInv.pairPts_last_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowDatum

private theorem prod_apply_update_eq_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (F : ∀ i, X i → ℂ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, F i (Function.update x j y i) = F j y * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (s : Finset ι) :
    ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert j s hj ih =>
    intro x

    have hg : (∑ d ∈ S, (c d * ∏ i ∈ Finset.univ.erase j,
        (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i)) • Φ d j) = 0 := by
      funext y
      rw [Finset.sum_apply, Pi.zero_apply, ← ih (Function.update x j y)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [prod_apply_update_eq_mul_prod_erase (fun i => if i ∈ s then Tm i (Φ d i) else Φ d i) x j y]
      simp only [Pi.smul_apply, smul_eq_mul, if_neg hj]
      ring

    have hT := congrArg (fun g => Tm j g (x j)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hT
    rw [← hT]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h2 : ∏ i ∈ Finset.univ.erase j, (if i ∈ insert j s then Tm i (Φ d i) else Φ d i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [Finset.mem_insert, hij, false_or]
    rw [h2, if_pos (Finset.mem_insert_self j s)]
    ring

theorem sum_prod_map_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (x : ∀ i, X i) :
    ∑ d ∈ S, c d * ∏ i, Tm i (Φ d i) (x i) = 0 := by
  have := sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero Tm S c Φ h Finset.univ x
  simpa using this

theorem sum_prod_map_eq_zero₂ {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ j, X j → ℂ) (Ψ : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) = 0)
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) = 0 := by

  have hx : ∀ (y : ∀ i, Y i) (x : ∀ j, X j),
      ∑ d ∈ S, (c d * ∏ i, Ψ d i (y i)) * ∏ j, TX j (Φ d j) (x j) = 0 := by
    intro y
    refine sum_prod_map_eq_zero TX S (fun d => c d * ∏ i, Ψ d i (y i)) Φ (fun x => ?_)
    rw [← h x y]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

  have hy := sum_prod_map_eq_zero TY S (fun d => c d * ∏ j, TX j (Φ d j) (x j)) Ψ (fun y' => by
    rw [← hx y' x]
    exact Finset.sum_congr rfl fun d _ => by ring) y
  rw [← hy]


end GlobalTheory.FirstRowDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepPiecesAdmissibleSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem piecesFB_is_and_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), (pcFB W F σ h h').Is (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ ∧ Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨f1, f2, f3, f4⟩ := _root_.GlobalTheory.AscFin.pcFB_fin D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨g1, g2, g3⟩ := _root_.GlobalTheory.AscFin.AnnPieces.pcFB_dualA D hq T L μ0 hL sc G W M hM F hF σ h h'
  obtain ⟨b1, b2⟩ := _root_.GlobalTheory.AscFin.DualParts.pcFB_dual D hq T L μ0 hL sc G W M hM F hF σ h h'
  exact ⟨⟨f1, g1, f2, f3, g2, g3, b1, b2, _root_.GlobalTheory.UniStepFB.psiUni_pcFB D hq T L μ0 hL sc G W M hM F hF σ h h', f4, _root_.GlobalTheory.AscFin.PcFBVac.pcFB_vac D hq T L μ0 hL sc G W M hM F hF σ h h'⟩,
    _root_.GlobalTheory.AscFin.SplitsFB.splits_FB D hq T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem exists_idemSum_singleton : ∀ {D : D7} (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ w ∈ P, ∃ e' : AE D, IsIdemSum e' {w} := fun e P he w hw =>
  (GlobalTheory.IdemFlip.idemSum_sub_and_flip _ e P {w} he (Finset.singleton_subset_iff.2 hw)).1

theorem oneProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_) ((GlobalTheory.T.rowData_localPureTensors_largeDepth.and GlobalTheory.T.flatTensor_rowFactor_largeDepth).and (_root_.GlobalTheory.LocAsm.colFlat_expansion.and GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion))
  obtain ⟨⟨hR, hF⟩, hL, hC⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd fr hfd hfr
  obtain ⟨dr, cr, hdr, hcr, hdrfn⟩ := hR t e he φ fr hfr
  have heL : ∀ w : locPl ch.G t, ∃ eL, IsIdemSum eL {w.1} := fun w => exists_idemSum_singleton e _ he w.1 w.2
  choose eL heL using heL
  have hloc := fun w : locPl ch.G t => hL t β w (eL w) (heL w) (φ w) (hφ w)
  choose I S x d c hdc hexp using hloc
  obtain ⟨J, SJ, xJ, dJ, cJ, hJ, hJexp, hJev⟩ :=
    hC s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  let key : J → PureDat ch.G t × Combs ch.G := fun a => ((dJ a, dr), (cJ a, cr))
  have hsum : ∀ F : PureDat ch.G t × Combs ch.G → ℂ,
      ((∑ a ∈ SJ, Finsupp.single (key a) (xJ a)).sum fun k x => x * F k) = ∑ a ∈ SJ, xJ a * F (key a) := by
    intro F
    rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finset.sum_congr rfl fun a _ => Finsupp.sum_single_index (zero_mul _)
  refine ⟨∑ a ∈ SJ, Finsupp.single (key a) (xJ a), ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, hk'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hk)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hk')]
    exact ⟨fun j => hJ a ha j, fun n => hdr n⟩
  · intro u y hu hy
    rw [hsum]
    have hrow : ∏ n, (dr n).fn (y n) = ∏ n : Fin D.R.m, ∏ w : locPl ch.G t, φ w (.ex n D.R.m)
        (ch.S.B.coord t w.1 (X := (n, D.R.m)) (Y := (n + 1, D.R.m)) ⟨n.2.le, le_rfl⟩ ⟨n.2, le_rfl⟩
          ((y n).map fun a => cpt w.1 (toEAf D a))) :=
      Finset.prod_congr rfl fun n _ => hdrfn n (y n) (hy n)
    calc (∑ a ∈ SJ, xJ a * ((∏ j, ((key a).1.1 j).fn (u j)) * ∏ n, ((key a).1.2 n).fn (y n)))
        = (∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j)) * ∏ n, (dr n).fn (y n) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by simp only [key]; ring
      _ = _ := by
          rw [hJexp u hu, hrow, Finset.prod_comm, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun w _ => (hF t β w (φ w) (hφ w) u y).symm
  · intro P p hp u y
    rw [hsum]
    have hev : ∀ (C : BiFam ch.G) (f : SchRow ch.G), evT C f u y = evT C 1 u 0 * ∏ i, f i (y i) := by
      intro C f
      simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one]
    have hcomb : ∀ a (C₀ : BiFam ch.G), evT (combC ch.W (key a).2 C₀) (combR ch.rm (key a).2) u y =
        evT (combC ch.W (cJ a, 0) C₀) 1 u 0 * ∏ i, fr i (y i) := by
      intro a C₀
      rw [hev]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by simp only [key, combR, hcr i]
    rw [hev, hJev P p hp u, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [hcomb a]; ring

end GlobalTheory.LocAsm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalLatticeMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m)
    (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ besGrp (besDecAt ch.G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  first | exact @GlobalTheory.RowLiftBes.mem_besGrp_of_hasLoc | exact GlobalTheory.RowLiftBes.mem_besGrp_of_hasLoc | (intros; apply GlobalTheory.RowLiftBes.mem_besGrp_of_hasLoc <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingCellMassEqConstMulLocalCoefficients
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CellMass


set_option maxHeartbeats 1600000 in
theorem cell_mass : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ)
    (ρ : ∀ j, Measure ((rowGrp ch.G j).subgroupOf (GfC _))) (μ : ∀ j, Measure (GfC (ch.G.V (.grid D.R.m j)))),
    (∀ j ∈ idx D, (ρ j).IsHaarMeasure ∧ (μ j).IsHaarMeasure) → ∀ j ∈ idx D, ∃ c : ℂ, ∀ t Φ β b, IsRep t ch.S.B s β b →
      ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' → ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) →
        ∀ hb : b j ∈ GfC _, cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, hb⟩ * ((x : ℝ) : ℂ) =
          c * (GlobalTheory.RowWt.colCoef ch t β j : ℂ) := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and _root_.GlobalTheory.CellMass.cell_fubini (Big.and _root_.GlobalTheory.CellLevel.pr_vol GlobalTheory.T.exists_haar_volume_of_conjugate_lattice))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH j hj
  obtain ⟨hA, hB, hC⟩ := h
  obtain ⟨κ, la, ν, hκ, hla, hν, hAeq⟩ := hA j hj (ρ j) (hH j hj).1
  obtain ⟨κ', hκ', hBeq⟩ := hB s j hj ν hν
  obtain ⟨V₀, hV₀, hCeq⟩ := hC s j hj la hla
  have hjm : j ≤ D.R.m := by rw [idx, List.mem_range'_1] at hj; omega
  refine ⟨(((μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) : ℝ) : ℂ),
    fun t Φ β b hb M M' hM hM' x hx hbj => ?_⟩
  have e1 := hAeq ⟨b j, hbj⟩
  have e2 := hBeq t Φ β b hb M M' hM hM' x hx hbj
  have e3 := hCeq t β b hb hbj
  have hx0 : (x : ℝ) ≠ 0 := by
    intro h0
    have hH' := (hM.vtx (.top j) hjm).haar_fund.1
    have hz : M.ν (.top j) = 0 := by
      rw [hx, show x = 0 from NNReal.coe_eq_zero.1 h0, zero_smul]
    have hpos := Measure.IsOpenPosMeasure.open_pos (μ := M.ν (.top j)) Set.univ isOpen_univ Set.univ_nonempty
    rw [hz] at hpos
    exact hpos rfl
  set lv := la.real {n | (⟨b j, hbj⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hbj⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} with hlv
  set cc : ℝ := (GlobalTheory.RowWt.colCoef ch t β j : ℝ) with hcc
  have hlv0 : lv ≠ 0 := fun h0 => by rw [h0, zero_mul] at e3; exact hV₀.ne' e3.symm
  unfold cellWt
  rw [e1, e2]
  have key : (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * lv * (κ' * x)) * x =
      (μ j).real (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup _) : Set (GfC _)) / (κ * κ' * V₀) * cc := by
    have hcc0 : cc ≠ 0 := fun h0 => by rw [h0, mul_zero] at e3; exact hV₀.ne' e3.symm
    have hk1 := hκ.ne'
    have hk2 := hκ'.ne'
    rw [← e3]
    field_simp
  have := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [hcc] at this
  push_cast at this ⊢
  exact this

end GlobalTheory.CellMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplusStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.top 0), finG (G.V (.top 0)) k ∈ G.Kplus →
    ∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (τ.sum fun d b => b * ∏ l, moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l (z l)) =
        τ.sum fun d b => b * ∏ l, vecsOf S d l (z l) := by
  first | exact @GlobalTheory.TopZeroFirst.product_invariant | exact GlobalTheory.TopZeroFirst.product_invariant | (intros; apply GlobalTheory.TopZeroFirst.product_invariant <;> assumption)
end

