module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0653
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UniBF

private theorem psiE_add_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) :
    psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  simp only [psiE, map_add (f := _), AddChar.map_add_eq_mul]

private theorem psiE_zero_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  simp only [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiUni_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ,
    MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ →
    psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W Mv hM F hF ρ h u hu hx
  have hA := _root_.GlobalTheory.UniOff.uni_off D hq T L μ0 hL sc G W Mv hM F hF ρ h
  have hB := _root_.GlobalTheory.AscFin.psiE_superdiag_S0 D hq T L μ0 hL sc G W Mv hM F hF ρ h
  set N : Mx D ρ ρ := u.1.1 - 1 with hNdef
  have hx' : (F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ∈ latRow G (2 * ρ + 1) := by
    have e : xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) = (F.dJ ρ h).jX ⬝ N := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one]; rfl
    rw [← e]; exact hx
  have hN : (F.dJ ρ h).pX ⬝ ((F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ⬝ (F.dB ρ h).jX) = N := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, ← Matrix.mul_assoc, HypDec.pX_jX,
      Matrix.one_mul]
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have e1 : u.1.1 i j = N i j := by rw [hNdef, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [e1]
    refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (hu i j) fun v _ => ?_
    have ho := GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)
    by_cases hv : v ∈ G.pl.S0
    · have := hB _ hx' i j hij v hv _ ho
      rwa [hN] at this
    · have := hA _ hx' i j hij v hv _ ho
      rwa [hN] at this
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero_one W.ψ

end GlobalTheory.AscFin.UniBF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowZeroBasePointCarriesLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowShape

theorem moves_of_forall {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L)
    (hM : Submodule.IsLattice D.host.E M) (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L M (· = v)) :
    GlobalTheory.FinPl.Moves S g L M (fun _ => True) := by
  intro y hy
  have hT := fun (N : GlobalTheory.FinPl.Lat S) (hN : Submodule.IsLattice D.host.E N) (z : Fin S.rank → AE D) =>
    ((_root_.GlobalTheory.FinPl.localComponents D (fun _ => True)).2 S).2.2.2 N z hN
  have hmy : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [hT L hL y, hT M hM _]
  refine ⟨fun ⟨_, h2⟩ => ⟨hmy, fun v _ e he => ?_⟩, fun ⟨_, h2⟩ => ⟨hy, fun v _ e he => ?_⟩⟩
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    have := (h v (e • y) hs).1 (h2 v trivial e he)
    rwa [Matrix.mulVec_smul] at this
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    refine (h v (e • y) hs).2 ?_
    rw [Matrix.mulVec_smul]
    exact h2 v trivial e he

theorem moves0_of_selfDual : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G 0) → ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hN t b hb
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc := hch.guard t
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hΛ : IsSelfDualC _ (ch.G.Λ (.grid D.R.m 0)) :=
    (ch.G.isV (X := .grid D.R.m 0) ⟨le_rfl, Nat.zero_le _⟩ (fun j e => by injection e with h1 h2; omega)).sd
  apply moves_of_forall _ _ _ _ hΛ.1 hN.1
  intro v
  classical
  by_cases hv : ∃ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) = v
  · obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨e, ⟨⟨es, hes, -⟩, -⟩, -, -⟩ := hb.1
    obtain ⟨p, hpe, hpv, hpr⟩ := _root_.GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt D w (es w) (hes w hw) s.hF
    have key := _root_.GlobalTheory.BaseMoveAt.lat_moves_at_place hL hde ch.G ch.W Set.univ ch.S.toGridChoice t trivial hc b hb w hw p (hpe ▸ hes w hw) hpr
    rw [← hpv, ← GlobalTheory.Core.Mi.LatMatch.sMoves_one]
    refine _root_.GlobalTheory.Core.Mi.LatMatch.sMoves_of_wComp D _ p _ _ _ 1 (b 0) hΛ hN (GlobalTheory.Core.Mi.LatMatch.normOneAt_one _) fun x => ?_
    rw [map_one, one_smul]
    exact key x
  · push_neg at hv
    have hv0 : v ∉ ch.G.pl.S0 := fun h0 => hv (ch.G.pl.w v)
      (Finset.mem_union_left _ (by simpa [Places.W0] using ⟨v, h0, rfl⟩)) (ch.G.pl.under_w h0)
    intro y hy
    rw [_root_.GlobalTheory.RowVal.base_mt_mulVec_off ch.G t ch.S.B b hb v hv y hy]
    exact _root_.GlobalTheory.RowShape.latV_grid_iff_rowN_zero ch.G v hv0 y hy

theorem moves0 : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True :=
  big_mono (fun _ h => h.1 (h.2 0 (Nat.zero_le _))) (Big.and moves0_of_selfDual _root_.GlobalTheory.RowShape.big_isSelfDualC_rowN)

end GlobalTheory.RowShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnramifiedAtPlaceIdempotentOfUnramifiedOverPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UnrOverPlaceConv

open GlobalTheory.IdemSupport

theorem unramAt_of_unrAt_all : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F},
    IsPlaceIdem D v ε → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) →
    GlobalTheory.WeilParts.UnramAt ε χ := by
  intro D χ v ε hε hu x hx h1 h2
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨-, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have hee : ε = ε' := placeIdem_unique hε hε'
  subst hee
  subst hf
  exact GlobalTheory.UnrPlDict.unrPl_of_unrAt D v w hw χ hu e _ hp x hx h1 h2

end GlobalTheory.UnrOverPlaceConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_extendByZero_topStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  first | exact @GlobalTheory.LastStepExt0.model_last | exact GlobalTheory.LastStepExt0.model_last | (intros; apply GlobalTheory.LastStepExt0.model_last <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelFlatMapFourierJacobiStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastTwoSteps_localModel_flatMap_fourierJacobiStep : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hLoc : LocP ch) (hBes : BesP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (r r₀ h : Pts ch.G)
    (hpts : IsPts ch t w β p.e r r₀ h) (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt ch.G j 0 hj))
    (h₁ : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1))
    (h₂ : topRank (locGrid ch.G t w) j + (0 + 1) = (locGrid ch.G t w).rank (D.R.m, j)),
    ∃ (F₀ : Frame (Kw w) (besAt ch.G hM j 0 hj vN).V₀.rank (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit))
      (T₁ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)) →ₗ[ℂ]
        (WO (besAt ch.G hM j 0 hj vN).V₀ (ch.G.V (.top (j + 1))) → ℂ)),
      p.IsCoreFrame (besAt ch.G hM j 0 hj vN) (p.xi ^ 0)⁻¹ (frTop ch.S.toGridChoice t w j (by omega)) F₀ ∧
      p.IsModel ch.W.ψ F₀ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) T₁ ∧
      (∀ O, IsOne O → T₁ O = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
        ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r₀) j, 1) (v ⟨j, by omega⟩))) ∧
      ∃ Φ : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1))) (Fin (topRank (locGrid ch.G t w) j) ⊕ Unit) (Kw w)),
        Φ.1 = GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) (0 + 1) (datC h₁ h₂
          (phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j))) ∧
        T₁ Φ = GlobalTheory.Unf.flatBF (lastAt ch.G ch.W t hM j hj vN).s
          ((lastAt ch.G ch.W t hM j hj vN).s.om ((h * r) j, 1) (f ⟨j, by omega⟩)) := by
  first | exact @GlobalTheory.LastStepOne.first_step_flat | exact GlobalTheory.LastStepOne.first_step_flat | (intros; apply GlobalTheory.LastStepOne.first_step_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeMembershipAdjointIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LastGen

open GlobalTheory.SeeSaw GlobalTheory.SeeSaw.LastPrim

theorem incAdj_yZero_mulVec_gen {D : D7} {S A L T T₀ : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {ρ : ℕ}
    (d : HypDec T T₀ ρ) (hρ : 0 < ρ) (a : AE D) (y : Fin S.rank → AE D) :
    Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.incAdj S (a • yZero S ρ (vecB o ζ))) y =
      GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ (incA D D.host.xi0⁻¹ * cA D a * (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
  funext k
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, adj_smul, adj_neg, GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]]
  simp only [if_true, mul_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring


set_option maxHeartbeats 1000000 in
theorem incAdj_yZero_mem_latO_iff_gen : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A L T T₀ : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (ρ : ℕ) (d : HypDec T T₀ ρ) (M : Lat S) (LW : Lat T) (LW₀ : Lat T₀) (𝔟 : ℕ → GlobalTheory.SeeSaw.FI D) (𝔠 : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC S M → IsSelfDualC T LW → GlobalTheory.SeeSaw.MonoId d LW LW₀ 𝔟 v → GlobalTheory.SeeSaw.LineId o ζ M 𝔠 v → 𝔠 ≠ 0 → 𝔟 (ρ - 1) ≠ 0 → (∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (𝔟 (ρ - 1))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v) → 0 < ρ → ∀ a ∈ idAt D (· = v), d.incAdj S (a • yZero S ρ (vecB o ζ)) ∈ latO S T (M : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D ψ hψ S A L T T₀ o ζ ρ d M LW LW₀ 𝔟 𝔠 v hM hLW hmono hline hc hb0 hid hρ a ha
  obtain ⟨h1, h2, h3, h4, -, h6, -⟩ := _root_.GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.LocFrame.cmHost_imaginaryGenerator_ne_zero
  have hci : 𝔠⁻¹ ≠ 0 := inv_ne_zero hc
  have hb : 𝔟 ((⟨ρ - 1, by omega⟩ : Fin ρ) : ℕ) ≠ 0 := hb0
  have hL0 := colMul_jY_mem_latA_iff D ψ hψ T T₀ ρ d LW (𝔟 (ρ - 1)) v ⟨ρ - 1, by omega⟩ hb
    (_root_.GlobalTheory.DualLine.dualLine_mem_iff D ψ hψ T T₀ ρ d LW LW₀ 𝔟 v hLW hmono ⟨ρ - 1, by omega⟩ hb)
  have hL : ∀ t ∈ idAt D (· = v), GlobalTheory.FinPl.colMul d.jY ⟨ρ - 1, by omega⟩ t ∈ latA T LW (· = v) ↔
      cA D t ∈ idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * 𝔠⁻¹) v :=
    fun t ht => (hL0 t ht).trans (hid _)
  have e3 : incA D (D.host.xi0⁻¹)⁻¹ * incA D (star D.host.xi0⁻¹) = -1 := by
    rw [← map_mul, inv_inv, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, mul_neg, mul_inv_cancel₀ hξ, map_neg, map_one]
  have key : ∀ y ∈ latV S M (· = v),
      (Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from
        d.incAdj S (a • yZero S ρ (vecB o ζ))) y ∈ latA T LW (· = v) ↔
        a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idV 𝔠⁻¹ v) := by
    intro y hy
    have hzi : (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l) ∈ idAt D (· = v) :=
      sum_mem fun l _ => Ideal.mul_mem_left _ _ (latV_entry_mem' hy l)
    rw [incAdj_yZero_mulVec_gen o ζ d hρ a y, hL _ (Ideal.mul_mem_left _ _ hzi), map_mul, map_mul, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
      h3 _ _ (inv_ne_zero hξ)]
    have e4 : incA D (D.host.xi0⁻¹)⁻¹ * (incA D (star D.host.xi0⁻¹) * a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) =
        -(a * cA D (∑ l, (∑ m, cA D (ratV (vecB o ζ) m) * gA S m l) * y l)) := by
      rw [← mul_assoc, ← mul_assoc, e3]; ring
    rw [e4, neg_mem_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)⟩⟩
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M LW hM hLW]
  constructor
  · rintro ⟨-, hu⟩
    obtain ⟨g, hg, g', -, hgg, hiff⟩ := h6 𝔠⁻¹ hci
    obtain ⟨y, hy, hyg⟩ := _root_.GlobalTheory.SeeSaw.HzOnto.hz_onto D ψ hψ S A L o ζ M 𝔠 v hM hline hc g hg
    have h7 := ((hiff _).1 ((key y hy).1 (hu y hy))).2
    rw [hyg] at h7
    rw [← hgg a ha]
    have e6 : g' * g * a = g' * (a * g) := by rw [mul_assoc, mul_comm g a]
    rw [e6]; exact h7
  · intro haI
    have hcA : cA D a ∈ idAt D (· = v) := by
      have := (h4 0 a).1 (by rw [zpow_zero]; exact (h1 a).2 haI)
      rw [zpow_zero] at this
      exact ((h1 _).1 this).1
    refine ⟨fun k l => ?_, fun y hy => (key y hy).2 ?_⟩
    · have e5 := congrFun (incAdj_yZero_mulVec_gen o ζ d hρ a (Pi.single l 1)) k
      rw [Matrix.mulVec_single_one] at e5
      refine (congrArg (· ∈ idAt D (· = v)) e5).mpr ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hcA))
    · have hmul := (h2 𝔠⁻¹ 𝔠⁻¹ hci hci a ha).2 (by rw [mul_inv_cancel₀ hci]; exact (h1 a).2 haI)
      exact hmul _ (_root_.GlobalTheory.LineDual.line_pair_mem_idV D ψ hψ S A L o ζ M 𝔠 v hM hline hc y hy)

end GlobalTheory.LastGen

namespace GlobalTheory.AscFin

theorem incAdj_yBF_mem_latO_iff : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, 0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v hv hρ a ha
  have I := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hoff T L μ0 hL sc G W M hM F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hsdJ := (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (by simp)).sd
  obtain ⟨hb0, hc0, hid⟩ := _root_.GlobalTheory.StairIdealAt.completion_eq_of_modul_unit G.pl sc ρ v hρ (_root_.GlobalTheory.ModulUnit.idV_modul_eq_one G.pl sc v hv)
  exact GlobalTheory.LastGen.incAdj_yZero_mem_latO_iff_gen D W.ψ hψ _ _ _ _ _ (F.oB ρ h) (F.ζ (ρ + 1)) ρ (F.dJ ρ h) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0))
    (G.Λ (.core (2 * ρ + 1)))
    (fun i => FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i) * (G.pl.stAbar sc ^ (i + 1))⁻¹))
    _ v (I.2.1 ρ h).1 hsdJ ⟨((I.2.1 ρ h).2.1 v).2, fun i b hb => GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff D hoff T L μ0 hL sc G W M hM F hF ρ h v i b hb⟩
    (_root_.GlobalTheory.ZLineIdeal.bessel_core_lattice_meets_line_of_z_ideal D hoff T L μ0 hL sc G W M hM F hF ρ h v) hc0 hb0 hid hρ a ha

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

theorem GlobalTheory.FlatPlace.eventually_combination_of_lattice : Big fun ch => LatP ch → CombP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat t w hw p hp j hj d c hde hc
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  obtain ⟨f₀, hf₀⟩ := exists_isVac ch.W hL hr
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨q, hq⟩, hn⟩ := hf₀.2.norm
    have := hn q hq
    rw [h0] at this
    simp [nrm2] at this
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hth := hc.2.2 f₀ hf₀.2.theta hf₀.2.lat
  have sdS := (node_isV ch.G hL (X := .top j) hj.le).sd
  have sdT := (node_isV ch.G hL (X := .top (j + 1)) hj).sd
  have hsb := d.sb
  have hth' : FinDatum.IsTheta ch.W d _ _ f₀ _ := hth
  unfold FinDatum.IsTheta at hth'
  rw [hde] at hsb hth'
  obtain ⟨Tm, hTm, hO, Φ, hΦ, hTΦ⟩ := _root_.GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt D (Kw w) p ch.W.ψ hψ _ _ _ _ sdS sdT _ _
    (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) ((hLat t w hw p hp j hj).2) f₀ d.fn _
    hf₀.2.theta hsb hth'
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w) (Y := Fin (topRank (locGrid ch.G t w) (j + 1))) (Y' := Fin (topRank (locGrid ch.G t w) j))
  have hhalf := hc.2.1
  rw [hde] at hhalf
  refine ⟨Φ, hΦ, _root_.GlobalTheory.FlatPlace.isCombAt_of_one D (Kw w) p ch.W.ψ hψ _ _ _ _ _ _ c hhalf Tm hTm O Φ hO1 ?_ ?_⟩
  · rw [hO O hO1]; exact hf0
  · rw [hTΦ, hO O hO1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.RowVal.conLin_big : Big fun ch => ConLin ch :=
  GlobalTheory.RowReal.big_mono (fun ch h => GlobalTheory.ConnectionLinear.conLin_of_positions ch h.1.1.1 h.1.1.2 h.1.2 h.2)
    (((_root_.GlobalTheory.ConnectionLinear.contrLin_left.and _root_.GlobalTheory.ConLinR.contrLin_one_big).and _root_.GlobalTheory.LastPositionLin.lastLin_zero).and _root_.GlobalTheory.ConnectionLinear.big_lastLin_one)
end

