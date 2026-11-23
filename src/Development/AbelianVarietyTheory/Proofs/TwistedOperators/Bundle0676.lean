module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeColumnsOffFiniteSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsBesselLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenPathRepresentationFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem restrictPol_comp (P : PolE G) {X Y : Node} (p : Path T X Y) : ∀ {Z : Node} (q : Path T Y Z),
    restrictPol P (p.comp q) = Path.Fam.append (restrictPol P p) (restrictPol P q)
  | _, .nil => rfl
  | _, .snoc a q => by
    show (restrictPol P (p.comp q), polOf P a) = (Path.Fam.append (restrictPol P p) (restrictPol P q), polOf P a)
    rw [restrictPol_comp P p q]

theorem zip_append {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} (d : p.Fam S)
    (d' : p.Fam S') : ∀ {Z : Node} (q : Path T Y Z) (e : q.Fam S) (e' : q.Fam S'),
    Path.Fam.zip φ (d.append e) (d'.append e') = (Path.Fam.zip φ d d').append (Path.Fam.zip φ e e')
  | _, .nil, _, _ => rfl
  | _, .snoc a q, e, e' => by
    show (Path.Fam.zip φ (d.append e.1) (d'.append e'.1), φ a e.2 e'.2) =
      ((Path.Fam.zip φ d d').append (Path.Fam.zip φ e.1 e'.1), φ a e.2 e'.2)
    rw [zip_append φ d d' q e.1 e'.1]

theorem zip_rowFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (j : ℕ) : ∀ n (f : ∀ i : Fin n, S (.right i j))
    (g : ∀ i : Fin n, S' (.right i j)), Path.Fam.zip φ (rowFam j n f) (rowFam j n g) = rowFam j n fun i => φ _ (f i) (g i)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (Path.Fam.zip φ (rowFam j n fun i => f i.castSucc) (rowFam j n fun i => g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n))) =
      (rowFam j n fun i => φ _ (f i.castSucc) (g i.castSucc), φ _ (f (Fin.last n)) (g (Fin.last n)))
    rw [zip_rowFam φ j n]

theorem zip_downFam {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) : ∀ n (f : ∀ j : Fin n, S (.down t i j))
    (g : ∀ j : Fin n, S' (.down t i j)), Path.Fam.zip φ (downFam t i n f) (downFam t i n g) = downFam t i n fun j => φ _ (f j) (g j)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show Path.Fam.zip φ (Path.Fam.append (p := Path.one (.down t i n)) ((), f (Fin.last n)) (downFam t i n fun j => f j.castSucc))
        (Path.Fam.append (p := Path.one (.down t i n)) ((), g (Fin.last n)) (downFam t i n fun j => g j.castSucc)) =
      Path.Fam.append (p := Path.one (.down t i n)) ((), φ _ (f (Fin.last n)) (g (Fin.last n)))
        (downFam t i n fun j => φ _ (f j.castSucc) (g j.castSucc))
    refine (zip_append φ (p := Path.one (.down t i n)) (((), f (Fin.last n)) : (Path.one (.down t i n)).Fam S)
      (((), g (Fin.last n)) : (Path.one (.down t i n)).Fam S') (downPath t i n) (downFam t i n fun j => f j.castSucc)
      (downFam t i n fun j => g j.castSucc)).trans ?_
    rw [zip_downFam φ t i n]
    rfl

theorem restrictPol_rowPath (P : PolE G) (j : ℕ) : ∀ n, restrictPol P (rowPath T j n) = rowFam j n fun i => polOf P (.right i j)
  | 0 => rfl
  | n + 1 => by
    show (restrictPol P (rowPath T j n), polOf P (.right n j)) = (rowFam j n fun i => polOf P (.right (i.castSucc : Fin (n + 1)) j), _)
    rw [restrictPol_rowPath P j n]
    rfl

theorem restrictPol_downPath (P : PolE G) (t : T) (i : ℕ) : ∀ n,
    restrictPol P (downPath t i n) = downFam t i n fun j => polOf P (.down t i j)
  | 0 => rfl
  | n + 1 => by
    show restrictPol P ((Path.one (.down t i n)).comp (downPath t i n)) = _
    rw [restrictPol_comp, restrictPol_downPath P t i n]
    rfl

theorem tensE_single (W : G.Weil) {X Y : Node} (p : Path T X Y) (P : PolE G) (d : PureT G p) (c : ℂ) :
    tensE W p (Finsupp.single P 1) (Finsupp.single d c) =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d (restrictPol P p)) c := by
  unfold tensE tensT
  rw [Finsupp.mapDomain_single, Finsupp.sum_single_index, Finsupp.sum_single_index, one_mul]
  · simp
  · simp

theorem zip_given (W : G.Weil) (t : T) (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank)
    (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) :
    Path.Fam.zip (fun a (g : Sch G a) Q => W.fock a.pair g Q) (givenFin W t f Φ) (restrictPol (gPol ρ q) (givenPath t D.R.m)) =
      Path.Fam.append (colPure W t f fun j => q j) (rowDatum W ρ Φ) := by
  unfold givenFin givenPath
  rw [restrictPol_comp, zip_append, restrictPol_downPath, restrictPol_rowPath, zip_downFam, zip_rowFam]
  congr 1
  unfold rowDatum
  congr 1
  funext i
  show W.fock (.chi i 0) (W.cosVec i (Φ i)) (if h : (i : ℕ) < D.R.m then ρ ⟨i, h⟩ else 0) = W.datum ρ Φ i
  rw [dite_eq_left i.2]
  rfl

end GlobalTheory.FlipStart


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPositionOffBadPlacesFromBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.GoodPosBF

theorem goodPosition_offBadPlaces_from_besselLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dB ρ h) (F.dJ ρ h) (xZero (F.dJ ρ h)) W.ψ (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v ∧ StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v ∧ (0 < ρ → ∀ a ∈ idAt D (· = v), (F.dJ ρ h).incAdj (F.V₀ ρ) (a • yBF F ρ h) ∈ latO (F.V₀ ρ) _ (lat0 F ρ h : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (· = v) ↔ a ∈ intAt D (· = v)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h v hv
  have I := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  refine ⟨⟨sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e), (I.2.1 ρ h).1,
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e),
    sd (.core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega) (fun j e => by cases e),
    ((I.2.1 ρ h).2.1 v).1, ((I.2.1 ρ h).2.1 v).2,
    _root_.GlobalTheory.AscFin.primAt_std_bessel D hq T L μ0 hL sc G W M hM F hF ρ h v hv, _root_.GlobalTheory.StairCols.colsAt_xZero D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩,
    _root_.GlobalTheory.AscFin.stdAt_pcBF D hq T L μ0 hL sc G W M hM F hF ρ h v hv, _root_.GlobalTheory.AscFin.incAdj_yBF_mem_latO_iff D hq T L μ0 hL sc G W M hM F hF ρ h v hv⟩

end GlobalTheory.GoodPosBF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape


set_option maxHeartbeats 800000 in
theorem shapeAt_big : Big fun ch => ShapeAt ch := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    ((((((((((((((_root_.GlobalTheory.RowShape.moves0).and _root_.GlobalTheory.BaseTiltMove.base_moves_rowN).and _root_.GlobalTheory.RowShape.topL_selfDual_orthAt).and _root_.GlobalTheory.RowShape.coreL_selfDual_split).and _root_.GlobalTheory.RowShape.big_isSelfDualC_rowN).and _root_.GlobalTheory.RowShape.big_monoAt_rowN).and _root_.GlobalTheory.RowShape.rowN_monoAt).and _root_.GlobalTheory.RowShape.big_primAt_rowN).and _root_.GlobalTheory.RowShape.big_primAt_rowJac).and
      _root_.GlobalTheory.RowColsBF.colsAt_bf).and _root_.GlobalTheory.RowShape.cols_jacBes_rowN).and _root_.GlobalTheory.RowShape.big_last_rowN).and _root_.GlobalTheory.LastLineLat.kap_lastTau_latO).and _root_.GlobalTheory.LastRowUnram.chars_unram)
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmv0, hmvS⟩, htop⟩, hcore⟩, hsd⟩, hmB⟩, hmJ⟩, hpB⟩, hpJ⟩, hcBF⟩, hcFB⟩, hlast⟩, hkap⟩, hun⟩ := h
  have hmv : ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → ∀ j, j ≤ D.R.m → GlobalTheory.FinPl.Moves _ (b j) (ch.G.Λ (.grid D.R.m j)) (GlobalTheory.RowShape.rowN ch.G j) fun _ => True := fun t b hb j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hmv0 t b hb
    · exact hmvS t b hb j hj0 hj
  have hX : ∀ k, k ≤ D.R.m → IsSelfDualC (ch.G.V (.top k)) (ch.G.Λ (.top k)) := fun k hk =>
    (ch.G.isV (X := .top k) (by show k ≤ D.R.m; omega) (fun _ e => Node.noConfusion e)).sd
  refine ⟨GlobalTheory.RowShape.rowN ch.G, GlobalTheory.RowShape.coreL ch.G, GlobalTheory.RowShape.lineL D, GlobalTheory.RowShape.topL D, hmv, htop.1, htop.2,
    fun t M hM j σ hj vN v => ?_⟩
  obtain ⟨hLL, hN0, hO⟩ := hcore j σ hj
  refine ⟨hLL, hO v, ?_, ?_, ?_, ?_⟩
  · exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd j (by omega)
        sdV₀ := hN0
        sdW := hsd (j + 1) (by omega)
        sdW₀ := hX (j + 1) (by omega)
        monoV := hmB j σ hj v
        monoW := hmJ (j + 1) (by omega) σ (by omega) v
        prim := hpB j σ hj v
        cols := hcBF j σ hj v
        last := fun hσ a ha => hlast j σ hj v hσ a ha }
  · intro i hi hi'
    subst hi
    exact
      { tame := GlobalTheory.FinPl.TamePlaces.tame D v
        sdV := hsd i (by omega)
        sdV₀ := hX i (by omega)
        sdW := hsd (i + 1) (by omega)
        sdW₀ := hN0
        monoV := hmJ i (by omega) (σ + 1) (by omega) v
        monoW := hmB (i + 1) σ (by omega) v
        prim := hpJ i (by omega) (σ + 1) (by omega) v
        cols := hcFB i σ hi' v }
  · intro hσ w hw
    subst hσ
    exact hkap j (by omega) v w hw
  · exact fun hoff i hi => hun t v hoff i hi
end GlobalTheory.RowShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypotheses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowBasic

theorem c3 : Big fun ch => ∀ t (M : Vol ch.G), M.Is t → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t M hM X hX _
  refine (hM.vtx X ?_).haar_fund
  cases X <;> simp only [DefNode, Node.InRange] at hX ⊢ <;> omega

theorem c4 : Big fun ch => ∀ t Φ β M, IsTermVol t ch.S.toGridChoice Φ β M → IsHaarDef M := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro t Φ β M hM X hX hne
  cases X with
  | grid i j =>
    obtain ⟨hi, rfl⟩ := hX
    exact (hM.2 i hi).haar_fund
  | top j =>
    have : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
    exact (hM.1 j this).haar_fund
  | core i => exact hX.elim

theorem basicAt : Big fun ch => BasicAt ch := by
  have hall := (((((((_root_.GlobalTheory.RowClaim.colFn_cont_left.and _root_.GlobalTheory.FormTopAut.formTop_cont_left).and c3).and c4).and _root_.GlobalTheory.ThetaJoint.main).and _root_.GlobalTheory.FlipRowTheta.row_isThetaFunO).and _root_.GlobalTheory.RowCombGood.comb_good).and _root_.GlobalTheory.CombsExist.combs_exist)
  refine GlobalTheory.RowReal.big_mono (fun ch h => ?_) hall
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5a⟩, h5b⟩, h6⟩, h7⟩
  refine ⟨fun a => ⟨(h1 a).2, (h1 a).1⟩, fun t y => ⟨(h2 t y).2, (h2 t y).1⟩, h3, h4, ?_, h6, h7⟩
  intro t Φ τ hτ M hM d hd P hh
  exact ⟨fun j hj hjm => h5a t Φ τ hτ M hM d hd P hh j hj hjm, h5b t Φ τ hτ d hd⟩

end GlobalTheory.RowBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalMatrixGridNode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocGrp GlobalTheory.LocMod

theorem mem_bes {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1)) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ + 1) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ + 1)) k}
    (e : Eq (α := Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin A.rank ⊕ Fin (2 * σ + 1)) k)
      x.val (Γ * ((mt B g).map p.π * sumCols d p.π b u))) (hx : x ∈ symR k (Fin A.rank) (2 * σ + 1)) :
    g ∈ besGrp (diagDec (besDec d rfl) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* k := p.π.comp (incA D)
  set dd := diagDec (besDec d rfl) l hl with hdd
  set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ + 1)) := { β := sumCols d p.π b u, γ := Γ, βγ := h2, γβ := h1 }
  let FA : Frame k A.rank (Fin A.rank) := { β := b, γ := b', βγ := hb, γβ := hb' }
  let F₀ : Frame k (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank (Fin A.rank ⊕ Fin 1) :=
    { β := (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id
      γ := (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix id E.symm
      βγ := by
        refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb]
      γβ := by
        refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb'] }
  have hloc : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    change _ = sumCols d p.π b u * x.val * Γ
    rw [e, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * (dd.jX.map p.π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) = φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z k), dd.j0.map p.π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : dd.j0.map p.π = (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  have jA : dd.j0.map p.π * o.jA.map p.π = (frameMat B A d.ι).map φ := by
    have e : o.jA.map p.π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) k) (0 : Matrix (Fin 1) (Fin A.rank) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have jB : dd.j0.map p.π * o.jB.map p.π = (midCol d rfl).map φ := by
    have e : o.jB.map p.π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) k) (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    refine (congrArg (dd.j0.map p.π * ·) e).trans ((core _).trans ?_)
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  have fX : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i)) = u (Fin.castLE hσ i) * φ (l i)⁻¹ * (dd.jX.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
  have fY : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i).rev) =
      u (Fin.castLE hσ i).rev * φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
  have fZ : ∀ r, F.β r (Sum.inr ⟨σ, hσ'⟩) = u ⟨σ, hσ'⟩ * (dd.j0.map p.π * o.jB.map p.π) r (0 : Fin 1) := fun r =>
    (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun jB r) (0 : Fin 1)).symm))
  have ec := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k))
  rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at ec
  obtain ⟨Φ, hΦ⟩ := exists_hom p F
  have hN : N k (Fin A.rank) (2 * σ + 1) (σ + 1) ≤ (besGrp dd o).comap Φ := by
    refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_sup_left (flag_of_strict p dd F₀ F
      (Sum.elim (Sum.map id fun _ => ⟨σ, hσ'⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, hσ'⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i)))) ?_
      (GlobalTheory.RootEx.lev (σ + 1)) ?_ (hΦ y) fun r s hrs => by rw [Matrix.sub_apply, hy r s hrs, sub_self])
    · rintro (a | j)
      · exact ⟨Sum.inl (Sum.inl a), rfl⟩
      · rcases lt_trichotomy j.val σ with h | h | h
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
    · rintro r ((a | a) | i | i)
      · exact (congrFun (congrFun ec r) (Sum.inl a)).symm.trans (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun ec r) (Sum.inr a)).symm))
      · exact fX i r
      · exact fY i r
    · rintro ((a | a) | i | i)
      · rfl
      · rfl
      · rfl
      · have := i.2
        simp only [GlobalTheory.RootEx.lev, wlev, Sum.elim_inr, Fin.val_rev, Fin.val_castLE]
        omega
  have hle : symR k (Fin A.rank) (2 * σ + 1) ≤ (besGrp dd o).comap Φ := by
    rw [symR, symN_odd]
    refine sup_le ?_ hN
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨h, hh⟩ := Witness.exists_isLoc p FA g₀
    have eA : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jA) = dd.j0 ⬝ o.jA ⬝ mt A h := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
    have eB : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jB) = dd.j0 ⬝ o.jB := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
    have eZ := map_fix p eB
    rw [Matrix.map_mul] at eZ
    have hm : p.IsLoc F (dd.emb0 (o.emb (h, 1))) (embX (2 * σ + 1) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding dd (suppAt_emb o hh.1), eq_embX F _ g₀ ((dd.j0 ⬝ o.jA).map p.π * FA.β) (fun r a => ?_)
        (intertwine p eA hh) fun j => ?_⟩
      · change ((frameMat B A d.ι).map φ * b) r a = _
        rw [Matrix.map_mul, jA]
      · rcases lt_trichotomy j.val σ with hj | hj | hj
        · exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (fX ⟨j.val, hj⟩)
        · obtain rfl : j = ⟨σ, hσ'⟩ := Fin.ext hj
          exact fix_col eZ _ (0 : Fin 1) fZ
        · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, j = (Fin.castLE hσ q).rev :=
            ⟨⟨2 * σ - j.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
          exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclY _)) _ q (fY q)
    change Φ _ ∈ besGrp _ _
    rw [isLoc_unique p (hΦ _) hm]
    exact Subgroup.mem_sup_right ⟨h, rfl⟩
  rw [isLoc_unique p hloc (hΦ x)]
  exact hle hx

end GlobalTheory.RowRepBes

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocMod

theorem mem_besGrp_of_symR {D : D7} {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D))
    (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank)
    (hb : b = B.rank) (hab : a + c = b) (p : Place D (Kw w)) (hp : piAt w = p.π) (g : GA D B) (hg : SuppAt p.e B g)
    (hx : frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c) :
    g ∈ besGrp (diagDec (besDec d h) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  rw [hp] at h1 h2 e
  exact mem_bes p d l hl (GlobalTheory.StdFrames.loc w β).mul_inv (GlobalTheory.StdFrames.loc w β).inv_mul h1 h2 hg (e g) hx

theorem mem_besGrp_of_locAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  intro D T L sc G W U S t ht w hw ew hew j σ hj hj' h' h hs hx
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.PlcAtW.exists_plc D w ew he
  exact mem_besGrp_of_symR (G.rowDec j hj') (by omega) _ _ w _ _ _ (S.row t ht w hw j hj') (topRank_eq G t w hj)
    (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ p (RingHom.ext fun x => (hp.2.1 x).symm) h hs hx

end GlobalTheory.RowRepBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndStepsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subset_place_vectors_and_steps : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  first | exact @GlobalTheory.SubsetVecs.subset_vectors | exact GlobalTheory.SubsetVecs.subset_vectors | (intros; apply GlobalTheory.SubsetVecs.subset_vectors <;> assumption)
end

