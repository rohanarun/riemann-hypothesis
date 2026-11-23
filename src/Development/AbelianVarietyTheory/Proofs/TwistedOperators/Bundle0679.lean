module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0675
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowInnerVertexVacuaScaledLocalProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepPairFixesFlippedTensorSum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil
open GlobalTheory.SplitFlip (Grid Edge oppositePath)

namespace GlobalTheory.FlatPlace

theorem prod_range_pairs (g : ℕ → ℂ) (n : ℕ) : ∏ j ∈ Finset.range (2 * n), g j = ∏ l ∈ Finset.range n, g (2 * l) * g (2 * l + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]

theorem prod_fin_pairs {m : ℕ} (hm : Even m) (g : Fin m → ℂ) :
    ∏ j, g j = ∏ l : Fin (m / 2), g ⟨2 * l, by have := l.2; omega⟩ * g ⟨2 * l + 1, by have := l.2; omega⟩ := by
  have h2 : m = 2 * (m / 2) := by obtain ⟨a, ha⟩ := hm; omega
  let g' : ℕ → ℂ := fun j => if h : j < m then g ⟨j, h⟩ else 1
  have e1 : ∏ j, g j = ∏ j ∈ Finset.range m, g' j := by
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => by simp only [g', dif_pos j.2]
  rw [e1, congrArg Finset.range h2, prod_range_pairs, Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  have := l.2
  simp only [g']
  rw [dif_pos (by omega), dif_pos (by omega)]

theorem exists_unpair {Y : ℕ → Type} [∀ j, Nonempty (Y j)] {n : ℕ} (q : ∀ l : Fin n, Y (2 * l) × Y (2 * l + 1)) :
    ∃ x : ∀ j, Y j, ∀ l : Fin n, (x (2 * l), x (2 * l + 1)) = q l := by
  have h : ∀ j, ∃ y : Y j, ∀ l : Fin n, (j = 2 * l → HEq y (q l).1) ∧ (j = 2 * l + 1 → HEq y (q l).2) := fun j => by
    by_cases h1 : ∃ l : Fin n, j = 2 * l
    · obtain ⟨l, rfl⟩ := h1
      refine ⟨(q l).1, fun l' => ⟨fun e => ?_, fun e => by omega⟩⟩
      obtain rfl : l = l' := Fin.ext (by omega)
      rfl
    · by_cases h2 : ∃ l : Fin n, j = 2 * l + 1
      · obtain ⟨l, rfl⟩ := h2
        refine ⟨(q l).2, fun l' => ⟨fun e => by omega, fun e => ?_⟩⟩
        obtain rfl : l = l' := Fin.ext (by omega)
        rfl
      · exact ⟨Classical.arbitrary _, fun l => ⟨fun e => absurd ⟨l, e⟩ h1, fun e => absurd ⟨l, e⟩ h2⟩⟩
  choose x hx using h
  exact ⟨x, fun l => Prod.ext (eq_of_heq ((hx _ l).1 rfl)) (eq_of_heq ((hx _ l).2 rfl))⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k)

theorem pureTensor_phiM (keep : Bool) (ε g : Γ.VertexGroup)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (z : Γ.Args) :
    Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z =
      zetaLoc Γ keep ε g * moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
  have h1 : Γ.edgeFactor .one (ε * g) = fun e => Γ.edgeFactor .one ε e * Γ.edgeFactor .one g e := by
    funext e
    simp only [Grid.edgeFactor, Pi.mul_apply, map_mul, GlobalTheory.SplitFlip.apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z = ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod *
      Γ.pathAct .one (oppositePath Γ.m) g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
    simp only [Grid.lines₂, Grid.pathAct, phiM, h1, List.prod_map_mul, mul_assoc]
    rfl
  rw [h2, zetaLoc, moved]
  cases keep
  · simp only [Bool.false_eq_true, if_false, mul_assoc, Units.mul_inv_cancel_left]
  · simp only [if_true, mul_one, one_mul]

theorem flatTensor_phiM [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (ε g : Γ.VertexGroup) (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (x : ColArgs Γ) (y : RowArgs Γ) :
    flatTensor hs ψ ν (Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ)) x y =
      zetaLoc Γ keep ε g * flatTensor hs ψ ν (moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ)) x y := by
  simp only [flatTensor, flatIntegrand, pureTensor_phiM Γ keep, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem gv_row (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (i : ℕ) :
    (epsV ch.G t w * (repsAt ch.G t w).elt β) (i, D.R.m) = 1 := by
  rw [Pi.mul_apply]
  by_cases hi : i = D.R.m
  · subst hi
    rw [epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), mul_one]
  · have e1 : epsV ch.G t w (i, D.R.m) = 1 := dif_neg hi
    have e2 : (repsAt ch.G t w).elt β (i, D.R.m) = 1 := dif_neg hi
    rw [e1, e2, mul_one]

theorem colAt_up {t : T} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : ColArgs (locGrid ch.G t w)) (j : ℕ)
    (hj : j < D.R.m) : ch.S.toGridChoice.colAt t w (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
      (frTop ch.S.toGridChoice t w (j + 1) j.2) (x j)) j = x j := by
  rw [GridChoice.colAt, dif_pos hj]
  refine Eq.trans ?_ (Witness.down_up p (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) (x j))
  have e : p.π = (cpt w).comp (toEAf D) := RingHom.ext hp.2.1
  rw [Place.down, e]
  rfl

theorem placeAt_of (hc : ChrP ch) (ha : ArrP ch) (hl : LocP ch) (hd : DblP ch) (hz : LastP ch) (hb : CombP ch) (hs : ScalP ch) :
    PlaceAt ch (-1) := by
  obtain ⟨κ, z, h1, h2, h3⟩ := hs
  refine ⟨κ, z, h1, h2, fun t w hw β => ⟨_, h3 t w hw β, ?_⟩⟩
  intro e he M hM r r₀ h hr hr₀ hh φ hφ v f hv hf I S x d c hdc hx u
  obtain ⟨p, hp, rfl⟩ := _root_.GlobalTheory.PlcAtW.exists_plc D w e he
  have hm := D.R.two_le_m
  have hev : Even D.R.m := D.R.m_even
  have hP : IsPts ch t w β p.e r r₀ h := ⟨hr, hr₀, hh⟩
  have hV : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j) := fun j => ⟨hv j, hf j⟩
  have hcond := (hc t w hw p hp).2.1
  have hE : ∀ j (hj : j + 1 < D.R.m), Even j →
      Expands p j hj (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j) := fun j hj hj' => by
    by_cases h2 : j + 2 = D.R.m
    · exact hz t w hw p hp β r r₀ h hP M hM φ v f hV j h2
    · exact hd t w hw p hp β r r₀ h hP M hM φ v f hV j hj' (by omega)
  have hΞ : ∀ (i : I) (j : Fin D.R.m), ∃ Ξ : SB (Matrix _ _ (Kw w)), i ∈ S →
      (∀ y, Ξ.1 y = (d i j).fn (p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) y)) ∧
      p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) ((c i).1 j) Ξ.1 :=
    fun i j => by
      by_cases hi : i ∈ S
      · obtain ⟨Ξ, hΞ⟩ := hb t w hw p hp j j.2 (d i j) ((c i).1 j) (hdc i hi j).1 (hdc i hi j).2
        exact ⟨Ξ, fun _ => hΞ⟩
      · exact ⟨0, fun h => absurd h hi⟩
  choose Ξ hΞ using hΞ
  have hlt : ∀ l : Fin (D.R.m / 2), 2 * l.1 + 1 < D.R.m := fun l => by have := l.2; omega
  have hSB : ∀ j < D.R.m - 1, phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
      (.theta D.R.m j) ∈ SB _ := fun j hj => by
    obtain ⟨-, -, -, Φ, hΦ, -⟩ := ha t w hw p hp φ j (by omega) _ _ (hV ⟨j, by omega⟩) _ _ (epsV_mem t w) 1 _ 1 _
      (hl t w hw p hp β r r₀ h hP j (by omega)).1 (hl t w hw p hp β r r₀ h hP (j + 1) (by omega)).1 _ _ (Equiv.refl _) (Equiv.refl _)
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Kw w)
    have key : ∀ {A B : Type}, Topology.IsClosedEmbedding fun z : Matrix A B (Kw w) => zᵀ :=
      Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ) (fun z => rfl) continuous_id.matrix_transpose
        continuous_id.matrix_transpose
    have e : phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j) =
        Φ.1 ∘ fun z => zᵀ := funext fun z => (hΦ zᵀ).symm
    rw [e]
    exact ⟨Φ.2.1.comp_continuous key.continuous, Φ.2.2.comp_isClosedEmbedding key⟩
  have key := _root_.GlobalTheory.prod_eq_sum_of_factorwise_expansion (Fin (D.R.m / 2)) _ I S
    (fun i => zetaLoc (locGrid ch.G t w) (keepAt ch.G w) (epsV ch.G t w) ((repsAt ch.G t w).elt β) * x i)
    (fun l i q => (Ξ i ⟨2 * l, by have := hlt l; omega⟩).1 q.1 * (Ξ i ⟨2 * l + 1, hlt l⟩).1 q.2)
    (fun l i => combC ch.W (c i) (conAt ch.W hM v (h * r₀)) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l => facAt ch t w β φ (2 * l)) (fun l => conAt ch.W hM f (h * r) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).1
        fun q₁ q₂ => hy (q₁, q₂)) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, combC] using this)
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).2
        hy) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, combC] using this)
    (fun q => by
      obtain ⟨y, hy⟩ := exists_unpair (Y := fun j => Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)))
        (Fin (topRank (locGrid ch.G t w) j)) (Kw w)) q
      have e1 := hx (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j))
        fun j => Witness.up_half p _ _ _
      have e2 := _root_.GlobalTheory.FlatPlace.flatTensor_pureTensor_eq_prod_locA (Kw w) (locGrid ch.G t w) one_le_sLen hm hev (psiAt ch.W w) (unitVol w) hcond.continuous hcond.ne_one
        (isUnitVol_unitVol w).1 _ hSB (ch.S.toGridChoice.colAt t w fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
          (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j)) 0
      replace e2 := ((flatTensor_phiM (locGrid ch.G t w) one_le_sLen (psiAt ch.W w) (unitVol w) (keepAt ch.G w) (epsV ch.G t w)
        ((repsAt ch.G t w).elt β) φ _ 0).trans (congrArg _ e1.symm)).symm.trans e2
      rw [Finset.prod_eq_one (s := Finset.range (locGrid ch.G t w).m) (fun i _ => by
        simp only [phiM, hφ, Grid.edgeFactor, mul_one]
        change ((_ : ℂˣ) : ℂ) * _ * _ * _ = 1
        rw [show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).src = 1 from gv_row ch t w β i,
          show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).tgt = 1 from gv_row ch t w β (i + 1)]
        simp), one_mul, Finset.prod_range] at e2
      refine Eq.trans (Finset.prod_congr rfl fun l _ => ?_) (e2.symm.trans ?_)
      · rw [colAt_up ch hp y _ (by have := hlt l; omega), colAt_up ch hp y _ (hlt l), hy l]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_assoc, prod_fin_pairs hev]
        congr 1
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [(hΞ i _ hi).1, (hΞ i _ hi).1, ← hy l])
    fun l => ⟨0⟩
  simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one, Finset.prod_range]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem big_placeAt : Big fun ch => ∃ s, PlaceAt ch s :=
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨lat, chr⟩, loc⟩, bes⟩, jac⟩, scal⟩, arr⟩, comb⟩, dbl⟩, last⟩ =>
    ⟨-1, placeAt_of ch chr (arr lat chr) loc (dbl chr (arr lat chr) loc bes jac) (last chr (arr lat chr) loc bes jac) (comb lat) scal⟩)
  (((((((((_root_.GlobalTheory.FlatPlace.big_latP.and _root_.GlobalTheory.FlatPlace.chrP_big).and GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth).and _root_.GlobalTheory.FlatPlace.Big₂).and _root_.GlobalTheory.FlatPlace.big_jacP).and _root_.GlobalTheory.FlatScal.scal).and
    _root_.GlobalTheory.ArrowModel.arrow_model).and _root_.GlobalTheory.FlatPlace.eventually_combination_of_lattice).and _root_.GlobalTheory.FlatPlace.dblP_big).and _root_.GlobalTheory.FlatPlace.lastStep_eventually)

end GlobalTheory.FlatPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

theorem key {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (hch : ch.Is) (hsh : ShapeAt ch) : KFix ch := by
  intro t Φ τ hτ J hJ k hk y v
  have hJ' : 1 ≤ J ∧ J + 1 < D.R.m := by
    simp only [idx, List.mem_range'_1] at hJ
    omega
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : j + 1 + 1 < D.R.m := hJ'.2
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := _root_.GlobalTheory.RowKFix.local_prod_col ch large₂ F hS hch hsh t Φ j hj k hk
  exact _root_.GlobalTheory.RowKFix.Tens.sum_om_single_eq ch large₂ F hS hch t Φ τ hτ j hj k hk c₁ c₂ h1 h2 h3 y v

theorem kfix : Big fun ch => KFix ch := by
  obtain ⟨CF0, h⟩ := _root_.GlobalTheory.RowShape.shapeAt_big
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    key ch large₂ F hS hch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowKFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLatti
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

theorem charx_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)),
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) →
      W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h'))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' a' ha'
  have hh := (F.dJ (σ + 1) h).hO_ext (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h') 0 0 a' 0 0
  simp only [map_zero, zero_add, add_zero] at hh
  rw [symplO, hh, show hO (G.V (.core (2 * (σ + 1) + 1))) (G.V (.grid (2 * σ + 2) 0)) 0 0 = 0 by simp [hO],
    show pairS (G.V (.grid (2 * σ + 2) 0)) (0 : Mx D _ (σ + 1)) 0 = 0 by simp [pairS], add_zero, add_zero,
    pairS_eq_sum, Finset.mul_sum]
  change psiE W.ψ _ = 1
  refine Finset.sum_induction _ (fun z => psiE W.ψ z = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun p _ => ?_
  rw [_root_.GlobalTheory.CharXFB.hA_xFB_col D hD T L μ0 hL sc G W M hM F hF σ h h' a' p]
  refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (P := fun _ => True) ?_ fun v _ => ?_
  · have hu : MxAt (fun _ => True) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a') :=
      mxAt_of_mem_depLat (p := .chi (2 * σ + 2) 0) ha'
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (GlobalTheory.LastOpPf.cA_mem_idAt ?_))
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hu k l)
  · by_cases hv : v ∈ G.pl.S0
    · exact _root_.GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv
    · exact _root_.GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv

end GlobalTheory.CharXFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSeesawHermitianTripleGridSquareOfStanding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num)

namespace GlobalTheory.SquareTripleForm

variable {D : D7}

theorem hasSignature_add {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b : ℕ} (h : Formalism.UG.HasSignature J a b) :
    a + b = n := by
  obtain ⟨e, -⟩ := h
  simpa using (Fintype.card_congr e).symm

theorem isTriple_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m),
    SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) := by
  intro D T L sc G μ₀ hL W t i j hS M hM
  obtain ⟨e, Bs, Γ, X, om, om', hX, hY, -⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j hS M hM
  have hi := i.2
  have hj := j.2
  have nv : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.node (.grid a b)).IsV (rankV D a b) ((D.R.m - b) / 2) :=
    fun a b ha hb => node_isV G hL (X := .grid a b) ⟨ha, hb⟩
  have rW : (G.V (.grid (↑i + 1) (↑j + 1))).rank = rankV D (↑i + 1) (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rW₁ : (G.V (.grid ↑i ↑j)).rank = rankV D ↑i ↑j := (nv _ _ (by omega) (by omega)).rank
  have rV : (G.V (.grid ↑i (↑j + 1))).rank = rankV D ↑i (↑j + 1) := (nv _ _ (by omega) (by omega)).rank
  have rV₁ : (G.V (.grid (↑i + 1) ↑j)).rank = rankV D (↑i + 1) ↑j := (nv _ _ (by omega) (by omega)).rank
  have hrank : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank =
      (G.V (.grid (↑i + 1) (↑j + 1))).rank + (G.V (.grid ↑i ↑j)).rank := by
    show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank = _
    rw [rW, rW₁, rV, rV₁]; simp only [rankV]; ring
  obtain ⟨hχ, hχ0⟩ := GlobalTheory.SquareChars.chi_hecke_res G hL i
  have hμ := GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j
  have hμ0 := GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j
  have hη := GlobalTheory.SquareChars.isHeckeChar_pow' hL.eta.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  have hη1 := GlobalTheory.SquareChars.resEta_pow' (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j)
  obtain ⟨p1, p2⟩ := GlobalTheory.SquareChars.rank_parity G hL i j
  refine ⟨GlobalTheory.SquareChars.isHeckeChar_mul' hμ hη, GlobalTheory.SquareChars.isHeckeChar_mul' hχ hη,
    resEta_parity (resEta_mul hμ0 hη1) (by rw [zero_add]; exact p2),
    resEta_parity (resEta_mul hχ0 hη1) (by rw [zero_add]; exact p1), hrank, ?_, ?_, ?_, ?_⟩
  · rw [hrank]; exact hY.geo.even
  · have sgn : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (G.V (.grid a b)) τ)
        ((G.V (.grid a b)).rank - (D.R.m - b) / 2) ((D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := (nv a b ha hb).sigOK (tauE D τ)
      rw [(nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    have sgnN : ∀ a b (ha : a ≤ D.R.m) (hb : b ≤ D.R.m) τ, Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid a b))) τ)
        ((D.R.m - b) / 2) ((G.V (.grid a b)).rank - (D.R.m - b) / 2) := by
      intro a b ha hb τ
      have s := GlobalTheory.GridWeil.sigOK_neg (nv a b ha hb).sigOK (tauE D τ)
      have e : (negSp (G.V (.grid a b))).sig (tauE D τ) = ((G.V (.grid a b)).sig (tauE D τ)).swap := rfl
      rw [e, (nv a b ha hb).sig, ← (nv a b ha hb).rank] at s
      exact s
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
    obtain ⟨τ₀, hτ₀, -⟩ := hX.cart w
    have tW : Formalism.UG.HasSignature (gramAt D (G.V (.grid (↑i + 1) (↑j + 1))) τ₀)
        ((G.V (.grid (↑i + 1) (↑j + 1))).rank - Γ.p) Γ.p := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV.sig w
      rw [hX.JW, one_smul] at hs
      have hmap : (G.V (.grid (↑i + 1) (↑j + 1))).gram.map (Bs.emb w).1 = (gramAt D _ τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀]
      rw [hmap] at hs
      exact hs
    have tW₁ : Formalism.UG.HasSignature (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀) Γ.q
        ((G.V (.grid ↑i ↑j)).rank - Γ.q) := by
      refine GlobalTheory.FunObj.hasSignature_of_hasSig_conj ?_
      have hs := hY.geo.hV'.sig w
      rw [hX.JW₁] at hs
      have hmap : ((-1 : D.host.E) • (G.V (.grid ↑i ↑j)).gram).map (Bs.emb w).1 =
          (gramAt D (negSp (G.V (.grid ↑i ↑j))) τ₀).map (starRingEnd ℂ) := by
        ext a b; simp [gramAt, hτ₀, HSpace.gram]
      rw [hmap] at hs
      exact hs
    have hp : Γ.p = (D.R.m - (↑j + 1)) / 2 := by
      have r1 := sgn (↑i + 1) (↑j + 1) (by omega) (by omega) τ₀
      have c1 := hasSignature_add r1
      have c2 := hasSignature_add tW
      have u := _root_.GlobalTheory.SylvesterInertia.hasSignature_fst_unique tW r1
      omega
    have hq : Γ.q = (D.R.m - ↑j) / 2 := _root_.GlobalTheory.SylvesterInertia.hasSignature_fst_unique tW₁ (sgnN ↑i ↑j (by omega) (by omega) τ₀)
    have h1 := hY.geo.eBig
    have h2 := hY.geo.aBig
    have h3 := hY.geo.lt
    dsimp only [spW, spW₁] at h1 h2 h3
    refine ⟨(D.R.m - (↑j + 1)) / 2, (D.R.m - ↑j) / 2, fun τ => ⟨sgn _ _ (by omega) (by omega) τ,
      sgn _ _ (by omega) (by omega) τ, ?_⟩, by rw [← hp, ← hq]; omega, by rw [← hp, ← hq]; exact h2⟩
    have sV := sgn ↑i (↑j + 1) (by omega) (by omega) τ
    have sV₁ := sgn (↑i + 1) ↑j (by omega) (by omega) τ
    have cV := hasSignature_add sV
    have cV₁ := hasSignature_add sV₁
    have s := GlobalTheory.Doubling.sigOK_hsum (nv ↑i (↑j + 1) (by omega) (by omega)).sigOK
      (nv (↑i + 1) ↑j (by omega) (by omega)).sigOK (tauE D τ)
    have e : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).sig (tauE D τ) =
        (G.V (.grid ↑i (↑j + 1))).sig (tauE D τ) + (G.V (.grid (↑i + 1) ↑j)).sig (tauE D τ) := rfl
    rw [e, (nv ↑i (↑j + 1) (by omega) (by omega)).sig, (nv (↑i + 1) ↑j (by omega) (by omega)).sig] at s
    simp only [Prod.fst_add, Prod.snd_add] at s
    have e3 : (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))).rank -
        ((D.R.m - (↑j + 1)) / 2 + (D.R.m - ↑j) / 2) =
        rankV D ↑i (↑j + 1) - (D.R.m - (↑j + 1)) / 2 + (rankV D (↑i + 1) ↑j - (D.R.m - ↑j) / 2) := by
      show (G.V (.grid ↑i (↑j + 1))).rank + (G.V (.grid (↑i + 1) ↑j)).rank - _ = _
      omega
    rw [e3]
    exact s
  · intro τ
    refine ⟨_, _, GlobalTheory.SquareExps.alpha_exp (G := G) hL t ↑i ↑j j.2 τ, GlobalTheory.SquareExps.beta_exp (G := G) hL ↑i ↑j i.2 τ, ?_⟩
    have key := _root_.GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen sc.cGap τ ↑i ↑j i.2 j.2
    rw [hrank, rW, rW₁]
    push_cast at key ⊢
    linarith
  · exact _root_.GlobalTheory.TripleRam.ram_clause hL W t i j hS M hM e Bs Γ X om om' hX hY

end GlobalTheory.SquareTripleForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalMatrixGridNodeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselGroup_of_localMatrix_gridNode : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  first | exact @GlobalTheory.RowRepBes.mem_besGrp_of_locAt | exact GlobalTheory.RowRepBes.mem_besGrp_of_locAt | (intros; apply GlobalTheory.RowRepBes.mem_besGrp_of_locAt <;> assumption)
end

