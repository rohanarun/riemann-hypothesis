module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalTangentFrameJacobianDetOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.LogPole.vert_jac_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N) (K : Type) [Field K] [Algebra c.F K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), z ≫ inc₀ TF.X Z = TF.X.ptY P → GlobalTheory.Frames.FrChg (fun σ => (N σ).map (ev z W hz)) 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : VIx Dw → FrPt Xo c (DualNumber K)) (zw : VIx Dw → (Sp (DualNumber K) ⟶ Y₀ TF.X Z)) (hzw : ∀ b, ⊤ ≤ zw b ⁻¹ᵁ W), (∀ b, IsVert P (Pi.single b.toF (1 : K)) (w b)) → (∀ b, zw b ≫ inc₀ TF.X Z = TF.X.ptY (w b)) → (Matrix.of fun a b : VIx Dw => (ev (zw b) W (hzw b) (cellCoord N a)).snd).det = 1 ∧ ∀ b r, (ev (zw b) W (hzw b) (((toBase TF Z).appLE U.1 W h.2.1).hom r)).snd = 0 := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h K _ _ z hz P₀ P hU hzP hPG hB w zw hzw hw hzw'
  have key : ∀ b σ', (N σ').map (ev (zw b) W (hzw b)) = GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
      ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
    intro b σ'
    have hx : frX (w b) ≫ TF.Y.j = zw b ≫ toBase TF Z := by
      rw [toBase, ← Category.assoc, hzw' b]; exact (TF.X.lies_ptY (w b)).1.symm
    have hUx : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_map (toBase TF Z) h.2.1 (hzw b)
    have hk : ⊤ ≤ (zw b ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map (inc₀ TF.X Z) h.2.2.1 (hzw b)
    have hM : ⊤ ≤ (zw b ≫ toBase TF Z) ⁻¹ᵁ (TF.X.F.M k).U := TF.X.F.inM hk (Category.assoc _ _ _)
    obtain ⟨B, hBl, hBu, hBc⟩ := _root_.GlobalTheory.LogPole.frVec_cell_comb E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (w b) (zw b) (hzw b)
      _ hx hUx (hzw' b)
    have hF := _root_.GlobalTheory.LogPole.frVec_isVert_isCombAtG E H Dw l Xo c TF U n e v hv K P₀ P hU _ hPG hB (Pi.single b.toF (1 : K)) (w b) _ hx hUx
      (TF.X.F.M k).toMChart hM (hw b)
    have eq : B σ' * (L σ').map (ev (zw b) W (hzw b)) * (N σ').map (ev (zw b) W (hzw b)) =
        GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' *
          ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) := by
      refine Matrix.ext fun i j => ?_
      have := _root_.GlobalTheory.LogPole.cell_eigComb_coeff_unique E H Dw l Xo c TF Z U n e v hv W k L N h (DualNumber K) (zw b) (hzw b) _ rfl hUx σ' _ _ _
        (hBc σ' i) (hF σ' i)
      have := congrFun this j
      simpa [Matrix.map_mul, Matrix.mul_assoc] using this
    have hN : ∀ i j, j < i → (N σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN1 : ∀ i, (N σ').map (ev (zw b) W (hzw b)) i i = 1 := fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hL : ∀ i j, i < j → (L σ').map (ev (zw b) W (hzw b)) i j = 0 := fun i j hij => by
      simp [h.2.2.2.1 σ' i j hij]
    have hN0 : ∀ i j, j < i → ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i j = 0 :=
      fun i j hij => by simp [h.2.2.2.2.2.1 σ' i j hij]
    have hN01 : ∀ i, ((N σ').map (ev z W hz)).map (fun r => (TrivSqZeroExt.inl r : DualNumber K)) i i = 1 :=
      fun i => by simp [h.2.2.2.2.2.2.1 σ' i]
    have hbt : ∀ (p q : Fin (Dw.mult σ')), some ⟨σ', (p, q)⟩ = b.toF → p < q := by
      intro p q hpq
      obtain ⟨σb, ⟨⟨i, j⟩, hij⟩⟩ := b
      simp only [GlobalTheory.FlagTan.VIx.toF, Option.some.injEq, Sigma.mk.inj_iff] at hpq
      obtain ⟨rfl, hq⟩ := hpq
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 (eq_of_heq hq)
      exact hij
    have hU0 : ∀ i j, j < i → GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i j = 0 := fun i j hij => by
      have h1 : (1 : Matrix (Fin (Dw.mult σ')) (Fin (Dw.mult σ')) K) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij)
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, j)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i j hh) (not_lt.2 hij.le)) _
      simp [GlobalTheory.FlagTan.unip, h1, h2]
    have hU1 : ∀ i, GlobalTheory.FlagTan.unip K (Pi.single b.toF (1 : K)) σ' i i = 1 := fun i => by
      have h2 : (Pi.single b.toF (1 : K) : GlobalTheory.FlagTan.FIx Dw → K) (some ⟨σ', (i, i)⟩) = 0 :=
        Pi.single_eq_of_ne (fun hh => absurd (hbt i i hh) (lt_irrefl _)) _
      simp [GlobalTheory.FlagTan.unip, h2]
    exact _root_.GlobalTheory.lu_unique _ _ _ _ _ _ _ (hBl σ') hL hN hN1 hU0 hU1 hN0 hN01 eq
  refine ⟨?_, fun b r => _root_.GlobalTheory.LogPole.snd_ev_toBase_of_isVert E H Dw l Xo c TF Z U.1 W h.2.1 K P _ (w b) (zw b) (hzw b) (hw b) (hzw' b) r⟩
  have hM : ∀ σ i j, j < i → (N σ).map (ev z W hz) i j = 0 := fun σ i j hij => by simp [h.2.2.2.2.2.1 σ i j hij]
  have hM1 : ∀ σ i, (N σ).map (ev z W hz) i i = 1 := fun σ i => by simp [h.2.2.2.2.2.2.1 σ i]
  convert _root_.GlobalTheory.LogPole.VertDet.det_vert E H Dw K (fun σ => (N σ).map (ev z W hz)) hM hM1 using 2
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.of_apply, cellCoord]
  rw [← key b a.1]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftGaps

theorem antitone_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) (by omega))
    · obtain rfl : a = n + 1 := by omega
      exact le_rfl

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

section Pt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem nCol_le (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    GlobalTheory.RefSum.nCol (dat p i) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
  obtain ⟨-, -, s3⟩ := hw.sig
  have hcard : Fintype.card (Lt1 (dat p i)) = D.R.f * D.R.r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [GlobalTheory.RefSum.sum_mult, hh.deg, s3]
    simp
  have hmult : ∀ τ, (dat p i).mult τ ≤ D.R.r := fun τ => by
    rw [← s3]; unfold Datum.mult; split_ifs <;> omega
  have hsum : ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 (dat p i)) * (2 * D.R.r) := by
    rw [← smul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have := GlobalTheory.FactorDepth.rk_le f
    have := hmult f.1
    omega
  rw [hcard] at hsum
  unfold GlobalTheory.RefSum.nCol
  have h8 : 8 * ((∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f) / 8) ≤ ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f :=
    Nat.mul_div_le _ _
  rw [hcard]
  have : D.R.f * D.R.r * (2 * D.R.r) = 2 * D.R.r * (D.R.f * D.R.r) := by ring
  omega

theorem cols_le_len (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    (GlobalTheory.RefSum.nCol (dat p i) + 1) * (CompHt.dimFlag (dat p i) + 3) ≤ lenT p i PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hr6 : 6 ≤ D.R.r := by omega
  have hf8 := hh.f8
  have hn := nCol_le p i PP A M hw hh
  have hZ : (40 : ℝ) ≤ zBase L := by
    unfold zBase
    have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
    have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    have a4 : (10 : ℝ) ≤ L.sc.L := hh.big.2.1
    nlinarith
  have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
  have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [hw.dim]; push_cast [Nat.cast_choose_two]; ring
  set Dd : ℝ := ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) with hDd
  have F8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have R6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
  have FR : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hDd1 : (1 : ℝ) ≤ Dd := by rw [hD]; nlinarith
  have hn' : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1 ≤ 17 * Dd := by
    have : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
      exact_mod_cast hn
    rw [hD]
    have h13 : (45 : ℝ) ≤ 13 * D.R.r - 33 := by linarith
    have : (48 : ℝ) * 45 ≤ ((D.R.f : ℝ) * D.R.r) * (13 * D.R.r - 33) := mul_le_mul FR h13 (by norm_num) (by linarith)
    nlinarith
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hT : 1600 * Dd ^ 2 ≤ (lenT p i PP : ℝ) := by
    have h1 : 1600 * Dd ^ 2 ≤ PP ^ 2 * Dd ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [le_div_iff₀ hm0]
      have c5 : (1600 : ℝ) ≤ PP ^ 2 := by nlinarith
      have c6 : (0 : ℝ) ≤ Dd ^ 2 := by positivity
      calc 1600 * Dd ^ 2 * D.R.m ≤ PP ^ 2 * Dd ^ 2 * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) hm0.le
        _ ≤ PP ^ 2 * Dd ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm (by positivity)
    exact h1.trans (Nat.le_ceil _)
  have hmain : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (lenT p i PP : ℝ) := by
    have e1 : Dd + 3 ≤ 4 * Dd := by linarith
    have : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (17 * Dd) * (4 * Dd) :=
      mul_le_mul hn' e1 (by linarith) (by linarith)
    nlinarith
  rw [hDd] at hmain
  exact_mod_cast hmain

theorem gapsAt (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))),
      (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p →
        (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  obtain ⟨s1, s2, s3⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have hcl := cols_le_len p i PP A M hw hh
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, -, hH⟩ := hw.hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hdiv
  have hT1 := hW.h1
  simp only [wtsAt] at G hT1

  have gin : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → 0 ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb
    obtain ⟨g1, g2, -⟩ := G τ a b hb
    by_cases hbp : (b : ℕ) = (dat p i).p
    · have g := (g2 hbp).1
      have hT0 : (0 : ℤ) < 2 * (lenT p i PP : ℤ) := by omega
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hT0 hc
      nlinarith
    · have g := g1 hbp
      have : (0 : ℤ) ≤ (lenT p i PP : ℤ) + CompHt.dimFlag (dat p i) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
        positivity
      omega
  have gbar : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb hbp
    obtain ⟨-, g2, -⟩ := G τ a b hb
    have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by omega
    have hle : (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    have : (0 : ℤ) ≤ (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
    linarith

  have gub : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      P.ub τ a - P.ub τ b = (P.u₁ τ a - P.u₁ τ b) / ((dimFlag (dat p i) : ℤ) + 3) := by
    intro τ a b hb
    have hb' : (a : ℕ) + 1 < (dat p i).p + (dat p i).q := hb ▸ b.2
    rw [← CompHS.gap_eq (P.ub τ) hb, P.gap_ub τ hb', CompHS.gap_eq (P.u₁ τ) hb]
  have hcl' : ((GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1) * ((dimFlag (dat p i) : ℤ) + 3) ≤ (lenT p i PP : ℤ) := by
    rw [← dimFlag_eq]; exact_mod_cast hcl
  have hD0 : (0 : ℤ) < (dimFlag (dat p i) : ℤ) + 3 := by positivity
  have hD1 : (1 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 3 := by omega
  have hnT : (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ (lenT p i PP : ℤ) := by
    have : (0 : ℤ) ≤ (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 := by positivity
    nlinarith
  refine ⟨by omega, fun la hla => ?_⟩
  rcases hla with rfl | hla
  · refine ⟨fun τ => antitone_of_step fun a b hb => by have := gin τ a b hb; omega, fun τ a b ha hb => ?_⟩
    exact hnT.trans (gbar τ a b (by omega) hb)
  · rw [Set.mem_singleton_iff] at hla
    subst hla
    refine ⟨fun τ => antitone_of_step fun a b hb => ?_, fun τ a b ha hb => ?_⟩
    · have e := gub τ a b hb
      have := Int.ediv_nonneg (gin τ a b hb) hD0.le
      omega
    · rw [gub τ a b (by omega)]
      exact Int.le_ediv_of_mul_le hD0 (hcl'.trans (gbar τ a b (by omega) hb))

end Pt

end GlobalTheory.LiftGaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.QuoWt

theorem dominance : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw),
    0 ≤ P.c₀ → 2 * (Dw.p + Dw.q) + CompHt.dimFlag Dw ≤ P.T →
    (∀ (τ : Psi H) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      ((b : ℕ) ≠ Dw.p → ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) ≤
        P.u τ a - P.u τ b + 2) ∧
      ((b : ℕ) = Dw.p → ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) + P.c₀ + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 ≤
        P.u τ a - P.u τ b)) →
    ∀ s : ℕ, s ≤ 3 → ∀ τ : Psi H, Antitone (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ) ∧
      Antitone (((P.T + CompHt.dimFlag Dw + (if s = 0 then 3 else 4) : ℕ) : ℤ) • P.u₁ τ - (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ)) := _root_.GlobalTheory.CompHS.WtPar.shifted_dominant

theorem arith : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := _root_.GlobalTheory.bar_gap_param_ineq

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

theorem quo_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) (hN : kc ≤ Dw.p + Dw.q) (u1 : AllWt.Weight Dw)
    (hq : IsQuot Dw kc P.T P.c₀ P.u u1) : u1 = P.u₁ :=
  GlobalTheory.MeanTop.Inhab.dividedWeight_unique _ u1 (by show 1 ≤ kc; omega) hN (isQuot_u₁ Dw P kc hk) hq

section Pt

open IsDedekindDomain _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero D ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  obtain ⟨⟨s1, s2, s3⟩, -, hdim, -, -, -, -, -, -, -, hyp⟩ := hw
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have er : (dat p i).p + (dat p i).q = D.R.r := s3
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := GlobalTheory.QuoWt.isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, hrow, hH⟩ := hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have ha : D.R.k - 2 < (dat p i).p + (dat p i).q := by omega
  refine ⟨by omega, by omega, ?_, fun u1 hu => GlobalTheory.QuoWt.quo_unique (dat p i) P _ hPa (by omega) u1 hu, fun τ => ?_, ?_, ?_⟩
  · have := hh.deg
    have := hh.f8
    omega
  · obtain ⟨a1, a2, -⟩ := GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hdiv τ
    refine ⟨a1, ?_⟩
    convert a2 using 1
    funext j
    simp only [CompHt.uPrime, wtsAt, GlobalTheory.MeanTop.Wts.u', hodgeWt, CompHt.barWt,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add]
    by_cases h : (j : ℕ) < (dat p i).p <;> simp [h] <;> ring
  · refine ⟨fun τ => -(FlagTan.kap (dat p i) τ ⟨D.R.k - 2, ha⟩), fun τ => ?_, ?_⟩
    · simp only [FlagTan.kap]
      rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega), ep, eq, hr, abs_le]
      constructor <;> push_cast <;> omega
    · funext τ j
      have e := P.uMinus_eq τ (a := ⟨D.R.k - 2, ha⟩) rfl j
      have e1 : P.u τ ⟨D.R.k - 2, ha⟩ = 0 :=
        uWt_anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ ⟨D.R.k - 2, ha⟩ (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
      have e0 : P.uMinus τ ⟨D.R.k - 2, ha⟩ = 0 := by
        simp only [WtPar.uMinus, Pi.sub_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, smul_eq_mul, e1]
        rw [if_pos (by show D.R.k - 2 < (dat p i).p; omega)]
        ring
      show P.uMinus τ j = P.wt P.T τ j + GlobalTheory.FlatLine.parWt (dat p i) _ τ j
      rw [e, e0]
      simp [GlobalTheory.FlatLine.parWt, sub_eq_add_neg]
  · intro s hs τ
    have hc := cZero_spec D ((i : ℕ) + 1)
    have hf8 := hh.f8
    have hL := hh.big.2.1
    have hZ : (40 : ℝ) ≤ zBase L := by
      unfold zBase
      have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
      have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast (show 6 ≤ D.R.r by omega)
      have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
      have a4 : (10 : ℝ) ≤ L.sc.L := hL
      nlinarith
    have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
    have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
      rw [hdim]; push_cast [Nat.cast_choose_two]; ring
    have hh1 : 4 * CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    have hh2 : 4 * (cZero D ((i : ℕ) + 1) + 2 * ((D.R.r : ℕ) : ℤ) + lenT p i PP + CompHt.dimFlag (dat p i) + 1) ≤ h0 := by
      have := hW.h2.1
      change 4 * (cZero D ((i : ℕ) + 1) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) + (lenT p i PP : ℤ) +
        (CompHt.dimFlag (dat p i) : ℤ) + 1) ≤ h0 at this
      rw [er] at this; exact this
    obtain ⟨r1, r2⟩ := GlobalTheory.QuoWt.arith (lenT p i PP : ℝ) (CompHt.dimFlag (dat p i) : ℝ) (cZero D ((i : ℕ) + 1) : ℝ) (h0 : ℝ)
      (D.R.r : ℝ) (D.R.f : ℝ) (D.R.m : ℝ) (D.R.k : ℝ) PP (by exact_mod_cast hh1) (by exact_mod_cast hT2) hrow
      (by exact_mod_cast hh2) (by exact_mod_cast hc.2.1) (by exact_mod_cast hc.2.2) hD hPP
      (by exact_mod_cast (show D.R.r + 4 ≤ 2 * D.R.k by omega)) (by exact_mod_cast hm)
      (by exact_mod_cast (show 6 ≤ D.R.r by omega)) (by exact_mod_cast hf8)
    have hbar : ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag (dat p i) + 1) + P.c₀ +
        2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) - 2 ≤ h0 := by
      rw [er]; exact_mod_cast r1
    have hTD : 2 * ((dat p i).p + (dat p i).q) + CompHt.dimFlag (dat p i) ≤ P.T := by
      rw [er]; exact_mod_cast r2
    exact GlobalTheory.QuoWt.dominance (dat p i) P hW.weightConst_nonneg hTD
      (fun τ a b hab => ⟨fun hb => (hW.h4 τ a b hab).1 hb, fun hb => hbar.trans ((hW.h4 τ a b hab).2.2 hb)⟩) s hs τ

end Pt

end GlobalTheory.QuoWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertVacLag

theorem vac_not_mem_augAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hvw hvT hmem
  obtain ⟨C, l, hC, hl, hne⟩ := GlobalTheory.T.exists_lagrangian_invariantForm_inertVacuum F E σ B a a' G X om om' hT v w hvw hvT
  have hle : augAt om' v ≤ LinearMap.ker l := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
    show φ₁ - φ ∈ LinearMap.ker l
    rw [LinearMap.mem_ker, map_sub,
      GlobalTheory.InertVacLag.inv_of_heisInv F E σ B a a' G X om om' hT v w hvw hvT _ C hC l hl g hg φ hφ φ₁ hφ₁ ha, sub_self]
  exact hne (hle hmem)

end GlobalTheory.InertVacLag
end
end

