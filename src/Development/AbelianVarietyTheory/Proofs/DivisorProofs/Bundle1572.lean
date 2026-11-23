module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesBorelFrameChangeCanonicalWeight
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlagTan

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {K : Type} [Field K]

def movedVert (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (k : VIx Dw) : FIx Dw → K :=
  fun x => x.elim ((Pi.single k.toF (1 : K) : FIx Dw → K) none) fun q =>
    (g' q.1 * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨q.1, i, j⟩)) * g q.1) q.2.1 q.2.2

theorem det_moved {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ}
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    (hg : ∀ τ i j, i < j → g τ i j = 0) (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : K))
    (hg' : ∀ τ i j, i < j → g' τ i j = 0) (hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ)) :
    (Matrix.of fun k => ksChg Φ g (Pi.single k 1)).det *
      (Matrix.of fun k j : VIx Dw => movedVert g g' k j.toF).det =
      ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  have eM : ∀ k j : HIx Dw Φ, ksChg Φ g (Pi.single k 1) j ≠ 0 →
      k = j ∨ ((j.2.1 : ℤ) + j.2.2 < (k.2.1 : ℤ) + k.2.2) := by
    rintro k ⟨τ, a, b⟩ hne
    rw [ksChg_apply] at hne
    obtain ⟨a', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b', -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain rfl : ⟨τ, a', b'⟩ = k := by
      by_contra hk
      simp [Pi.single_eq_of_ne hk] at hne
    have h1 : ¬ a' < a := fun k => by simp [hg _ _ _ k] at hne
    have h2 : ¬ b' < b := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a' = a ∧ b' = b
    · left; rw [h3.1, h3.2]
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega
  have dM : ∀ k : HIx Dw Φ, ksChg Φ g (Pi.single k 1) k =
      ((t (some ⟨conjEmb k.1.1, k.2.1⟩) * t (some ⟨k.1.1, k.2.2⟩) : Kˣ) : K) := by
    rintro ⟨τ, a, b⟩
    simp [ksChg_apply, Pi.single_apply, hd, ite_and]
  have fN : ∀ (k : VIx Dw) (σ : E →+* ℂ) (i j : Fin (Dw.mult σ)),
      (g' σ * (Matrix.of fun i j => (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, i, j⟩)) * g σ) i j =
      ∑ a, ∑ b, g' σ i a * (Pi.single k.toF (1 : K) : FIx Dw → K) (some ⟨σ, a, b⟩) * g σ b j := fun k σ i j => by
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [det_eq_prod_diag_of_height _ (fun k => (k.2.1 : ℤ) + k.2.2) eM,
    det_eq_prod_diag_of_height (m := VIx Dw) _ (fun k => (k.2.1.2 : ℤ) - k.2.1.1)]
  · rw [exOf_kap, ← prod_char_eq hΦ, Units.val_mul, Units.coe_prod, Units.coe_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => dM k)
      (Finset.prod_congr rfl fun ⟨σ, ⟨i, j⟩, hij⟩ _ => (fN _ σ i j).trans ?_)
    simp [VIx.toF, Pi.single_apply, hd, hd', ite_and]
  · rintro ⟨σ', ⟨i', j'⟩, hij'⟩ ⟨σ, ⟨i, j⟩, hij⟩ hne
    have hne := fun e => hne ((fN _ σ i j).trans e)
    obtain ⟨a, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨b, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have e : (some ⟨σ, a, b⟩ : FIx Dw) = some ⟨σ', i', j'⟩ := by
      by_contra hk
      exact hne (by rw [VIx.toF, Pi.single_eq_of_ne hk, mul_zero, zero_mul])
    obtain ⟨rfl, e⟩ := Sigma.mk.inj_iff.1 (Option.some.inj e)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq e)
    have h1 : ¬ i < a := fun k => by simp [hg' _ _ _ k] at hne
    have h2 : ¬ b < j := fun k => by simp [hg _ _ _ k] at hne
    by_cases h3 : a = i ∧ b = j
    · left; obtain ⟨rfl, rfl⟩ := h3; rfl
    · right
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 h3 ⊢
      omega

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F K]

theorem exists_moved_defs {Φ : Finset (E →+* ℂ)} (hΦ : IsHalf Φ) {t : Ix Dw → Kˣ} {y y' : FrPt Xo c K}
    (h : FrBor t y y') {v' : TIx Dw Φ → FrPt Xo c (DualNumber K)} (hv' : IsTanFrame Φ y' v') :
    ∃ (w : TIx Dw Φ → FrPt Xo c (DualNumber K)) (M : HIx Dw Φ → HIx Dw Φ → K) (N : VIx Dw → FIx Dw → K),
      (∀ k, ∃ t' : Ix Dw → (DualNumber K)ˣ, FrBor t' (w k) (v' k)) ∧
      (∀ k, IsDef y (w (.inl k)) ∧ IsKS Φ y (w (.inl k)).x (M k)) ∧ (∀ k, IsVert y (N k) (w (.inr k))) ∧
      (Matrix.of M).det * (Matrix.of fun k j : VIx Dw => N k j.toF).det =
        ((∏ k, t k ^ exOf Dw (kap Dw) 0 k : Kˣ) : K) := by
  obtain ⟨g, hg, hd, hc⟩ := (frBor_iff_frChg _ _ _).1 h
  obtain ⟨g', a', -, e1, e2⟩ := exists_frChg_inv hc
  have hg' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ i j hij => by
    let _ : Invertible (g τ) := ⟨g' τ, e1 τ, e2 τ⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular (M := g τ) (b := OrderDual.toDual)
      (fun i j hij => hg τ i j hij)
    rw [Matrix.inv_eq_left_inv (e1 τ)] at this
    exact this hij
  have hd' : ∀ τ i, g' τ i i = ((t (some ⟨τ, i⟩))⁻¹ : Kˣ) := fun τ i => by
    have := congrFun (congrFun (e1 τ) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hd, Matrix.one_apply_eq] at this
    · exact (Units.mul_eq_one_iff_eq_inv).1 this
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with k | k
      · rw [hg τ j i k, mul_zero]
      · rw [hg' τ i j k, zero_mul]
    · simp
  choose w hw hw' using fun k => exists_move hc (hv'.isDef k)
  refine ⟨w, fun k => ksChg Φ g (Pi.single k 1), movedVert g g', fun k =>
    ⟨fun i => Units.map (cst c K).toRingHom.toMonoidHom (t i),
      (frBor_iff_frChg _ _ _).2 ⟨_, fun τ i j hij => by simp [hg τ i j hij], fun τ i => by simp [hd], hw' k⟩⟩,
    fun k => ⟨hw _, by rw [← (hw' _).1]; exact (hv'.1 k).2.of_frChg hc⟩,
    fun k => isVert_move hc e2 (hv'.2 k) (hw' (.inr k)), det_moved hΦ hg hd hg' hd'⟩

end GlobalTheory.FlagTan

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem det_der_frBor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    {K : Type} [Field K] [Algebra c.F K] (z : Sp K ⟶ M.X) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) {P Q : FrPt Xo c K}
    (t : Ix Dw → Kˣ) (hz : z ≫ toFlag M = X.ptY Q) (ht : FrBor t Q P)
    {v v' : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K)}
    (hv : IsTanFrame (psiSet H) P v) (hv' : IsTanFrame (psiSet H) Q v')
    {zv zv' : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)}
    (hl : ∀ b, zv b ≫ toFlag M = X.ptY (v b)) (hl' : ∀ b, zv' b ≫ toFlag M = X.ptY (v' b))
    (O : M.X.Opens) (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hzv' : ∀ b, ⊤ ≤ zv' b ⁻¹ᵁ O), (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (kap Dw) 0 ix).val *
        (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS K _ _ z ho P Q t hz ht v v' hv hv' zv zv' hl hl' O g hzv hzv'
  obtain ⟨w, Mx, N, hb, hM, hN, hdet⟩ := GlobalTheory.FlagTan.exists_moved_defs (GlobalTheory.FlagTan.isHalf_psiSet H) ht hv
  have hlw : ∀ k, zv k ≫ toFlag M = X.ptY (w k) := fun k => by
    obtain ⟨_, h⟩ := hb k
    rw [hl, X.ptY_frBor h]
  choose C hC using fun k => _root_.GlobalTheory.CompHS.der_fun_hor M z ho (hKS K Q) hz hv' hl' (hM k).1 (hM k).2 (hlw (.inl k))
  have hV := fun k => GlobalTheory.T.derivative_along_vertical_deformation_lift M z ho hz (v := fun j => v' (.inr j)) (fun j => hv'.2 j)
    (zv := fun j => zv' (.inr j)) (fun j => hl' _) (hN k) (hlw (.inr k))
  let T : Matrix (TIx Dw (psiSet H)) (TIx Dw (psiSet H)) K :=
    Matrix.fromBlocks (Matrix.of Mx) (Matrix.of C) 0 (Matrix.of fun k j : VIx Dw => N k j.toF)
  have hT : ∀ a b, (evalPt (zv b) O (hzv b) (g a)).snd =
      ∑ c', T b c' * (evalPt (zv' c') O (hzv' c') (g a)).snd := by
    intro a b
    rcases b with k | k
    · rw [hC k O (g a) (hzv _) hzv', Fintype.sum_sum_type]
      simp [T]
    · rw [hV k O (g a) (hzv _) (fun j => hzv' _), Fintype.sum_sum_type]
      simp [T]
  have hA : (Matrix.of fun a b => (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd) =
      (Matrix.of fun a b => (evalPt (zv' (tanOrd Dw b)) O (hzv' _) (g a)).snd) *
        (T.submatrix (tanOrd Dw) (tanOrd Dw)).transpose := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, hT]
    rw [← (tanOrd Dw).sum_comp]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hA, Matrix.det_mul, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, hdet,
    mul_comm]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces
section
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.DiffCoprimeP

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem not_le_differentIdeal_of_psiUnr {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hu : PsiUnr ψ v) : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  classical
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)

  have key : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
      Valued.v x ≤ exp (-FractionalIdeal.count F v (codiff F)) := by
    intro x
    set α : Af F := GlobalTheory.AdelicU.singleFin v x with hα
    have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
    have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
    have k1 : (∀ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (x * y) = 1) ↔
        ∀ β : Af F, (∀ w, β w ∈ w.adicCompletionIntegers F) → ψ (pairA F 0 (β * α)) = 1 := by
      constructor
      · intro H β hβ
        have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact H _ (hβ v)
      · intro H y hy
        have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
          rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
        have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
          by_cases hw : w = v
          · subst hw
            change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_self]
            exact hy
          · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
            rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
            exact zero_mem _)
        rw [e] at this
        exact this
    rw [k1, ← h, mem_adelicIdeal_iff codiff_ne_zero]
    constructor
    · intro H
      have := H v
      rwa [hαv] at this
    · intro H w
      by_cases hw : w = v
      · subst hw
        rw [hαv]
        exact H
      · rw [hαw w hw, map_zero]
        exact zero_le
  set c := FractionalIdeal.count F v (codiff F) with hc

  have hc0 : c ≤ 0 := by
    have := FractionalIdeal.count_mono F v (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))
      (one_le_codiff (F := F))
    rw [FractionalIdeal.count_one] at this
    omega

  have hc1 : 0 ≤ c := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact exp_ne_zero hπ.symm
    set x : Fv F v := ((π⁻¹ : F) : v.adicCompletion F) with hx
    have hvx : Valued.v x = exp 1 := by
      rw [hx, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ, ← exp_neg, neg_neg]
    have h1 : Valued.v x ≤ exp (-c) := by
      rw [hvx, exp_le_exp]
      omega
    have h2 := (hu x).1 ((key x).2 h1)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hvx, ← exp_zero, exp_le_exp] at h2
    omega
  have hc2 : c = 0 := le_antisymm hc0 hc1
  intro hle
  have hD : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (codiff F)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h0 : differentIdeal ℤ (𝓞 F) ≠ 0 := differentIdeal_ne_bot
  have h1 := FractionalIdeal.count_coe F v h0
  rw [hD, FractionalIdeal.count_inv, ← hc, hc2, neg_zero] at h1
  have h2 := (Associates.count_ne_zero_iff_dvd h0 v.irreducible).2 (Ideal.dvd_iff_le.2 hle)
  exact h2 (by exact_mod_cast h1.symm)

end GlobalTheory.DiffCoprimeP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerComposition
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKEvAdm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl g hg
  classical
  obtain ⟨ei, ev, -, hvac, hpure⟩ := hev.loc
  obtain ⟨Bx, hBo, hBs, hBe, hinv⟩ := _root_.GlobalTheory.SBBox.exists_box_invariant F _ g hg
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.BoxCosetSum.eq_sum_finprod_box_indicator F _ Bx hBo hBs hBe g hg.2 hinv
  let φ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n × Fin d → v.adicCompletion F) → ℂ :=
    fun r v => Set.indicator {x : Fin n × Fin d → v.adicCompletion F | ∀ i, x i - evalV F v (r i) ∈ Bx v} 1
  have hφSB : ∀ r v, φ r v ∈ SB _ := fun r => (_root_.GlobalTheory.LocalBoxIndicator.indicator_box_translate F _ Bx hBo hBs hBe r).1
  have hφvac : ∀ r, ∀ᶠ v in cofinite, φ r v = M.vac v := fun r => by
    filter_upwards [(_root_.GlobalTheory.LocalBoxIndicator.indicator_box_translate F _ Bx hBo hBs hBe r).2, hM.std] with v h1 h2
    exact h1.trans h2.symm
  let ψ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n₁ × Fin d₁ → v.adicCompletion F) → ℂ :=
    fun r v => ev v (φ r v)
  have hψSB : ∀ r v, ψ r v ∈ SB _ := fun r v => by
    rw [← (hvac v).2]; exact Submodule.mem_map_of_mem (hφSB r v)
  have hψint : ∀ r, ∀ᶠ v in cofinite,
      ψ r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun r => by
    filter_upwards [hφvac r, hM₁.std] with v h1 h2
    show ev v (φ r v) = _
    rw [h1, (hvac v).1, h2]
  let g' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun r y => ∏ᶠ v, ψ r v fun i => evalV F v (y i)
  have hg'SB : ∀ r, g' r ∈ SB _ := fun r => _root_.GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (ψ r) (hψSB r) (hψint r)
  have hT : ∀ r, ∃ T : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f (g' r)) = T f := fun r => hl (g' r) (hg'SB r)
  choose T hT using hT
  have key : ∀ f : SInf F (Fin n × Fin d), pureA F f g = ∑ r ∈ R, g r • pure f (φ r) := by
    intro f
    funext x
    rw [Finset.sum_apply]
    conv_lhs => rw [hR]
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_left_comm]
    rfl
  have key2 : ∀ (f : SInf F (Fin n₁ × Fin d₁)) r, pure f (ψ r) = pureA F f (g' r) := fun f r => rfl
  refine ⟨∑ r ∈ R, g r • (T r).comp ei, fun f => ?_⟩
  have hL : l (e (pureA F (⇑f) g)) = ∑ r ∈ R, g r * T r (ei f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, map_smul, hpure f (φ r) (hφSB r) (hφvac r), key2, hT, smul_eq_mul]
  rw [LinearMap.comp_apply, hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

end GlobalTheory.ThKEvAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AdelicFourierUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t2Space_infiniteAdeleRing_of_numberField : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI := secondCountable_completion F
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI := t2Space_infiniteAdeleRing_of_numberField F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_AF : SecondCountableTopology (AF F) := by
  haveI := secondCountable_inf F
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem continuousAdd_AE : ContinuousAdd (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  IsModuleTopology.toContinuousAdd (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))

def homAE : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) ≃ₜ (Fin (Module.finrank F E) → AF F) :=
  haveI := continuousAdd_AE F E
  let e := (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem t2Space_cm_host_adeles : T2Space (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
  haveI := t2Space_adeleRing_of_numberField F
  exact (homAE F E).isEmbedding.t2Space

theorem secondCountable_AE : SecondCountableTopology (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := by
  haveI := secondCountable_AF F
  exact (homAE F E).isEmbedding.secondCountableTopology

theorem locallyCompact_AE : LocallyCompactSpace (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  (homAE F E).isClosedEmbedding.locallyCompactSpace

theorem topAddGroup_AE : IsTopologicalAddGroup (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  IsModuleTopology.topologicalAddGroup (R := AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))

end GlobalTheory.AdelicFourierUniq


open GlobalTheory.AdelicFourierUniq in
theorem GlobalTheory.AdelicFourierUniq.eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → AE F E) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → AE F E) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  intro F E _ _ _ _ _ ψ hψ d A _ p hp hsep μ hμ N hN hi h
  letI : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI := t2Space_cm_host_adeles F E
  haveI := secondCountable_AE F E
  haveI := locallyCompact_AE F E
  haveI := topAddGroup_AE F E
  have hp0 : p 0 = 0 := by simpa using hp 0 0
  refine GlobalTheory.CharFourierInj.eq_zero (fun a u => ψ (p a u))
    (fun a => hψ.1.comp (IsModuleTopology.continuous_of_linearMap (R := AF F) (p a)))
    (fun a x y => by simp only [map_add (f := _), AddChar.map_add_eq_mul])
    (fun a b x => by simp only [hp, LinearMap.add_apply, AddChar.map_add_eq_mul])
    (fun x => by simp only [hp0, LinearMap.zero_apply, AddChar.map_zero_eq_one])
    (fun a x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _) hsep μ N hN hi h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_representation_compact_character_local : ∀ {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ L : AddSubgroup (κ → Fv F v), IsCompact (L : Set (κ → Fv F v)) →
    ∀ L' : AddSubgroup (κ → Fv F v), IsOpen (L' : Set (κ → Fv F v)) →
    ∀ χ : (κ → Fv F v) → ℂ, (∀ y ∈ L, ∀ y' ∈ L, χ (y + y') = χ y * χ y') → (∀ y ∈ L, y ∈ L' → χ y = 1) →
    ∃ x₀ : κ → Fv F v, ∀ y ∈ L, χ y = ψ₀ (x₀ ⬝ᵥ y) := by
  first | exact @GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | exact GlobalTheory.CompactCharDual.exists_dotProduct_eq_local | (intros; apply GlobalTheory.CompactCharDual.exists_dotProduct_eq_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRamificationCompleteDVRValuationEqMulStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_completeDVR_valuation_eq_mul : ∀ (K : Type) [Field K] [NumberField K] (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∃ e : ℕ, 0 < e ∧ ∀ z : K, vV T.V (iK z) = (e : ℤ) * vAdd 𝔓 z := by
  first | exact @GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | exact GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd | (intros; apply GlobalTheory.CdvrPlaceVal.vV_eq_mul_vAdd <;> assumption)
end

