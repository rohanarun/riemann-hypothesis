module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTensorDecompositionCommutingFamilies
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolume
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjections
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjLat

variable {D : D7}

theorem tmul_mul_incA (x : AF D.host.F) (y z : D.host.E) : (x ⊗ₜ[D.host.F] y) * incA D z = x ⊗ₜ[D.host.F] (y * z) := by
  show (x ⊗ₜ[D.host.F] y) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem of_tmul_mul_rat {m n k : ℕ} (x : AF D.host.F) (X : Matrix (Fin m) (Fin n) D.host.E) (M : Matrix (Fin n) (Fin k) D.host.E) :
    HMul.hMul (Matrix.of fun i j => x ⊗ₜ[D.host.F] X i j : Mx D m n) (rat M : Mx D n k) =
      Matrix.of fun i j => x ⊗ₜ[D.host.F] (X * M) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, TensorProduct.tmul_sum]

theorem latO_mul_rat {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} (M M' : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (hadj : M'ᴴ * S.gram = S.gram * M) (hL : ∀ s ∈ LS, M' *ᵥ s ∈ LS) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    HMul.hMul (u : Mx D T.rank S.rank) (rat M : Mx D S.rank S.rank) ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    refine ⟨α, hα, hP, a, ha, M' *ᵥ s, hL s hs, t, ht, ?_⟩
    have h : ∀ l j, ∑ k, star (M' k l) * S.gram k j = ∑ k, S.gram l k * M k j := fun l j => by
      have := congrFun (congrFun hadj l) j
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, tmul_mul_incA, ← TensorProduct.tmul_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum, mul_assoc]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp_rw [mul_left_comm (star (M' _ y)) (star (s y))]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h y j]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_rat {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hN : ∀ x ∈ N, x * M ∈ N) {w : Mx D m n} (hw : w ∈ hatMx N) :
    HMul.hMul w (rat M : Mx D n n) ∈ hatMx N := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    apply AddSubgroup.subset_closure
    exact ⟨α, hα, x * M, hN x hx, of_tmul_mul_rat _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem smul_homLat_mul {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ)
    {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') : x * M ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on (p := fun x => x * M ∈ I • homLat Λ Λ') hx ?_ ?_
  · intro r hr n hn
    show (r • n) * M ∈ _
    rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (fun y hy => by rw [← Matrix.mulVec_mulVec]; exact hn _ (hM y hy))
  · intro x y hx hy
    show (x + y) * M ∈ _
    rw [Matrix.add_mul]; exact add_mem hx hy

theorem proj_adj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e' * d.qY)ᴴ * S.gram = S.gram * (d.e * d.qX) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem proj_adj' {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : (d.e * d.qX)ᴴ * S.gram = S.gram * (d.e' * d.qY) := by
  simp only [HypDec.qX, HypDec.qY, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, Matrix.mul_assoc]

theorem latRow_mul_rat {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : ℕ)
    (Mx₁ Mx₂ : Matrix (Fin (G.V (.grid (i + 1) 0)).rank) (Fin (G.V (.grid (i + 1) 0)).rank) D.host.E)
    (hadj : Mx₂ᴴ * (G.V (.grid (i + 1) 0)).gram = (G.V (.grid (i + 1) 0)).gram * Mx₁)
    (h1 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₁ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    (h2 : ∀ v ∈ G.Λ (.grid (i + 1) 0), Mx₂ *ᵥ v ∈ G.Λ (.grid (i + 1) 0))
    {u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0))} (hu : u ∈ latRow G i) :
    HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ latRow G i := by
  obtain ⟨hu1, hu2⟩ := hu
  have hadj' : Mx₂ᴴ * (G.pS (.chi i 0)).gram = (G.pS (.chi i 0)).gram * Mx₁ := by
    show Mx₂ᴴ * (-(G.V (.grid (i + 1) 0)).gram) = (-(G.V (.grid (i + 1) 0)).gram) * Mx₁
    rw [Matrix.mul_neg, Matrix.neg_mul, hadj]
  have hu1' : u ∈ latO (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) := hu1
  have L1 := @latO_mul_rat D (G.pS (.chi i 0)) (G.pT (.chi i 0)) (G.latS (.chi i 0) : Set _) (G.latT (.chi i 0) : Set _) (fun _ => True) Mx₁ Mx₂ hadj' h2
  have t1 := L1 hu1'
  have t2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • HMul.hMul u (rat Mx₁ : Mx D _ _) ∈ hatMx (G.modul • homLat (G.latS (.chi i 0)) (G.latT (.chi i 0))) := by
    intro e he
    rw [← Matrix.smul_mul]
    exact hatMx_mul_rat _ _ (fun x hx => smul_homLat_mul _ _ _ _ h1 hx) (hu2 e he)
  exact ⟨t1, t2⟩

theorem latRow_proj : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' u hu
  have hA := hF.hJ (σ + 1) h
  have e : G.Λ (.grid (2 * σ + 2 + 1) 0) = _ := G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)
  have hX : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact _root_.GlobalTheory.projX_embedding_lattice _ _ hA _ _ _ hv
  have hY : ∀ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0), ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) *ᵥ v ∈ G.Λ (.grid (2 * σ + 2 + 1) 0) := by
    intro v hv
    rw [e] at hv ⊢
    exact _root_.GlobalTheory.AscFin.projY_mem_lat _ _ hA _ _ _ hv
  rw [show (F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX = rat ((F.dJ (σ + 1) h).e * (F.dJ (σ + 1) h).qX) from (rat_mul _ _).symm,
    show (F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY = rat ((F.dJ (σ + 1) h).e' * (F.dJ (σ + 1) h).qY) from (rat_mul _ _).symm]
  exact ⟨latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj _) hX hY hu, latRow_mul_rat G (2 * σ + 2) _ _ (proj_adj' _) hY hX hu⟩

end GlobalTheory.ProjLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetPositivePartKroneckerBlockUnitaryOrthonormal
section
open Formalism.IndefR.Datum Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

namespace GlobalTheory.PlusDetONB

open GlobalTheory.CompactFockAction GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgnP {k : ℕ} (p : ℕ) : Fin k → Bool := fun a => decide (a.val < p)

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    B * B⁻¹ = 1 ∧ B⁻¹ * B = 1 ∧ s = B * Formalism.REAL.Jm (sgnP p) * B⁻¹ := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hd : Matrix.diagonal (fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgnP (k := k) p) := by
    unfold Formalism.REAL.Jm sgnP
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · have : ¬ a.val < p := by omega
      simp [h1, this]
  have hsq : Matrix.diagonal (fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hdet : (Matrix.diagonal (fun a => (ε a : ℂ))).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hsq
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hB : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hG, Matrix.det_mul, h0, mul_zero]
  have hU : IsUnit B.det := isUnit_iff_ne_zero.2 hB
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hU
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hU
  refine ⟨h1, h2, ?_⟩
  rw [← hd, ← hs, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem isBlock_of_isKMat {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) : IsBlock (sgnP p) κ := by
  intro i j hij
  apply h.2 i j
  intro hiff
  apply hij
  unfold sgnP
  exact decide_eq_decide.2 hiff

theorem card_sgnP {k p : ℕ} (hp : p ≤ k) (e : Bool) :
    (Finset.univ.filter fun i : Fin k => sgnP p i = e).card = if e then p else k - p := by
  have h1 : (Finset.univ.filter fun i : Fin k => i.val < p).card = p := by
    rw [Fin.card_filter_val_lt]; omega
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => i.val < p)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  cases e
  · simp only [sgnP, decide_eq_false_iff_not, Bool.false_eq_true, if_false]
    omega
  · simp only [sgnP, decide_eq_true_eq, if_true]
    exact h1

theorem signBlockDeterminant_positive_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) true κ = detPos p κ := by
  unfold signBlockDeterminant detPos
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = true ↔ a.val < p)))]
  rfl

theorem signBlockDeterminant_negative_eq {k p : ℕ} (κ : Matrix (Fin k) (Fin k) ℂ) : signBlockDeterminant (sgnP p) false κ = detNeg p κ := by
  unfold signBlockDeterminant detNeg
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (fun a : Fin k => (by simp [sgnP] : sgnP p a = false ↔ ¬ a.val < p)))]
  rfl

theorem detPlus_onb : ∀ {n m : ℕ} (GS sS BS κS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT κT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ), pS ≤ n → pT ≤ m → IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → IsKMat pS κS → IsKMat pT κT →
    GlobalTheory.WeilParts.detPlus sS sT (BS * κS * BS⁻¹)⁻¹ (BT * κT * BT⁻¹) =
      detPos pT κT ^ pS * detNeg pT κT ^ (n - pS) * (detPos pS κS ^ pT)⁻¹ * (detNeg pS κS ^ (m - pT))⁻¹ := by
  intro n m GS sS BS κS GT sT BT κT pS pT hpS hpT hBS hBT hκS hκT
  obtain ⟨h1S, h2S, hsS⟩ := onb_facts hBS
  obtain ⟨h1T, h2T, hsT⟩ := onb_facts hBT
  have hu : κS * κSᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hκS.1
  have hinv : (BS * κS * BS⁻¹)⁻¹ = BS * κSᴴ * BS⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc BS * κS * BS⁻¹ * (BS * κSᴴ * BS⁻¹) = BS * (κS * (BS⁻¹ * BS) * κSᴴ) * BS⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2S, Matrix.mul_one, hu, Matrix.mul_one, h1S]
  rw [hinv, hsS, hsT, detPlus_conj h2S h2T]
  have bS := isBlock_of_isKMat hκS
  have bT := isBlock_of_isKMat hκT
  have bS' : IsBlock (sgnP pS) κSᴴ := fun i j e => by
    rw [Matrix.conjTranspose_apply, bS j i (Ne.symm e), star_zero]
  rw [detPlus_block bS' bT, prod_bool _ fun e => signBlockDeterminant (sgnP pS) e κSᴴ,
    prod_bool _ fun e => signBlockDeterminant (sgnP pT) e κT, card_sgnP hpT, card_sgnP hpT, card_sgnP hpS, card_sgnP hpS]
  have ih := fun e => signBlockDeterminant_mul_eq_one_of_mul_eq_one e bS hu
  rw [eq_inv_of_mul_eq_one_right (ih true), eq_inv_of_mul_eq_one_right (ih false)]
  simp only [if_true, Bool.false_eq_true, if_false, signBlockDeterminant_positive_eq, signBlockDeterminant_negative_eq, inv_pow]
  ring

end GlobalTheory.PlusDetONB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualCoefSpaceIsTensorOverRealPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefTensorProof

theorem coefTensor : CoefTensor := by
  intro D V θ c hθ hc
  classical
  haveI : Nontrivial c.W := hc.2.2.2.1
  haveI : Nontrivial (Module.Dual ℂ c.W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Subspace.dual_finrank_eq]
    exact Module.finrank_pos
  let a : ∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.UH (gramAt D V τ) → Module.End ℂ (Module.Dual ℂ c.W) :=
    fun τ g => (c.ρ (atTau θ V τ g.1)⁻¹).dualMap
  have ha : ∀ τ (g : Formalism.QuantumDeterminants.UH (gramAt D V τ)) f, a τ g f = f ∘ₗ c.ρ (atTau θ V τ g.1)⁻¹ := fun _ _ _ => rfl
  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ g h, a τ g * a τ' h = a τ' h * a τ g := by
    intro τ τ' hne g h
    have hc' := GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne g.1 g.2 h.1 h.2
    ext f w
    simp only [Module.End.mul_apply, ha, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (c.ρ _), ← map_mul, ← Module.End.mul_apply (c.ρ _), ← map_mul, ← mul_inv_rev,
      ← mul_inv_rev, hc']
  have hirrD : ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ g, ∀ x ∈ N, a τ g x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => _root_.GlobalTheory.DualIrr.dual_irr D V θ c hθ hc N fun τ g hg f hf => hN τ ⟨g, hg⟩ f hf
  obtain ⟨X, i1, i2, i3, b, m, e, hinj, hint, hirr, heq⟩ := _root_.GlobalTheory.TensorDecomp.tensor_decomp D.what₂.Tau (Module.Dual ℂ c.W) _ a hcomm hirrD
  have hone : ∀ τ, atTau θ V τ 1 = 1 := fun τ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ
  let π : ∀ τ, Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (X τ) := fun τ g =>
    if hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then b τ ⟨g, hg⟩ else 1
  have hπ : ∀ τ g (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), π τ g = b τ ⟨g, hg⟩ := fun τ g hg => dif_pos hg
  refine ⟨X, i1, i2, i3, π, e, fun τ => ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  ·
    rw [hπ τ 1 (GlobalTheory.PointAtPlaceHom.one_mem_UH _)]
    ext x
    apply hinj τ
    rw [hint, ha]
    show m τ x ∘ₗ c.ρ (atTau θ V τ 1)⁻¹ = m τ x
    rw [hone, inv_one, map_one]
    rfl
  · intro g hg h hh
    rw [hπ τ _ (GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh), hπ τ g hg, hπ τ h hh]
    ext x
    apply hinj τ
    rw [Module.End.mul_apply, hint, hint, hint]
    ext w
    simp only [ha, LinearMap.comp_apply]
    rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hh, mul_inv_rev, map_mul, Module.End.mul_apply]
  · intro w l
    obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (m τ) (LinearMap.ker_eq_bot.2 (hinj τ))
    obtain ⟨v, hv⟩ : ∃ v : c.W, ∀ φ : Module.Dual ℂ c.W, (l ∘ₗ r) φ = φ v :=
      ⟨(Module.evalEquiv ℂ c.W).symm (l ∘ₗ r), fun φ => by
        conv_lhs => rw [← (Module.evalEquiv ℂ c.W).apply_symm_apply (l ∘ₗ r)]
        rfl⟩
    refine (_root_.GlobalTheory.coefA_dual_coef_continuousOn D V θ c hθ hc τ (m τ w) v).congr fun g hg => ?_
    show l (π τ g w) = _
    rw [hπ τ g hg]
    have : l (b τ ⟨g, hg⟩ w) = (l ∘ₗ r) (m τ (b τ ⟨g, hg⟩ w)) := by
      rw [LinearMap.comp_apply, ← LinearMap.comp_apply r, hr, LinearMap.id_apply]
    rw [this, hv, hint, ha, LinearMap.comp_apply]
  · intro U hU
    exact hirr τ U fun g x hx => by rw [← hπ τ g.1 g.2]; exact hU g.1 g.2 x hx
  · intro τ g hg x y hy hy'
    have : y = Function.update x τ (b τ ⟨g, hg⟩ (x τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h; rw [Function.update_self, hy, hπ _ g hg]
      · rw [Function.update_of_ne h, hy' τ' h]
    rw [this, heq]
    rfl

end GlobalTheory.CoefTensorProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEllSum


open Classical in
theorem finsum_subtype_ite {G : Type} (p : G → Prop) {u : G → ℂ} (hu : (Function.support u).Finite) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ δ ∈ hu.toFinset, if p δ then u δ else 0 := by
  rw [finsum_subtype_eq_finsum_cond (f := u) (p := p), finsum_eq_sum_of_support_subset (s := hu.toFinset)]
  · exact Finset.sum_congr rfl fun δ _ => finsum_eq_if
  · intro δ hδ
    simp only [Finite.coe_toFinset]
    intro h0
    exact hδ (by simp [h0])

theorem finsum_group {G Q I : Type} (c : G → Q) (ι : I → Q) (hι : Function.Injective ι) (p : G → Prop)
    (hp : ∀ g, p g ↔ ∃ i, c g = ι i) {u : G → ℂ} (hu : (Function.support u).Finite) (S : Finset I)
    (hS : ∀ g i, u g ≠ 0 → c g = ι i → i ∈ S) :
    ∑ᶠ δ : {δ // p δ}, u δ.1 = ∑ i ∈ S, ∑ᶠ δ : {δ // c δ = ι i}, u δ.1 := by
  classical
  rw [finsum_subtype_ite p hu, Finset.sum_congr rfl fun i _ => finsum_subtype_ite (fun δ => c δ = ι i) hu,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : u g ≠ 0 := by simpa using hg
  by_cases h : p g
  · obtain ⟨i, hi⟩ := (hp g).1 h
    rw [ite_eq_left h, Finset.sum_eq_single_of_mem i (hS g i hg' hi) fun j _ hj =>
      ite_eq_right fun e => hj (hι (e.symm.trans hi)), ite_eq_left hi]
  · rw [ite_eq_right h]
    exact (Finset.sum_eq_zero fun i _ => ite_eq_right fun e => h ((hp g).2 ⟨i, e⟩)).symm

theorem elliptic_expansion {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {r : ℕ} {J : Matrix (Fin r) (Fin r) E}
    (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L]
    {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)} {μ : Measure (GAd σ J)}
    (hμ : IsRestrictedProd σ J L μa μf μ) {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, fa w ∈ CcArch σ J w) (hf : IsFinFamily σ J L ff)
    (dta : ∀ (P : PPol σ r) (w : InfinitePlace F), Measure (Tor P w.Completion))
    (dtf : ∀ (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)), Measure (Tor P (Fv F v)))
    (dt : ∀ P : PPol σ r, Measure (Tor P (AF F))) (ht : ∀ P, IsTorusMeas P (dta P) (dtf P) (dt P))
    (K : GAd σ J → ℂ)
    (hK : K = fun x => ∑ᶠ δ : {δ : GRat σ J // Irreducible δ.1.1.charpoly}, tensor σ J fa ff (x⁻¹ * ratEmb σ J δ.1 * x))
    (t : PPol σ r → ℂ)
    (hterm : t = fun P => ((torVol P (dt P)).toReal : ℂ) * (∏ᶠ v, Phi (J := J) (μf v) (dtf P v) (ff v)) *
      ∏ w, Phi (J := J) (μa w) (dta P w) (fa w)) :
    (∀ P, (torVol P (dt P) ≠ ⊤ ∧ (∀ v, PhiOK (J := J) (μf v) (dtf P v) (ff v)) ∧
      ∀ᶠ v in cofinite, Phi (J := J) (μf v) (dtf P v) (ff v) = 1) ∧ ∀ w, PhiOK (J := J) (μa w) (dta P w) (fa w)) ∧
    (Function.support t).Finite ∧ Integrable (descend (ratPts σ J) K) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ) ∧
      ∫ q, descend (ratPts σ J) K q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (ratPts σ J) μ = ∑ᶠ P, t P := by
  have ha' : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord σ J w) (ha w), (ha w).1⟩
  have hc := (continuous_of_mem_ccAd (tensor_mem_ccAd ha hf)).2
  obtain ⟨hfin, hfinx⟩ := GlobalTheory.TrFinite.finite_charpoly_and_ratPts F E σ hcm r J _ hc
  have hpol := fun P => GlobalTheory.T.integral_charpolyKernel_eq_stableOrbitalIntegrals E F σ hcm hun r P J hJ L μa μf μ hμ fa ff ha' hf (dta P) (dtf P) (dt P) (ht P)
  have hinj : Function.Injective (Subtype.val : PPol σ r → E[X]) := Subtype.val_injective
  set S : Finset (PPol σ r) := (hfin.preimage (f := fun P : PPol σ r => P.1) hinj.injOn).toFinset with hSdef
  have hS : ∀ (x : GAd σ J) (γ : GRat σ J) (P : PPol σ r), tensor σ J fa ff (x⁻¹ * ratEmb σ J γ * x) ≠ 0 →
      γ.1.1.charpoly = P.1 → P ∈ S := fun x γ P h e =>
    (Finite.mem_toFinset _).2 ⟨γ, e, x, subset_tsupport _ h⟩
  have hsum : descend (ratPts σ J) K = fun q => ∑ P ∈ S, descend (ratPts σ J) (polKernel P J (tensor σ J fa ff)) q := by
    funext q
    rw [hK]
    refine finsum_group (fun γ : GRat σ J => γ.1.1.charpoly) _ hinj _ (fun γ => ⟨fun h => ?_, ?_⟩)
      (u := fun γ => tensor σ J fa ff ((Quotient.out q)⁻¹ * ratEmb σ J γ * Quotient.out q))
      ((hfinx (Quotient.out q)).subset fun γ h => subset_tsupport _ h) S (hS _)
    · obtain ⟨P, hP, -⟩ := (_root_.GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible F E σ hcm r J hJ).2 γ h
      exact ⟨P, hP⟩
    · rintro ⟨P, hP⟩
      rw [hP]
      exact P.2.2.1
  have hsupp : Function.support t ⊆ S := fun P hP => by
    by_contra hn
    refine hP ?_
    rw [hterm]
    refine (hpol P).2.symm.trans (integral_eq_zero_of_ae (.of_forall fun q => ?_))
    refine finsum_eq_zero_of_forall_eq_zero fun δ => ?_
    by_contra h
    exact hn (hS _ δ.1 P h δ.2)
  refine ⟨fun P => ⟨⟨(_root_.GlobalTheory.TorCompact.torus_compact_finiteVol F E σ hcm r P).2 _ (ht P).haar, fun v => ?_, ?_⟩, fun w => ?_⟩,
    S.finite_toSet.subset hsupp, ?_, ?_⟩
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).1 v _ _ _ (hμ.haar_loc v) ((ht P).haar_loc v) (hf.1 v).1.continuous
      (hf.1 v).2
  · have := isLattice_stdLattice (E := Fld P) (n := 1)
    filter_upwards [_root_.GlobalTheory.TrEll.eventually_unitLoc_orbCls F E σ hcm r P J hJ L, hf.2, hμ.eventually_eq_one,
      IsRestrictedProd.eventually_eq_one (ht P)] with v h1 h2 h3 h4
    have h5 := h1.2.2.2 (μf v) (dtf P v) (hμ.haar_loc v) ((ht P).haar_loc v) h3 h4
    rw [h2, Phi, finsum_eq_single _ ⟨1, h1.1⟩ fun q hq => (h5 q).2 fun e => hq (Subtype.ext e)]
    exact (h5 _).1 rfl
  · exact (GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ).2 w _ _ _ (hμ.haar_arch w) ((ht P).haar_arch w) (ha' w).1 (ha' w).2
  · rw [hsum]
    exact integrable_finsetSum _ fun P _ => (hpol P).1
  · rw [hsum, integral_finsetSum _ fun P _ => (hpol P).1, finsum_eq_sum_of_support_subset _ hsupp, hterm]
    exact Finset.sum_congr rfl fun P _ => (hpol P).2

end GlobalTheory.TrEllSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainStageLevelMeasurePeterssonCoefficiStatement
section
attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient : ∀ D : D7, ForStage D fun c _ s => (MeasurableSet (intOff c s) ∧ MeasurableSet s.big ∧ s.big ⊆ intOff c s ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ s.J, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F s.big s.ν ∧ ∫ g in s.big, F g ∂s.ν = ∫ b, f b ∂mR) ∧ ∀ ipD ip, IsMet c s ipD ip → ∀ (u : s.CC c) (v : s.M.Vec) (b : GinfC s.V), ∀ κ ∈ s.J, s.pet (rTr s.V ((b : GA D s.V) * κ) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v))) (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) = ip u u * ∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.EvenOnto.MeasPet.meas_petco | exact GlobalTheory.EvenOnto.MeasPet.meas_petco | (intros; apply GlobalTheory.EvenOnto.MeasPet.meas_petco <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInversesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_lifting_splitPlaceInverses : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  first | exact @GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | exact GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift | (intros; apply GlobalTheory.MatrixLeftInverseLift.matrix_left_inverse_lift <;> assumption)
end

